const std = @import("std");
const emission_planning = @import("emit_luau_plan.zig");
const emitter = @import("emit_luau.zig");
const ir = @import("ir.zig");
const jump_budget = @import("validate_luau_jump_budget.zig");
const luau_runtime = @import("luau_runtime.zig");
const readable_scope = @import("readable_scope.zig");
const validation = @import("validate.zig");

const argument_count = 250;
const call_units = argument_count + 2;

fn callProgram(allocator: std.mem.Allocator, call_count: usize, branched: bool, identical_edges: bool) !ir.Program {
    const proof = ir.EvidenceId.fromIndex(0);
    const evidence_ids = try allocator.dupe(ir.EvidenceId, &.{proof});
    const function_id = ir.FunctionId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(0);
    const argument = ir.ValueId.fromIndex(1);
    const condition = ir.ValueId.fromIndex(2);
    const entry = ir.BlockId.fromIndex(0);
    const body = ir.BlockId.fromIndex(1);
    const alternative = ir.BlockId.fromIndex(2);
    const join = ir.BlockId.fromIndex(3);
    const instruction_block = if (branched) body else entry;

    const arguments = try allocator.alloc(ir.ValueId, argument_count);
    @memset(arguments, argument);
    const instruction_ids = try allocator.alloc(ir.InstructionId, call_count);
    const instructions = try allocator.alloc(ir.Instruction, call_count);
    for (instruction_ids, instructions, 0..) |*instruction_id, *instruction, index| {
        instruction_id.* = ir.InstructionId.fromIndex(index);
        instruction.* = .{
            .id = instruction_id.*,
            .block = instruction_block,
            .operation = .{ .call = .{
                .callee = callee,
                .arguments = arguments,
                .result_arity = .{ .fixed = 0 },
            } },
            .results = &.{},
            .effects = .dynamic_call,
            .evidence = evidence_ids,
        };
    }

    const values = try allocator.dupe(ir.Value, &.{
        .{ .id = callee, .function = function_id, .type = .function, .name_hint = "f", .origin = .{ .parameter = 0 } },
        .{ .id = argument, .function = function_id, .name_hint = "x", .origin = .{ .parameter = 1 } },
        .{ .id = condition, .function = function_id, .type = .boolean, .name_hint = "c", .origin = .{ .parameter = 2 } },
    });
    const parameters = try allocator.dupe(ir.ValueId, &.{ callee, argument, condition });
    const returned = try allocator.dupe(ir.ValueId, &.{argument});
    const blocks = if (branched)
        try allocator.dupe(ir.Block, &.{
            .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
                .condition = condition,
                .then_edge = .{ .target = body },
                .else_edge = .{ .target = if (identical_edges) body else alternative },
            } }, .evidence = evidence_ids },
            .{ .id = body, .function = function_id, .instructions = instruction_ids, .terminator = .{ .jump = .{ .target = join } }, .evidence = evidence_ids },
            .{ .id = alternative, .function = function_id, .terminator = .{ .jump = .{ .target = join } }, .evidence = evidence_ids },
            .{ .id = join, .function = function_id, .terminator = .{ .return_values = returned }, .evidence = evidence_ids },
        })
    else
        try allocator.dupe(ir.Block, &.{.{
            .id = entry,
            .function = function_id,
            .instructions = instruction_ids,
            .terminator = .{ .return_values = returned },
            .evidence = evidence_ids,
        }});
    const block_ids = if (branched)
        try allocator.dupe(ir.BlockId, &.{ entry, body, alternative, join })
    else
        try allocator.dupe(ir.BlockId, &.{entry});
    const functions = try allocator.dupe(ir.Function, &.{.{
        .id = function_id,
        .parameters = parameters,
        .blocks = block_ids,
        .entry_block = entry,
        .evidence = evidence_ids,
    }});
    const evidence = try allocator.dupe(ir.Evidence, &.{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:jump-emission-budget",
    }});
    return .{
        .program_id = "jump-emission-budget",
        .entry_function = function_id,
        .functions = functions,
        .blocks = blocks,
        .instructions = instructions,
        .values = values,
        .evidence = evidence,
    };
}

fn unitCount(allocator: std.mem.Allocator, program: *const ir.Program) !usize {
    var readable = try readable_scope.Scope.init(allocator, program);
    defer readable.deinit();
    var emission = try emission_planning.Plan.init(allocator, program, .standard_luau);
    defer emission.deinit();
    return jump_budget.emissionUnitCount(program, &readable, &emission, program.functions[0]);
}

fn expectClean(report: *const validation.Report) !void {
    if (!report.isClean()) {
        for (report.diagnostics.items) |diagnostic| {
            std.debug.print("unexpected diagnostic {s} at {?}\n", .{ @tagName(diagnostic.code), diagnostic.entity_index });
        }
        return error.TestUnexpectedResult;
    }
}

test "jump-bearing admission accepts the unit boundary and rejects the next operand-heavy call" {
    var probe_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer probe_arena.deinit();
    const probe = try callProgram(probe_arena.allocator(), 1, true, false);
    const fixed_units = (try unitCount(std.testing.allocator, &probe)) - call_units;
    const boundary_count = (luau_runtime.max_jump_emission_units - fixed_units) / call_units;

    var boundary_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer boundary_arena.deinit();
    const boundary = try callProgram(boundary_arena.allocator(), boundary_count, true, false);
    try std.testing.expect((try unitCount(std.testing.allocator, &boundary)) <= luau_runtime.max_jump_emission_units);
    var boundary_report = try validation.validate(std.testing.allocator, &boundary, .readable_luau);
    defer boundary_report.deinit();
    try expectClean(&boundary_report);
    const source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &boundary);
    defer std.testing.allocator.free(source);
    try std.testing.expect(source.len != 0);

    var excessive_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer excessive_arena.deinit();
    const excessive = try callProgram(excessive_arena.allocator(), boundary_count + 1, true, false);
    var core_report = try validation.validate(std.testing.allocator, &excessive, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try validation.validate(std.testing.allocator, &excessive, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expectEqual(@as(usize, 1), readable_report.diagnostics.items.len);
    try std.testing.expect(readable_report.contains(.unsupported_readable_jump_distance));
    try std.testing.expectError(error.InvalidIr, emitter.emitStandardLuauAlloc(std.testing.allocator, &excessive));
}

test "straight-line functions do not inherit the jump-distance policy" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const call_count = luau_runtime.max_jump_emission_units / call_units + 1;
    const program = try callProgram(arena.allocator(), call_count, false, false);
    try std.testing.expect((try unitCount(std.testing.allocator, &program)) > luau_runtime.max_jump_emission_units);
    var report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer report.deinit();
    try expectClean(&report);
}

test "identical branch edges do not create a jump-distance obligation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const call_count = luau_runtime.max_jump_emission_units / call_units + 1;
    const program = try callProgram(arena.allocator(), call_count, true, true);
    try std.testing.expect((try unitCount(std.testing.allocator, &program)) > luau_runtime.max_jump_emission_units);
    var report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer report.deinit();
    try expectClean(&report);
}

test "the forced dispatcher budgets the flat root's whole-body back jump" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const call_count = luau_runtime.max_jump_emission_units / call_units + 1;
    // branched=true gives more than one block, so the .dispatcher strategy lays the function out flat
    // (initArbitrary builds an all-.block root emitted as `while true do` plus a balanced dispatch over the blocks).
    const program = try callProgram(arena.allocator(), call_count, true, false);
    try std.testing.expect((try unitCount(std.testing.allocator, &program)) > luau_runtime.max_jump_emission_units);
    var report = try validation.validateForTargetWithStrategy(std.testing.allocator, &program, .readable_luau, .standard_luau, .dispatcher);
    defer report.deinit();
    try std.testing.expect(report.contains(.unsupported_readable_jump_distance));
}
