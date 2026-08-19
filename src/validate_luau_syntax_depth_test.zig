const std = @import("std");
const cfg = @import("cfg.zig");
const diagnostics = @import("diagnostics.zig");
const ir = @import("ir.zig");
const luau_runtime = @import("luau_runtime.zig");
const syntax_depth = @import("validate_luau_syntax_depth.zig");
const validation = @import("validate.zig");

fn nestedBranchProgram(allocator: std.mem.Allocator, depth: usize) !ir.Program {
    const proof = ir.EvidenceId.fromIndex(0);
    const evidence_ids = try allocator.dupe(ir.EvidenceId, &.{proof});
    const function_id = ir.FunctionId.fromIndex(0);
    const block_count = depth * 2 + 1;
    const value_count = depth + 3;
    const function_blocks = try allocator.alloc(ir.BlockId, block_count);
    const instruction_ids = try allocator.alloc(ir.InstructionId, depth);
    const value_ids = try allocator.alloc(ir.ValueId, value_count);
    const blocks = try allocator.alloc(ir.Block, block_count);
    const instructions = try allocator.alloc(ir.Instruction, depth);
    const values = try allocator.alloc(ir.Value, value_count);

    for (function_blocks, 0..) |*block_id, index| block_id.* = ir.BlockId.fromIndex(index);
    for (instruction_ids, 0..) |*instruction_id, index| instruction_id.* = ir.InstructionId.fromIndex(index);
    for (value_ids, 0..) |*value_id, index| value_id.* = ir.ValueId.fromIndex(index);
    values[0] = .{ .id = value_ids[0], .function = function_id, .type = .function, .origin = .{ .parameter = 0 } };
    values[1] = .{ .id = value_ids[1], .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } };
    values[2] = .{ .id = value_ids[2], .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } };

    for (0..depth) |index| {
        const branch_id = function_blocks[index];
        const failure_id = function_blocks[depth + index];
        const condition_id = value_ids[index + 3];
        values[index + 3] = .{
            .id = condition_id,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .instruction_result = .{ .instruction = instruction_ids[index], .index = 0 } },
        };
        instructions[index] = .{
            .id = instruction_ids[index],
            .block = branch_id,
            .operation = .{ .call = .{
                .callee = value_ids[0],
                .arguments = &.{},
                .result_arity = .{ .fixed = 1 },
            } },
            .results = value_ids[index + 3 .. index + 4],
            .effects = .dynamic_call,
            .evidence = evidence_ids,
        };
        blocks[index] = .{
            .id = branch_id,
            .function = function_id,
            .instructions = instruction_ids[index .. index + 1],
            .terminator = .{ .branch = .{
                .condition = condition_id,
                .then_edge = .{ .target = if (index + 1 == depth) function_blocks[block_count - 1] else function_blocks[index + 1] },
                .else_edge = .{ .target = failure_id },
            } },
            .evidence = evidence_ids,
        };
        blocks[depth + index] = .{
            .id = failure_id,
            .function = function_id,
            .terminator = .{ .return_values = value_ids[2..3] },
            .evidence = evidence_ids,
        };
    }
    blocks[block_count - 1] = .{
        .id = function_blocks[block_count - 1],
        .function = function_id,
        .terminator = .{ .return_values = value_ids[1..2] },
        .evidence = evidence_ids,
    };

    const functions = try allocator.alloc(ir.Function, 1);
    functions[0] = .{
        .id = function_id,
        .parameters = value_ids[0..3],
        .blocks = function_blocks,
        .entry_block = function_blocks[0],
        .evidence = evidence_ids,
    };
    const evidence = try allocator.dupe(ir.Evidence, &.{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:nested-readable-syntax-depth",
    }});
    return .{
        .program_id = "nested-readable-syntax-depth",
        .entry_function = function_id,
        .functions = functions,
        .blocks = blocks,
        .instructions = instructions,
        .values = values,
        .evidence = evidence,
    };
}

fn nestedClosureProgram(allocator: std.mem.Allocator, closure_depth: usize) !ir.Program {
    const proof = ir.EvidenceId.fromIndex(0);
    const evidence_ids = try allocator.dupe(ir.EvidenceId, &.{proof});
    const function_count = closure_depth + 1;
    const function_ids = try allocator.alloc(ir.FunctionId, function_count);
    const block_ids = try allocator.alloc(ir.BlockId, function_count);
    const instruction_ids = try allocator.alloc(ir.InstructionId, closure_depth);
    const value_ids = try allocator.alloc(ir.ValueId, closure_depth);
    const functions = try allocator.alloc(ir.Function, function_count);
    const blocks = try allocator.alloc(ir.Block, function_count);
    const instructions = try allocator.alloc(ir.Instruction, closure_depth);
    const values = try allocator.alloc(ir.Value, closure_depth);
    for (function_ids, 0..) |*function_id, index| function_id.* = ir.FunctionId.fromIndex(index);
    for (block_ids, 0..) |*block_id, index| block_id.* = ir.BlockId.fromIndex(index);
    for (instruction_ids, 0..) |*instruction_id, index| instruction_id.* = ir.InstructionId.fromIndex(index);
    for (value_ids, 0..) |*value_id, index| value_id.* = ir.ValueId.fromIndex(index);

    for (0..function_count) |index| {
        functions[index] = .{
            .id = function_ids[index],
            .lexical_parent = if (index == 0) null else function_ids[index - 1],
            .blocks = block_ids[index .. index + 1],
            .entry_block = block_ids[index],
            .evidence = evidence_ids,
        };
        if (index == closure_depth) {
            blocks[index] = .{
                .id = block_ids[index],
                .function = function_ids[index],
                .terminator = .{ .return_values = &.{} },
                .evidence = evidence_ids,
            };
            continue;
        }
        values[index] = .{
            .id = value_ids[index],
            .function = function_ids[index],
            .type = .function,
            .origin = .{ .instruction_result = .{ .instruction = instruction_ids[index], .index = 0 } },
        };
        instructions[index] = .{
            .id = instruction_ids[index],
            .block = block_ids[index],
            .operation = .{ .make_closure = .{ .function = function_ids[index + 1], .bindings = &.{} } },
            .results = value_ids[index .. index + 1],
            .effects = .pure,
            .evidence = evidence_ids,
        };
        blocks[index] = .{
            .id = block_ids[index],
            .function = function_ids[index],
            .instructions = instruction_ids[index .. index + 1],
            .terminator = .{ .return_values = value_ids[index .. index + 1] },
            .evidence = evidence_ids,
        };
    }

    const evidence = try allocator.dupe(ir.Evidence, &.{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:nested-readable-closure-depth",
    }});
    return .{
        .program_id = "nested-readable-closure-depth",
        .entry_function = function_ids[0],
        .functions = functions,
        .blocks = blocks,
        .instructions = instructions,
        .values = values,
        .evidence = evidence,
    };
}

test "readable syntax admission accepts 512 nested branches and rejects 513" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const boundary = try nestedBranchProgram(arena.allocator(), luau_runtime.max_emitted_syntax_nesting);
    var boundary_report = try validation.validate(std.testing.allocator, &boundary, .readable_luau);
    defer boundary_report.deinit();
    try std.testing.expect(boundary_report.isClean());

    const excessive = try nestedBranchProgram(arena.allocator(), luau_runtime.max_emitted_syntax_nesting + 1);
    var core_report = try validation.validate(std.testing.allocator, &excessive, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try validation.validate(std.testing.allocator, &excessive, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expectEqual(@as(usize, 1), readable_report.diagnostics.items.len);
    try std.testing.expect(readable_report.contains(.unsupported_readable_syntax_depth));
}

test "deep branch spine is rejected before recursive structuring" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const boundary = try nestedBranchProgram(arena.allocator(), luau_runtime.max_emitted_syntax_nesting);
    var boundary_analysis = try cfg.Analysis.init(std.testing.allocator, &boundary, boundary.functions[0]);
    defer boundary_analysis.deinit();
    try std.testing.expect(!try syntax_depth.exceedsPlanningDepth(
        std.testing.allocator,
        &boundary,
        &boundary_analysis,
    ));

    const excessive = try nestedBranchProgram(arena.allocator(), luau_runtime.max_emitted_syntax_nesting + 1);
    var excessive_analysis = try cfg.Analysis.init(std.testing.allocator, &excessive, excessive.functions[0]);
    defer excessive_analysis.deinit();
    try std.testing.expect(try syntax_depth.exceedsPlanningDepth(
        std.testing.allocator,
        &excessive,
        &excessive_analysis,
    ));
}

test "lexical closure bodies consume the same readable syntax budget" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const boundary = try nestedClosureProgram(arena.allocator(), luau_runtime.max_emitted_syntax_nesting);
    var boundary_report = try validation.validate(std.testing.allocator, &boundary, .readable_luau);
    defer boundary_report.deinit();
    try std.testing.expect(boundary_report.isClean());

    const excessive = try nestedClosureProgram(arena.allocator(), luau_runtime.max_emitted_syntax_nesting + 1);
    var readable_report = try validation.validate(std.testing.allocator, &excessive, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expectEqual(@as(usize, 1), readable_report.diagnostics.items.len);
    try std.testing.expect(readable_report.contains(.unsupported_readable_syntax_depth));
}
