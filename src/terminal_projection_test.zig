const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const structure = @import("structure.zig");
const validation = @import("validate.zig");
const emit_luau = @import("emit_luau.zig");

test "effectful shared terminal projects complete admitted instructions" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const direct_entry = ir.BlockId.fromIndex(1);
    const nested_entry = ir.BlockId.fromIndex(2);
    const nested = ir.BlockId.fromIndex(3);
    const early = ir.BlockId.fromIndex(4);
    const join = ir.BlockId.fromIndex(5);
    const terminal = ir.BlockId.fromIndex(6);
    const observe_id = ir.InstructionId.fromIndex(0);
    const outer_condition = ir.ValueId.fromIndex(0);
    const inner_condition = ir.ValueId.fromIndex(1);
    const early_value = ir.ValueId.fromIndex(2);
    const fallback_value = ir.ValueId.fromIndex(3);
    const observer = ir.ValueId.fromIndex(4);
    const result = ir.ValueId.fromIndex(5);
    const observed = ir.ValueId.fromIndex(6);
    const proof = ir.EvidenceId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = outer_condition, .function = function_id, .type = .boolean, .name_hint = "outer_condition", .origin = .{ .parameter = 0 } },
        .{ .id = inner_condition, .function = function_id, .type = .boolean, .name_hint = "inner_condition", .origin = .{ .parameter = 1 } },
        .{ .id = early_value, .function = function_id, .type = .string, .name_hint = "early_value", .origin = .{ .parameter = 2 } },
        .{ .id = fallback_value, .function = function_id, .type = .string, .name_hint = "fallback_value", .origin = .{ .parameter = 3 } },
        .{ .id = observer, .function = function_id, .type = .function, .name_hint = "observer", .origin = .{ .parameter = 4 } },
        .{ .id = result, .function = function_id, .type = .string, .name_hint = "result", .origin = .{ .block_parameter = .{ .block = terminal, .index = 0 } } },
        .{ .id = observed, .function = function_id, .type = .string, .name_hint = "observed", .origin = .{ .instruction_result = .{ .instruction = observe_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = observe_id,
        .block = terminal,
        .operation = .{ .call = .{
            .callee = observer,
            .arguments = &.{result},
            .result_arity = .{ .fixed = 1 },
        } },
        .results = &.{observed},
        .effects = .dynamic_call,
        .evidence = &.{proof},
    }};
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = outer_condition,
            .then_edge = .{ .target = nested_entry },
            .else_edge = .{ .target = direct_entry },
        } }, .evidence = &.{proof} },
        .{ .id = direct_entry, .function = function_id, .terminator = .{ .jump = .{ .target = join } }, .evidence = &.{proof} },
        .{ .id = nested_entry, .function = function_id, .terminator = .{ .jump = .{ .target = nested } }, .evidence = &.{proof} },
        .{ .id = nested, .function = function_id, .terminator = .{ .branch = .{
            .condition = inner_condition,
            .then_edge = .{ .target = early },
            .else_edge = .{ .target = join },
        } }, .evidence = &.{proof} },
        .{ .id = early, .function = function_id, .terminator = .{ .jump = .{ .target = terminal, .arguments = &.{early_value} } }, .evidence = &.{proof} },
        .{ .id = join, .function = function_id, .terminator = .{ .jump = .{ .target = terminal, .arguments = &.{fallback_value} } }, .evidence = &.{proof} },
        .{ .id = terminal, .function = function_id, .parameters = &.{result}, .instructions = &.{observe_id}, .terminator = .{ .return_values = &.{observed} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ outer_condition, inner_condition, early_value, fallback_value, observer },
        .blocks = &.{ terminal, nested, direct_entry, entry, join, early, nested_entry },
        .entry_block = entry,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:effectful-terminal-projection",
    }};
    const program: ir.Program = .{
        .program_id = "effectful-terminal-projection",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    var report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer report.deinit();
    try std.testing.expect(report.isClean());

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const inner = plan.root.nodes[0].branch.then_region.nodes[1].branch;
    try std.testing.expectEqual(terminal, inner.then_region.terminal_projection.?.terminal);
    try std.testing.expect(inner.then_region.terminal_projection.?.edge != null);

    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expectEqual(@as(usize, 2), std.mem.count(u8, source, "observer(result)"));

    var direct_blocks = blocks;
    direct_blocks[nested.index()].terminator.branch.then_edge = .{
        .target = terminal,
        .arguments = &.{early_value},
    };
    const direct_functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ outer_condition, inner_condition, early_value, fallback_value, observer },
        .blocks = &.{ terminal, nested, direct_entry, entry, join, early, nested_entry },
        .entry_block = entry,
        .evidence = &.{proof},
    }};
    var direct_program = program;
    direct_program.program_id = "effectful-direct-terminal-projection";
    direct_program.functions = &direct_functions;
    direct_program.blocks = &direct_blocks;

    var direct_report = try validation.validate(std.testing.allocator, &direct_program, .readable_luau);
    defer direct_report.deinit();
    try std.testing.expect(direct_report.isClean());
    var direct_analysis = try cfg.Analysis.init(std.testing.allocator, &direct_program, direct_functions[0]);
    defer direct_analysis.deinit();
    var direct_plan = try structure.Plan.init(std.testing.allocator, &direct_analysis);
    defer direct_plan.deinit();
    const direct_inner = direct_plan.root.nodes[0].branch.then_region.nodes[1].branch;
    try std.testing.expectEqual(terminal, direct_inner.then_region.terminal_projection.?.terminal);
    try std.testing.expect(direct_inner.then_region.terminal_projection.?.edge == null);
    const direct_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &direct_program);
    defer std.testing.allocator.free(direct_source);
    try std.testing.expectEqual(@as(usize, 2), std.mem.count(u8, direct_source, "observer(result)"));
}
