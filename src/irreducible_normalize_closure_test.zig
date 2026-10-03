const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const irreducible_region = @import("irreducible_region.zig");
const irreducible_normalize = @import("irreducible_normalize.zig");
const node_split = @import("node_split.zig");
const control_flow = @import("control_flow.zig");
const validation = @import("validate.zig");

test "secondary closure splits a branch reached before the primary" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const primary = ir.BlockId.fromIndex(1);
    const secondary = ir.BlockId.fromIndex(2);
    const primary_path = ir.BlockId.fromIndex(3);
    const then_path = ir.BlockId.fromIndex(4);
    const else_path = ir.BlockId.fromIndex(5);
    const entry_condition = ir.ValueId.fromIndex(0);
    const branch_condition = ir.ValueId.fromIndex(1);
    const initial_payload = ir.ValueId.fromIndex(2);
    const primary_parameter = ir.ValueId.fromIndex(3);
    const secondary_value = ir.ValueId.fromIndex(4);
    const copied_value = ir.ValueId.fromIndex(5);
    const constant_id = ir.InstructionId.fromIndex(0);
    const copy_id = ir.InstructionId.fromIndex(1);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = entry_condition,
            .then_edge = .{ .target = primary, .arguments = &.{initial_payload} },
            .else_edge = .{ .target = secondary },
        } }, .evidence = &.{evidence_id} },
        .{ .id = primary, .function = function_id, .parameters = &.{primary_parameter}, .terminator = .{ .jump = .{ .target = primary_path } }, .evidence = &.{evidence_id} },
        .{ .id = secondary, .function = function_id, .instructions = &.{constant_id}, .terminator = .{ .branch = .{
            .condition = branch_condition,
            .then_edge = .{ .target = then_path },
            .else_edge = .{ .target = else_path },
        } }, .evidence = &.{evidence_id} },
        .{ .id = primary_path, .function = function_id, .terminator = .{ .jump = .{ .target = secondary } }, .evidence = &.{evidence_id} },
        .{ .id = then_path, .function = function_id, .instructions = &.{copy_id}, .terminator = .{ .jump = .{ .target = primary, .arguments = &.{copied_value} } }, .evidence = &.{evidence_id} },
        .{ .id = else_path, .function = function_id, .terminator = .{ .jump = .{ .target = primary, .arguments = &.{secondary_value} } }, .evidence = &.{evidence_id} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ entry_condition, branch_condition, initial_payload },
        .blocks = &.{ else_path, secondary, entry, then_path, primary_path, primary },
        .entry_block = entry,
        .evidence = &.{evidence_id},
    }};
    const values = [_]ir.Value{
        .{ .id = entry_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = branch_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = initial_payload, .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = primary_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = primary, .index = 0 } } },
        .{ .id = secondary_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = constant_id, .index = 0 } } },
        .{ .id = copied_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = copy_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = constant_id,
            .block = secondary,
            .operation = .{ .constant = .{ .integer = "7" } },
            .results = &.{secondary_value},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
        .{
            .id = copy_id,
            .block = then_path,
            .operation = .{ .copy = secondary_value },
            .results = &.{copied_value},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
    };
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .dynamic_fixture,
        .locator = "fixture:secondary-closure-branch-before-primary",
    }};
    const program: ir.Program = .{
        .program_id = "secondary-closure-branch-before-primary",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const normalized = try irreducible_normalize.normalizeInArena(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 3), normalized.cloned_blocks);
    try std.testing.expectEqual(@as(usize, 2), normalized.cloned_values);
    try std.testing.expectEqual(@as(usize, 2), normalized.cloned_instructions);
    try std.testing.expectEqual(@as(usize, 3), normalized.rewritten_edges);
    try std.testing.expectEqual(@as(usize, 9), normalized.program.blocks.len);
    try std.testing.expectEqual(@as(usize, 3), normalized.program.edge_rewrites.len);
    const cloned_secondary_value = ir.ValueId.fromIndex(values.len);
    const cloned_copy = normalized.program.instructions[3].operation.copy;
    try std.testing.expectEqual(cloned_secondary_value, cloned_copy);
    const cloned_copy_result = normalized.program.instructions[3].results[0];
    try std.testing.expectEqual(
        cloned_copy_result,
        normalized.program.blocks[8].terminator.jump.arguments[0],
    );

    for (normalized.program.edge_rewrites) |rewrite| {
        try std.testing.expectEqual(ir.EdgeRewriteRule.node_split, rewrite.rule);
        const replayed = (try node_split.replayAlloc(
            std.testing.allocator,
            &normalized.program,
            rewrite.from,
            rewrite.to.target,
        )).?;
        defer if (replayed.arguments.len != 0) std.testing.allocator.free(replayed.arguments);
        try std.testing.expectEqual(rewrite.to.target, replayed.target);
        try std.testing.expectEqualSlices(ir.ValueId, rewrite.to.arguments, replayed.arguments);
    }

    var graph = try cfg.Analysis.init(std.testing.allocator, &normalized.program, normalized.program.functions[0]);
    defer graph.deinit();
    var regions = try irreducible_region.analyze(std.testing.allocator, &graph);
    defer regions.deinit();
    try std.testing.expectEqual(@as(usize, 0), regions.regions.len);

    var report = try validation.validate(std.testing.allocator, &normalized.program, .readable_luau);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "secondary closure orders cloned definitions before dependent uses" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const primary = ir.BlockId.fromIndex(1);
    const consumer = ir.BlockId.fromIndex(2);
    const independent = ir.BlockId.fromIndex(3);
    const secondary = ir.BlockId.fromIndex(4);
    const producer = ir.BlockId.fromIndex(5);
    const entry_condition = ir.ValueId.fromIndex(0);
    const primary_condition = ir.ValueId.fromIndex(1);
    const secondary_condition = ir.ValueId.fromIndex(2);
    const produced_value = ir.ValueId.fromIndex(3);
    const consumed_value = ir.ValueId.fromIndex(4);
    const constant_id = ir.InstructionId.fromIndex(0);
    const copy_id = ir.InstructionId.fromIndex(1);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = entry_condition,
            .then_edge = .{ .target = primary },
            .else_edge = .{ .target = secondary },
        } }, .evidence = &.{evidence_id} },
        .{ .id = primary, .function = function_id, .terminator = .{ .branch = .{
            .condition = primary_condition,
            .then_edge = .{ .target = secondary },
            .else_edge = .{ .target = independent },
        } }, .evidence = &.{evidence_id} },
        .{ .id = consumer, .function = function_id, .instructions = &.{copy_id}, .terminator = .{ .jump = .{ .target = primary } }, .evidence = &.{evidence_id} },
        .{ .id = independent, .function = function_id, .terminator = .{ .jump = .{ .target = primary } }, .evidence = &.{evidence_id} },
        .{ .id = secondary, .function = function_id, .terminator = .{ .branch = .{
            .condition = secondary_condition,
            .then_edge = .{ .target = producer },
            .else_edge = .{ .target = independent },
        } }, .evidence = &.{evidence_id} },
        .{ .id = producer, .function = function_id, .instructions = &.{constant_id}, .terminator = .{ .jump = .{ .target = consumer } }, .evidence = &.{evidence_id} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ entry_condition, primary_condition, secondary_condition },
        .blocks = &.{ consumer, producer, independent, secondary, entry, primary },
        .entry_block = entry,
        .evidence = &.{evidence_id},
    }};
    const values = [_]ir.Value{
        .{ .id = entry_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = primary_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = secondary_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 2 } },
        .{ .id = produced_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = constant_id, .index = 0 } } },
        .{ .id = consumed_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = copy_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = constant_id,
            .block = producer,
            .operation = .{ .constant = .{ .integer = "7" } },
            .results = &.{produced_value},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
        .{
            .id = copy_id,
            .block = consumer,
            .operation = .{ .copy = produced_value },
            .results = &.{consumed_value},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
    };
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .dynamic_fixture,
        .locator = "fixture:secondary-closure-definition-order",
    }};
    const program: ir.Program = .{
        .program_id = "secondary-closure-definition-order",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const normalized = try irreducible_normalize.normalizeInArena(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 4), normalized.cloned_blocks);
    try std.testing.expectEqual(@as(usize, 2), normalized.cloned_values);
    try std.testing.expectEqual(@as(usize, 2), normalized.cloned_instructions);
    try std.testing.expectEqual(@as(usize, 4), normalized.rewritten_edges);
    const cloned_produced_value = ir.ValueId.fromIndex(values.len);
    try std.testing.expectEqual(
        cloned_produced_value,
        normalized.program.instructions[3].operation.copy,
    );

    var graph = try cfg.Analysis.init(std.testing.allocator, &normalized.program, normalized.program.functions[0]);
    defer graph.deinit();
    var regions = try irreducible_region.analyze(std.testing.allocator, &graph);
    defer regions.deinit();
    try std.testing.expectEqual(@as(usize, 0), regions.regions.len);

    var report = try validation.validate(std.testing.allocator, &normalized.program, .readable_luau);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "transparent forwarding chains are replayable and function scoped" {
    const function_zero = ir.FunctionId.fromIndex(0);
    const function_one = ir.FunctionId.fromIndex(1);
    const zero_entry = ir.BlockId.fromIndex(0);
    const zero_forward_one = ir.BlockId.fromIndex(1);
    const zero_forward_two = ir.BlockId.fromIndex(2);
    const zero_exit = ir.BlockId.fromIndex(3);
    const one_entry = ir.BlockId.fromIndex(4);
    const one_forward = ir.BlockId.fromIndex(5);
    const one_exit = ir.BlockId.fromIndex(6);
    const blocks = [_]ir.Block{
        .{ .id = zero_entry, .function = function_zero, .terminator = .{ .jump = .{ .target = zero_forward_one } } },
        .{ .id = zero_forward_one, .function = function_zero, .terminator = .{ .jump = .{ .target = zero_forward_two } } },
        .{ .id = zero_forward_two, .function = function_zero, .terminator = .{ .jump = .{ .target = zero_exit } } },
        .{ .id = zero_exit, .function = function_zero, .terminator = .{ .return_values = &.{} } },
        .{ .id = one_entry, .function = function_one, .terminator = .{ .jump = .{ .target = one_forward } } },
        .{ .id = one_forward, .function = function_one, .terminator = .{ .jump = .{ .target = one_exit } } },
        .{ .id = one_exit, .function = function_one, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{
        .{ .id = function_zero, .blocks = &.{ zero_entry, zero_forward_one, zero_forward_two, zero_exit }, .entry_block = zero_entry },
        .{ .id = function_one, .blocks = &.{ one_entry, one_forward, one_exit }, .entry_block = one_entry },
    };
    const program: ir.Program = .{
        .program_id = "transparent-forwarding-chain-scope",
        .entry_function = function_zero,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const normalized = try irreducible_normalize.normalizeFunctionWithScratchInArena(
        arena.allocator(),
        std.testing.allocator,
        &program,
        0,
    );

    try std.testing.expectEqual(@as(usize, 2), normalized.program.edge_rewrites.len);
    try std.testing.expectEqual(zero_exit, normalized.program.blocks[zero_entry.index()].terminator.jump.target);
    try std.testing.expectEqual(zero_forward_two, normalized.program.blocks[zero_forward_one.index()].terminator.jump.target);
    try std.testing.expectEqual(one_forward, normalized.program.blocks[one_entry.index()].terminator.jump.target);
    try std.testing.expectEqual(@as(usize, 0), normalized.program.edge_rewrites[0].source.index());
    try std.testing.expectEqual(@as(usize, 0), normalized.program.edge_rewrites[1].source.index());

    for (normalized.program.edge_rewrites) |rewrite| {
        try std.testing.expectEqual(ir.EdgeRewriteRule.forwarding_jump, rewrite.rule);
        const replayed = (try control_flow.replayForwardingJump(
            std.testing.allocator,
            &normalized.program,
            rewrite.from,
        )).?;
        defer if (replayed.arguments.len != 0) std.testing.allocator.free(replayed.arguments);
        try std.testing.expectEqual(rewrite.to.target, replayed.target);
        try std.testing.expectEqualSlices(ir.ValueId, rewrite.to.arguments, replayed.arguments);
    }
}

test "conditional multi-entry loop clones each authenticated incoming edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const route = ir.BlockId.fromIndex(1);
    const header = ir.BlockId.fromIndex(2);
    const body = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const entry_condition = ir.ValueId.fromIndex(0);
    const route_condition = ir.ValueId.fromIndex(1);
    const loop_condition = ir.ValueId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = entry_condition,
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = route },
        } } },
        .{ .id = route, .function = function_id, .terminator = .{ .branch = .{
            .condition = route_condition,
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = loop_condition,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ entry_condition, route_condition, loop_condition },
        .blocks = &.{ entry, route, header, body, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = entry_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = route_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = loop_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 2 } },
    };
    const program: ir.Program = .{
        .program_id = "conditional-multi-entry-loop",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const normalized = try irreducible_normalize.normalizeInArena(arena.allocator(), &program);

    try std.testing.expectEqual(@as(usize, 4), normalized.cloned_blocks);
    const entry_clone = switch (normalized.program.blocks[entry.index()].terminator) {
        .branch => |branch| branch.then_edge.target,
        else => unreachable,
    };
    const route_clone = switch (normalized.program.blocks[route.index()].terminator) {
        .branch => |branch| branch.then_edge.target,
        else => unreachable,
    };
    try std.testing.expect(entry_clone != header);
    try std.testing.expect(route_clone != header);
    try std.testing.expect(entry_clone != route_clone);

    var graph = try cfg.Analysis.init(std.testing.allocator, &normalized.program, normalized.program.functions[0]);
    defer graph.deinit();
    var regions = try irreducible_region.analyze(std.testing.allocator, &graph);
    defer regions.deinit();
    try std.testing.expectEqual(@as(usize, 0), regions.regions.len);

    var report = try validation.validate(std.testing.allocator, &normalized.program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}
