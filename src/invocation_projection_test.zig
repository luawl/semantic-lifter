const std = @import("std");
const ir = @import("ir.zig");
const validation = @import("validate.zig");
const pack_plan = @import("pack_plan.zig");

const Diamond = struct {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const then_block = ir.BlockId.fromIndex(1);
    const else_block = ir.BlockId.fromIndex(2);
    const join = ir.BlockId.fromIndex(3);

    const get_callee = ir.InstructionId.fromIndex(0);
    const produce = ir.InstructionId.fromIndex(1);
    const condition_instruction = ir.InstructionId.fromIndex(2);
    const then_gap = ir.InstructionId.fromIndex(3);
    const else_gap = ir.InstructionId.fromIndex(4);
    const join_gap = ir.InstructionId.fromIndex(5);
    const consume = ir.InstructionId.fromIndex(6);

    const callee = ir.ValueId.fromIndex(0);
    const condition = ir.ValueId.fromIndex(1);
    const then_value = ir.ValueId.fromIndex(2);
    const else_value = ir.ValueId.fromIndex(3);
    const join_value = ir.ValueId.fromIndex(4);
    const result = ir.ValueId.fromIndex(5);
    const open_pack = ir.ValuePackId.fromIndex(0);

    const evidence_ids = [_]ir.EvidenceId{proof};
    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .instruction_result = .{ .instruction = get_callee, .index = 0 } } },
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = condition_instruction, .index = 0 } } },
        .{ .id = then_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = then_gap, .index = 0 } } },
        .{ .id = else_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = else_gap, .index = 0 } } },
        .{ .id = join_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = join_gap, .index = 0 } } },
        .{ .id = result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = consume, .index = 0 } } },
    };
    const packs = [_]ir.ValuePack{.{
        .id = open_pack,
        .function = function_id,
        .origin = .{ .instruction_result = produce },
        .evidence = &evidence_ids,
    }};
    const instructions = [_]ir.Instruction{
        .{
            .id = get_callee,
            .block = entry,
            .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "produce" } },
            .results = &.{callee},
            .effects = .semantic_environment_read,
            .evidence = &evidence_ids,
        },
        .{
            .id = produce,
            .block = entry,
            .operation = .{ .call = .{
                .callee = callee,
                .arguments = &.{},
                .result_arity = .{ .variadic = {} },
            } },
            .results = &.{},
            .pack_result = open_pack,
            .effects = .dynamic_call,
            .evidence = &evidence_ids,
        },
        .{
            .id = condition_instruction,
            .block = entry,
            .operation = .{ .constant = .{ .boolean = true } },
            .results = &.{condition},
            .effects = .pure,
            .evidence = &evidence_ids,
        },
        .{
            .id = then_gap,
            .block = then_block,
            .operation = .{ .constant = .{ .integer = "11" } },
            .results = &.{then_value},
            .effects = .pure,
            .evidence = &evidence_ids,
        },
        .{
            .id = else_gap,
            .block = else_block,
            .operation = .{ .constant = .{ .integer = "22" } },
            .results = &.{else_value},
            .effects = .pure,
            .evidence = &evidence_ids,
        },
        .{
            .id = join_gap,
            .block = join,
            .operation = .{ .constant = .{ .integer = "33" } },
            .results = &.{join_value},
            .effects = .pure,
            .evidence = &evidence_ids,
        },
        .{
            .id = consume,
            .block = join,
            .operation = .{ .call = .{
                .callee = callee,
                .arguments = &.{},
                .argument_pack = open_pack,
                .result_arity = .{ .fixed = 1 },
            } },
            .results = &.{result},
            .effects = .dynamic_call,
            .evidence = &evidence_ids,
        },
    };
    const blocks = [_]ir.Block{
        .{
            .id = entry,
            .function = function_id,
            .instructions = &.{ get_callee, produce, condition_instruction },
            .terminator = .{ .branch = .{
                .condition = condition,
                .then_edge = .{ .target = then_block },
                .else_edge = .{ .target = else_block },
            } },
            .evidence = &evidence_ids,
        },
        .{ .id = then_block, .function = function_id, .instructions = &.{then_gap}, .terminator = .{ .jump = .{ .target = join } }, .evidence = &evidence_ids },
        .{ .id = else_block, .function = function_id, .instructions = &.{else_gap}, .terminator = .{ .jump = .{ .target = join } }, .evidence = &evidence_ids },
        .{ .id = join, .function = function_id, .instructions = &.{ join_gap, consume }, .terminator = .{ .return_values = &.{result} }, .evidence = &evidence_ids },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ entry, then_block, else_block, join },
        .entry_block = entry,
        .evidence = &evidence_ids,
    }};
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:generic-open-pack-region",
    }};
    const program: ir.Program = .{
        .program_id = "generic-open-pack-region",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
        .evidence = &evidence,
    };
};

test "acyclic postdominated diamond records the complete invocation projection" {
    var core_report = try validation.validate(std.testing.allocator, &Diamond.program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());

    var plan = try pack_plan.Plan.init(std.testing.allocator, &Diamond.program);
    defer plan.deinit();
    try std.testing.expectEqual(Diamond.consume, plan.role(Diamond.produce).fused_invocation_producer);
    const projection = plan.invocationProjection(&Diamond.program, Diamond.produce).?;
    try std.testing.expectEqual(pack_plan.ProjectionConsumer{ .instruction = Diamond.consume }, projection.consumer);
    try std.testing.expectEqual(pack_plan.InvocationProjectionReentry.none, projection.reentry);
    try std.testing.expectEqual(@as(usize, 0), projection.reentry_blocks.len);
    try std.testing.expectEqual(@as(usize, 0), projection.reentry_edges.len);
    try std.testing.expectEqual(@as(usize, 0), projection.exit_edges.len);
    try std.testing.expectEqualSlices(
        pack_plan.InvocationProjectionMovedEdge,
        &.{
            .{ .source = Diamond.entry, .target = Diamond.then_block },
            .{ .source = Diamond.entry, .target = Diamond.else_block },
            .{ .source = Diamond.then_block, .target = Diamond.join },
            .{ .source = Diamond.else_block, .target = Diamond.join },
        },
        projection.moved_edges,
    );
    try std.testing.expectEqualSlices(
        ir.BlockId,
        &.{ Diamond.entry, Diamond.then_block, Diamond.else_block, Diamond.join },
        projection.blocks,
    );
    try std.testing.expectEqualSlices(
        ir.InstructionId,
        &.{ Diamond.condition_instruction, Diamond.then_gap, Diamond.else_gap, Diamond.join_gap },
        projection.gaps,
    );
    try std.testing.expect(pack_plan.invocationProjectionIsMovable(&Diamond.program, projection));

    var readable_report = try validation.validate(std.testing.allocator, &Diamond.program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());
}

test "open invocation storage preserves impure paths and rejects consumer reentry" {
    var instructions = Diamond.instructions;
    var blocks = Diamond.blocks;
    var program = Diamond.program;
    program.instructions = &instructions;
    program.blocks = &blocks;

    instructions[Diamond.then_gap.index()].operation = .{ .environment_get = .{
        .target = .{ .ambient = {} },
        .name = "path_probe",
    } };
    instructions[Diamond.then_gap.index()].effects = .semantic_environment_read;
    var impure = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer impure.deinit();
    try std.testing.expect(impure.role(Diamond.produce) == .stored_invocation_producer);
    try std.testing.expect(impure.storedPackServesInstruction(Diamond.produce, Diamond.consume));
    try std.testing.expect(impure.invocationProjection(&program, Diamond.produce) == null);

    instructions[Diamond.then_gap.index()] = Diamond.instructions[Diamond.then_gap.index()];
    blocks[Diamond.then_block.index()].terminator = .{ .return_values = &.{} };
    var side_exit = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer side_exit.deinit();
    try std.testing.expect(side_exit.role(Diamond.produce) == .stored_invocation_producer);
    try std.testing.expect(side_exit.storedPackServesInstruction(Diamond.produce, Diamond.consume));

    blocks[Diamond.then_block.index()] = Diamond.blocks[Diamond.then_block.index()];
    blocks[Diamond.then_block.index()].terminator = .{ .jump = .{ .target = Diamond.then_block } };
    var pre_consumer_cycle = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer pre_consumer_cycle.deinit();
    try std.testing.expect(pre_consumer_cycle.role(Diamond.produce) == .stored_invocation_producer);
    try std.testing.expect(pre_consumer_cycle.storedPackServesInstruction(Diamond.produce, Diamond.consume));

    blocks[Diamond.then_block.index()] = Diamond.blocks[Diamond.then_block.index()];
    blocks[Diamond.join.index()].terminator = .{ .jump = .{ .target = Diamond.then_block } };
    var consumer_reentry = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer consumer_reentry.deinit();
    try std.testing.expect(consumer_reentry.role(Diamond.produce) == .ordinary);

    blocks[Diamond.join.index()] = Diamond.blocks[Diamond.join.index()];
    instructions[Diamond.then_gap.index()].operation = .{ .make_closure = .{
        .function = Diamond.function_id,
        .bindings = &.{},
    } };
    instructions[Diamond.then_gap.index()].effects = .pure;
    var closure_gap = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer closure_gap.deinit();
    try std.testing.expect(closure_gap.role(Diamond.produce) == .stored_invocation_producer);
    try std.testing.expect(closure_gap.storedPackServesInstruction(Diamond.produce, Diamond.consume));
}

test "finite branched indirect latch records its invocation reentry proof" {
    const reentry_dispatch = ir.BlockId.fromIndex(Diamond.blocks.len);
    const reentry_then = ir.BlockId.fromIndex(Diamond.blocks.len + 1);
    const reentry_else = ir.BlockId.fromIndex(Diamond.blocks.len + 2);
    const reentry_merge = ir.BlockId.fromIndex(Diamond.blocks.len + 3);
    const exit_block = ir.BlockId.fromIndex(Diamond.blocks.len + 4);
    var blocks = Diamond.blocks ++ [_]ir.Block{
        .{
            .id = reentry_dispatch,
            .function = Diamond.function_id,
            .terminator = .{ .branch = .{
                .condition = Diamond.condition,
                .then_edge = .{ .target = reentry_then },
                .else_edge = .{ .target = reentry_else },
            } },
            .evidence = &Diamond.evidence_ids,
        },
        .{
            .id = reentry_then,
            .function = Diamond.function_id,
            .terminator = .{ .jump = .{ .target = reentry_merge } },
            .evidence = &Diamond.evidence_ids,
        },
        .{
            .id = reentry_else,
            .function = Diamond.function_id,
            .terminator = .{ .jump = .{ .target = reentry_merge } },
            .evidence = &Diamond.evidence_ids,
        },
        .{
            .id = reentry_merge,
            .function = Diamond.function_id,
            .terminator = .{ .branch = .{
                .condition = Diamond.condition,
                .then_edge = .{ .target = Diamond.entry },
                .else_edge = .{ .target = exit_block },
            } },
            .evidence = &Diamond.evidence_ids,
        },
        .{
            .id = exit_block,
            .function = Diamond.function_id,
            .terminator = .{ .return_values = &.{Diamond.result} },
            .evidence = &Diamond.evidence_ids,
        },
    };
    blocks[Diamond.join.index()].terminator = .{ .jump = .{ .target = reentry_dispatch } };
    const function_blocks = [_]ir.BlockId{
        Diamond.entry,
        Diamond.then_block,
        Diamond.else_block,
        Diamond.join,
        reentry_dispatch,
        reentry_then,
        reentry_else,
        reentry_merge,
        exit_block,
    };
    var functions = Diamond.functions;
    functions[Diamond.function_id.index()].blocks = &function_blocks;
    var program = Diamond.program;
    program.functions = &functions;
    program.blocks = &blocks;

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());

    var plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqual(Diamond.consume, plan.role(Diamond.produce).fused_invocation_producer);
    const projection = plan.invocationProjection(&program, Diamond.produce).?;
    try std.testing.expectEqual(pack_plan.InvocationProjectionReentry.indirect_region, projection.reentry);
    try std.testing.expectEqualSlices(
        ir.BlockId,
        &.{ reentry_dispatch, reentry_then, reentry_else, reentry_merge },
        projection.reentry_blocks,
    );
    try std.testing.expectEqualSlices(
        pack_plan.InvocationProjectionReentryEdge,
        &.{
            .{ .source = Diamond.join, .target = reentry_dispatch },
            .{ .source = reentry_dispatch, .target = reentry_then },
            .{ .source = reentry_dispatch, .target = reentry_else },
            .{ .source = reentry_then, .target = reentry_merge },
            .{ .source = reentry_else, .target = reentry_merge },
            .{ .source = reentry_merge, .target = Diamond.entry },
        },
        projection.reentry_edges,
    );
    try std.testing.expectEqualSlices(
        pack_plan.InvocationProjectionExitEdge,
        &.{.{ .source = reentry_merge, .target = exit_block }},
        projection.exit_edges,
    );
    try std.testing.expect(pack_plan.invocationProjectionIsMovable(&program, projection));

    var duplicate_reentry = projection;
    duplicate_reentry.reentry_blocks = &.{ reentry_dispatch, reentry_then, reentry_else, reentry_merge, reentry_merge };
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, duplicate_reentry));

    var reordered_reentry = projection;
    reordered_reentry.reentry_blocks = &.{ reentry_dispatch, reentry_merge, reentry_then, reentry_else };
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, reordered_reentry));

    var detached_reentry = projection;
    detached_reentry.reentry_blocks = &.{ reentry_dispatch, reentry_then, reentry_else, reentry_merge, exit_block };
    detached_reentry.reentry_edges = &.{
        .{ .source = Diamond.join, .target = reentry_dispatch },
        .{ .source = reentry_dispatch, .target = reentry_then },
        .{ .source = reentry_dispatch, .target = reentry_else },
        .{ .source = reentry_then, .target = reentry_merge },
        .{ .source = reentry_else, .target = reentry_merge },
        .{ .source = reentry_merge, .target = Diamond.entry },
        .{ .source = reentry_merge, .target = exit_block },
    };
    detached_reentry.exit_edges = &.{};
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, detached_reentry));

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());

    blocks[reentry_dispatch.index()].terminator = .{ .branch = .{
        .condition = Diamond.condition,
        .then_edge = .{ .target = reentry_then },
        .else_edge = .{ .target = exit_block },
    } };
    var multiple_exit_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer multiple_exit_plan.deinit();
    const multiple_exit_projection = multiple_exit_plan.invocationProjection(&program, Diamond.produce).?;
    try std.testing.expectEqualSlices(
        ir.BlockId,
        &.{ reentry_dispatch, reentry_then, reentry_merge },
        multiple_exit_projection.reentry_blocks,
    );
    try std.testing.expectEqualSlices(
        pack_plan.InvocationProjectionExitEdge,
        &.{
            .{ .source = reentry_dispatch, .target = exit_block },
            .{ .source = reentry_merge, .target = exit_block },
        },
        multiple_exit_projection.exit_edges,
    );
    try std.testing.expect(pack_plan.invocationProjectionIsMovable(&program, multiple_exit_projection));

    var multiple_exit_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer multiple_exit_report.deinit();
    try std.testing.expect(multiple_exit_report.isClean());

    blocks[reentry_dispatch.index()].terminator = .{ .branch = .{
        .condition = Diamond.condition,
        .then_edge = .{ .target = reentry_then },
        .else_edge = .{ .target = reentry_else },
    } };
    blocks[Diamond.join.index()].terminator = .{ .branch = .{
        .condition = Diamond.condition,
        .then_edge = .{ .target = reentry_then },
        .else_edge = .{ .target = reentry_else },
    } };
    var convergent_roots_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer convergent_roots_plan.deinit();
    try std.testing.expectEqual(Diamond.consume, convergent_roots_plan.role(Diamond.produce).fused_invocation_producer);
    const convergent_projection = convergent_roots_plan.invocationProjection(&program, Diamond.produce).?;
    try std.testing.expectEqualSlices(
        ir.BlockId,
        &.{ reentry_then, reentry_else, reentry_merge },
        convergent_projection.reentry_blocks,
    );
    try std.testing.expectEqualSlices(
        pack_plan.InvocationProjectionReentryEdge,
        &.{
            .{ .source = Diamond.join, .target = reentry_then },
            .{ .source = Diamond.join, .target = reentry_else },
            .{ .source = reentry_then, .target = reentry_merge },
            .{ .source = reentry_else, .target = reentry_merge },
            .{ .source = reentry_merge, .target = Diamond.entry },
        },
        convergent_projection.reentry_edges,
    );
    try std.testing.expectEqualSlices(
        pack_plan.InvocationProjectionExitEdge,
        &.{.{ .source = reentry_merge, .target = exit_block }},
        convergent_projection.exit_edges,
    );

    var convergent_roots_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer convergent_roots_report.deinit();
    try std.testing.expect(convergent_roots_report.isClean());

    blocks[Diamond.join.index()].terminator = .{ .branch = .{
        .condition = Diamond.condition,
        .then_edge = .{ .target = Diamond.entry },
        .else_edge = .{ .target = reentry_dispatch },
    } };
    var multiple_entry_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer multiple_entry_plan.deinit();
    try std.testing.expectEqual(Diamond.consume, multiple_entry_plan.role(Diamond.produce).fused_invocation_producer);
    const multiple_entry_projection = multiple_entry_plan.invocationProjection(&program, Diamond.produce).?;
    try std.testing.expectEqual(pack_plan.InvocationProjectionReentry.indirect_region, multiple_entry_projection.reentry);
    try std.testing.expectEqualSlices(
        pack_plan.InvocationProjectionReentryEdge,
        &.{
            .{ .source = Diamond.join, .target = Diamond.entry },
            .{ .source = Diamond.join, .target = reentry_dispatch },
            .{ .source = reentry_dispatch, .target = reentry_then },
            .{ .source = reentry_dispatch, .target = reentry_else },
            .{ .source = reentry_then, .target = reentry_merge },
            .{ .source = reentry_else, .target = reentry_merge },
            .{ .source = reentry_merge, .target = Diamond.entry },
        },
        multiple_entry_projection.reentry_edges,
    );
    try std.testing.expect(pack_plan.invocationProjectionIsMovable(&program, multiple_entry_projection));

    var omitted_entry = multiple_entry_projection;
    omitted_entry.reentry_edges = multiple_entry_projection.reentry_edges[0 .. multiple_entry_projection.reentry_edges.len - 1];
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, omitted_entry));

    var duplicated_entry = multiple_entry_projection;
    duplicated_entry.reentry_edges = &.{
        .{ .source = Diamond.join, .target = Diamond.entry },
        .{ .source = Diamond.join, .target = Diamond.entry },
        .{ .source = Diamond.join, .target = reentry_dispatch },
        .{ .source = reentry_dispatch, .target = reentry_then },
        .{ .source = reentry_dispatch, .target = reentry_else },
        .{ .source = reentry_then, .target = reentry_merge },
        .{ .source = reentry_else, .target = reentry_merge },
        .{ .source = reentry_merge, .target = Diamond.entry },
    };
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, duplicated_entry));

    var multiple_entry_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer multiple_entry_report.deinit();
    try std.testing.expect(multiple_entry_report.isClean());

    blocks[Diamond.join.index()].terminator = .{ .jump = .{ .target = reentry_dispatch } };
    blocks[reentry_merge.index()].terminator = .{ .branch = .{
        .condition = Diamond.condition,
        .then_edge = .{ .target = Diamond.then_block },
        .else_edge = .{ .target = exit_block },
    } };
    var bypass_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer bypass_plan.deinit();
    try std.testing.expect(bypass_plan.role(Diamond.produce) == .ordinary);
    try std.testing.expect(bypass_plan.invocationProjection(&program, Diamond.produce) == null);

    var bypass_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer bypass_report.deinit();
    try std.testing.expect(bypass_report.contains(.variadic_result_arity));
    try std.testing.expect(bypass_report.contains(.unsupported_readable_pack_operation));

    blocks[reentry_merge.index()].terminator = .{ .branch = .{
        .condition = Diamond.condition,
        .then_edge = .{ .target = Diamond.entry },
        .else_edge = .{ .target = reentry_dispatch },
    } };
    var cyclic_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer cyclic_plan.deinit();
    try std.testing.expect(cyclic_plan.role(Diamond.produce) == .ordinary);
    try std.testing.expect(cyclic_plan.invocationProjection(&program, Diamond.produce) == null);
}

test "direct post-consumer backedge records iterative invocation projection" {
    const exit_block = ir.BlockId.fromIndex(Diamond.blocks.len);
    var packs = Diamond.packs;
    var instructions = Diamond.instructions;
    var blocks = Diamond.blocks ++ [_]ir.Block{.{
        .id = exit_block,
        .function = Diamond.function_id,
        .terminator = .{ .return_values = &.{Diamond.result} },
        .evidence = &Diamond.evidence_ids,
    }};
    blocks[Diamond.join.index()].terminator = .{ .branch = .{
        .condition = Diamond.condition,
        .then_edge = .{ .target = Diamond.entry },
        .else_edge = .{ .target = exit_block },
    } };
    const function_blocks = [_]ir.BlockId{
        Diamond.entry,
        Diamond.then_block,
        Diamond.else_block,
        Diamond.join,
        exit_block,
    };
    var functions = Diamond.functions;
    functions[Diamond.function_id.index()].blocks = &function_blocks;
    var program = Diamond.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.value_packs = &packs;

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());

    var plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqual(Diamond.consume, plan.role(Diamond.produce).fused_invocation_producer);
    const projection = plan.invocationProjection(&program, Diamond.produce).?;
    try std.testing.expectEqual(pack_plan.InvocationProjectionReentry.direct_backedge, projection.reentry);
    try std.testing.expectEqual(@as(usize, 0), projection.reentry_blocks.len);
    try std.testing.expectEqualSlices(
        pack_plan.InvocationProjectionReentryEdge,
        &.{.{ .source = Diamond.join, .target = Diamond.entry }},
        projection.reentry_edges,
    );
    try std.testing.expectEqualSlices(
        pack_plan.InvocationProjectionExitEdge,
        &.{.{ .source = Diamond.join, .target = exit_block }},
        projection.exit_edges,
    );
    var invalid_pack = projection;
    invalid_pack.pack = ir.ValuePackId.fromIndex(Diamond.packs.len);
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, invalid_pack));
    instructions[Diamond.produce.index()].pack_result = null;
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    instructions[Diamond.produce.index()].pack_result = Diamond.open_pack;
    packs[Diamond.open_pack.index()].origin = .{ .varargs = Diamond.function_id };
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    packs[Diamond.open_pack.index()].origin = .{ .instruction_result = Diamond.produce };
    const original_consumer_operation = instructions[Diamond.consume.index()].operation;
    instructions[Diamond.consume.index()].operation.call.argument_pack = null;
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    instructions[Diamond.consume.index()].operation = .{ .constant = .{ .integer = "0" } };
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    instructions[Diamond.consume.index()].operation = original_consumer_operation;
    const original_exit_terminator = blocks[exit_block.index()].terminator;
    blocks[exit_block.index()].terminator = .{ .jump = .{ .target = Diamond.then_block } };
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    blocks[exit_block.index()].terminator = original_exit_terminator;
    var invalid_exit_source = projection;
    invalid_exit_source.exit_edges = &.{.{ .source = Diamond.then_block, .target = exit_block }};
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, invalid_exit_source));
    var invalid_exit_target = projection;
    invalid_exit_target.exit_edges = &.{.{ .source = Diamond.join, .target = Diamond.then_block }};
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, invalid_exit_target));
    var invalid_moved_edge = projection;
    invalid_moved_edge.moved_edges = &.{.{ .source = Diamond.join, .target = Diamond.entry }};
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, invalid_moved_edge));
    const original_consumer_terminator = blocks[Diamond.join.index()].terminator;
    blocks[Diamond.join.index()].terminator = .{ .jump = .{ .target = Diamond.entry } };
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    blocks[Diamond.join.index()].terminator = .{ .branch = .{
        .condition = Diamond.condition,
        .then_edge = .{ .target = Diamond.entry },
        .else_edge = .{ .target = Diamond.then_block },
    } };
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    blocks[Diamond.join.index()].terminator = original_consumer_terminator;
    const original_moved_terminator = blocks[Diamond.then_block.index()].terminator;
    blocks[Diamond.then_block.index()].terminator = .{ .return_values = &.{} };
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    blocks[Diamond.then_block.index()].terminator = .{ .jump = .{ .target = Diamond.entry } };
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    blocks[Diamond.then_block.index()].terminator = original_moved_terminator;
    const original_producer_instructions = blocks[Diamond.entry.index()].instructions;
    const stale_producer_instructions = [_]ir.InstructionId{
        Diamond.get_callee,
        Diamond.produce,
        Diamond.get_callee,
        Diamond.condition_instruction,
    };
    blocks[Diamond.entry.index()].instructions = &stale_producer_instructions;
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    blocks[Diamond.entry.index()].instructions = original_producer_instructions;
    instructions[Diamond.consume.index()].id = Diamond.join_gap;
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    instructions[Diamond.consume.index()].id = Diamond.consume;
    instructions[Diamond.then_gap.index()].id = Diamond.else_gap;
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    instructions[Diamond.then_gap.index()].id = Diamond.then_gap;
    instructions[Diamond.then_gap.index()].block = Diamond.else_block;
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    instructions[Diamond.then_gap.index()].block = Diamond.then_block;
    try std.testing.expectEqualSlices(
        ir.BlockId,
        &.{ Diamond.entry, Diamond.then_block, Diamond.else_block, Diamond.join },
        projection.blocks,
    );
    try std.testing.expectEqualSlices(
        ir.InstructionId,
        &.{ Diamond.condition_instruction, Diamond.then_gap, Diamond.else_gap, Diamond.join_gap },
        projection.gaps,
    );
    try std.testing.expect(pack_plan.invocationProjectionIsMovable(&program, projection));

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());
}

test "unreachable dead predecessor preserves an unchanged invocation projection" {
    const dead_predecessor = ir.BlockId.fromIndex(Diamond.blocks.len);
    const blocks = Diamond.blocks ++ [_]ir.Block{.{
        .id = dead_predecessor,
        .function = Diamond.function_id,
        .terminator = .{ .jump = .{ .target = Diamond.then_block } },
        .evidence = &Diamond.evidence_ids,
    }};
    const function_blocks = [_]ir.BlockId{
        Diamond.entry,
        Diamond.then_block,
        Diamond.else_block,
        Diamond.join,
        dead_predecessor,
    };
    var functions = Diamond.functions;
    functions[Diamond.function_id.index()].blocks = &function_blocks;
    var program = Diamond.program;
    program.functions = &functions;
    program.blocks = &blocks;

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());

    var plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqual(Diamond.consume, plan.role(Diamond.produce).fused_invocation_producer);
    const projection = plan.invocationProjection(&program, Diamond.produce).?;
    try std.testing.expect(pack_plan.invocationProjectionIsMovable(&program, projection));

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());
}

test "indirect invocation latch refuses a reachable side entry" {
    const reentry_dispatch = ir.BlockId.fromIndex(Diamond.blocks.len);
    const exit_block = ir.BlockId.fromIndex(Diamond.blocks.len + 1);
    const side_entry = ir.BlockId.fromIndex(Diamond.blocks.len + 2);
    const side_condition = ir.ValueId.fromIndex(Diamond.values.len);
    const values = Diamond.values ++ [_]ir.Value{.{
        .id = side_condition,
        .function = Diamond.function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    var blocks = Diamond.blocks ++ [_]ir.Block{
        .{
            .id = reentry_dispatch,
            .function = Diamond.function_id,
            .terminator = .{ .branch = .{
                .condition = side_condition,
                .then_edge = .{ .target = Diamond.entry },
                .else_edge = .{ .target = exit_block },
            } },
            .evidence = &Diamond.evidence_ids,
        },
        .{
            .id = exit_block,
            .function = Diamond.function_id,
            .terminator = .{ .return_values = &.{} },
            .evidence = &Diamond.evidence_ids,
        },
        .{
            .id = side_entry,
            .function = Diamond.function_id,
            .terminator = .{ .jump = .{ .target = reentry_dispatch } },
            .evidence = &Diamond.evidence_ids,
        },
    };
    blocks[Diamond.join.index()].terminator = .{ .jump = .{ .target = reentry_dispatch } };
    const function_blocks = [_]ir.BlockId{
        side_entry,
        Diamond.entry,
        Diamond.then_block,
        Diamond.else_block,
        Diamond.join,
        reentry_dispatch,
        exit_block,
    };
    var functions = Diamond.functions;
    functions[Diamond.function_id.index()].parameters = &.{side_condition};
    functions[Diamond.function_id.index()].blocks = &function_blocks;
    functions[Diamond.function_id.index()].entry_block = side_entry;
    var program = Diamond.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.values = &values;

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());

    var plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expect(plan.role(Diamond.produce) == .ordinary);
    try std.testing.expect(plan.invocationProjection(&program, Diamond.produce) == null);
}
