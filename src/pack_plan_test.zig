const std = @import("std");
const ir = @import("ir.zig");
const pack_plan = @import("pack_plan.zig");

const Plan = pack_plan.Plan;
test "sole adjacent open-call adjustment receives a shared fusion plan" {
    const fixtures = @import("fixtures.zig");
    var plan = try Plan.init(std.testing.allocator, &fixtures.open_pack_adjust_module.program);
    defer plan.deinit();
    try std.testing.expectEqual(
        fixtures.open_pack_adjust_module.i_adjust,
        plan.role(fixtures.open_pack_adjust_module.i_call).fused_invocation_producer,
    );
    try std.testing.expectEqual(
        fixtures.open_pack_adjust_module.i_call,
        plan.role(fixtures.open_pack_adjust_module.i_adjust).fused_adjustment,
    );
}

test "sole nonadjacent pack adjustment materializes at its producer" {
    const fixtures = @import("fixtures.zig");
    const gap_id = ir.InstructionId.fromIndex(fixtures.open_pack_adjust_module.instructions.len);
    const instructions = fixtures.open_pack_adjust_module.instructions ++ [_]ir.Instruction{.{
        .id = gap_id,
        .block = fixtures.open_pack_adjust_module.b_entry,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "observed",
            .value = fixtures.open_pack_adjust_module.v_callee,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
        .evidence = &.{fixtures.open_pack_adjust_module.proof},
    }};
    const reordered = [_]ir.InstructionId{
        fixtures.open_pack_adjust_module.i_get,
        fixtures.open_pack_adjust_module.i_call,
        gap_id,
        fixtures.open_pack_adjust_module.i_adjust,
    };
    var blocks = fixtures.open_pack_adjust_module.blocks;
    blocks[0].instructions = &reordered;
    var program = fixtures.open_pack_adjust_module.program;
    program.blocks = &blocks;
    program.instructions = &instructions;
    var plan = try Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqual(
        fixtures.open_pack_adjust_module.i_adjust,
        plan.role(fixtures.open_pack_adjust_module.i_call).materialized_invocation_producer,
    );
    try std.testing.expectEqual(
        fixtures.open_pack_adjust_module.i_call,
        plan.role(fixtures.open_pack_adjust_module.i_adjust).materialized_adjustment,
    );
}

test "same-block fixed and expanded uses receive stored pack roles" {
    const fixture = @import("fixtures.zig").open_pack_adjust_module;
    const gap_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const instructions = fixture.instructions ++ [_]ir.Instruction{.{
        .id = gap_id,
        .block = fixture.b_entry,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "observed",
            .value = fixture.v_callee,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
        .evidence = &.{fixture.proof},
    }};
    const instruction_ids = [_]ir.InstructionId{ fixture.i_get, fixture.i_call, gap_id, fixture.i_adjust };
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].instructions = &instruction_ids;
    blocks[fixture.b_entry.index()].terminator = .{ .return_expanded = .{
        .values = &.{fixture.v_first},
        .pack = fixture.p_results,
    } };
    var program = fixture.program;
    program.blocks = &blocks;
    program.instructions = &instructions;

    var plan = try Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expect(plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(
        fixture.i_call,
        plan.role(fixture.i_adjust).stored_adjustment,
    );
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        plan.terminatorRole(fixture.b_entry),
    );
}

test "sole adjacent open call table tail receives producer fusion" {
    const fixture = @import("fixtures.zig").open_pack_adjust_module;
    var values = fixture.values;
    values[fixture.v_first.index()].type = .{ .kind = .table };
    var instructions = fixture.instructions;
    instructions[fixture.i_adjust.index()].operation = .{ .make_table_literal = .{
        .fields = &.{},
        .tail_pack = fixture.p_results,
    } };
    instructions[fixture.i_adjust.index()].effects = .table_constructor;
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;

    var plan = try Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqual(
        fixture.i_adjust,
        plan.role(fixture.i_call).fused_invocation_producer,
    );
    try std.testing.expect(plan.role(fixture.i_adjust) == .ordinary);
}

test "ordinary invocation argument packs store across an observable gap" {
    const fixture = @import("fixtures.zig").open_pack_adjust_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_adjust.index()].operation = .{ .call = .{
        .callee = fixture.v_callee,
        .arguments = &.{},
        .argument_pack = fixture.p_results,
        .result_arity = .{ .fixed = 1 },
    } };
    instructions[fixture.i_adjust.index()].effects = .dynamic_call;
    var program = fixture.program;
    program.instructions = &instructions;

    var adjacent = try Plan.init(std.testing.allocator, &program);
    defer adjacent.deinit();
    try std.testing.expectEqual(
        fixture.i_adjust,
        adjacent.role(fixture.i_call).fused_invocation_producer,
    );

    const gap_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    var delayed_instructions = fixture.instructions ++ [_]ir.Instruction{.{
        .id = gap_id,
        .block = fixture.b_entry,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "after_producer",
            .value = fixture.v_callee,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
        .evidence = &.{fixture.proof},
    }};
    delayed_instructions[fixture.i_adjust.index()] = instructions[fixture.i_adjust.index()];
    const reordered = [_]ir.InstructionId{ fixture.i_get, fixture.i_call, gap_id, fixture.i_adjust };
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].instructions = &reordered;
    program.blocks = &blocks;
    program.instructions = &delayed_instructions;
    var nonadjacent = try Plan.init(std.testing.allocator, &program);
    defer nonadjacent.deinit();
    try std.testing.expect(nonadjacent.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expect(nonadjacent.storedPackServesInstruction(fixture.i_call, fixture.i_adjust));
    try std.testing.expect(nonadjacent.invocationProjection(&program, fixture.i_call) == null);
}

test "single-use open packs project across movable local gaps" {
    const fixture = @import("fixtures.zig").open_pack_adjust_module;
    const gap_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const gap_value = ir.ValueId.fromIndex(fixture.values.len);
    var values = fixture.values ++ [_]ir.Value{.{
        .id = gap_value,
        .function = fixture.f_entry,
        .type = .integer,
        .origin = .{ .instruction_result = .{ .instruction = gap_id, .index = 0 } },
    }};
    var instructions = fixture.instructions ++ [_]ir.Instruction{.{
        .id = gap_id,
        .block = fixture.b_entry,
        .operation = .{ .constant = .{ .integer = "7" } },
        .results = &.{gap_value},
        .effects = .pure,
        .evidence = &.{fixture.proof},
    }};
    const projected_ids = [_]ir.InstructionId{ fixture.i_get, fixture.i_call, gap_id, fixture.i_adjust };
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].instructions = &projected_ids;
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.blocks = &blocks;

    values[fixture.v_first.index()].type = .{ .kind = .table };
    instructions[fixture.i_adjust.index()].operation = .{ .make_table_literal = .{
        .fields = &.{},
        .tail_pack = fixture.p_results,
    } };
    instructions[fixture.i_adjust.index()].effects = .table_constructor;
    var table_plan = try Plan.init(std.testing.allocator, &program);
    defer table_plan.deinit();
    try std.testing.expectEqual(fixture.i_adjust, table_plan.role(fixture.i_call).fused_invocation_producer);
    const table_projection = table_plan.invocationProjection(&program, fixture.i_call).?;
    try std.testing.expectEqual(pack_plan.ProjectionConsumer{ .instruction = fixture.i_adjust }, table_projection.consumer);
    try std.testing.expectEqualSlices(ir.BlockId, &.{fixture.b_entry}, table_projection.blocks);
    try std.testing.expectEqualSlices(ir.InstructionId, &.{gap_id}, table_projection.gaps);

    instructions[fixture.i_adjust.index()].operation = .{ .table_set_pack = .{
        .table = fixture.v_callee,
        .first_index = 1,
        .pack = fixture.p_results,
    } };
    instructions[fixture.i_adjust.index()].results = &.{};
    instructions[fixture.i_adjust.index()].effects = .raw_table_write;
    var table_write_plan = try Plan.init(std.testing.allocator, &program);
    defer table_write_plan.deinit();
    try std.testing.expectEqual(fixture.i_adjust, table_write_plan.role(fixture.i_call).fused_invocation_producer);
    const table_write_projection = table_write_plan.invocationProjection(&program, fixture.i_call).?;
    try std.testing.expect(pack_plan.invocationProjectionIsMovable(&program, table_write_projection));

    instructions[fixture.i_adjust.index()].results = &.{fixture.v_first};
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, table_write_projection));
    instructions[fixture.i_adjust.index()].results = &.{};
    instructions[fixture.i_adjust.index()].pack_result = fixture.p_results;
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, table_write_projection));
    instructions[fixture.i_adjust.index()].pack_result = null;
    instructions[fixture.i_adjust.index()].operation.table_set_pack.pack = ir.ValuePackId.fromIndex(1);
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, table_write_projection));

    values[fixture.v_first.index()].type = .dynamic;
    instructions[fixture.i_adjust.index()].operation = .{ .call = .{
        .callee = fixture.v_callee,
        .arguments = &.{},
        .argument_pack = fixture.p_results,
        .result_arity = .{ .fixed = 1 },
    } };
    instructions[fixture.i_adjust.index()].results = &.{fixture.v_first};
    instructions[fixture.i_adjust.index()].effects = .dynamic_call;
    var argument_plan = try Plan.init(std.testing.allocator, &program);
    defer argument_plan.deinit();
    try std.testing.expectEqual(fixture.i_adjust, argument_plan.role(fixture.i_call).fused_invocation_producer);
    try std.testing.expectEqualSlices(
        ir.InstructionId,
        &.{gap_id},
        argument_plan.invocationProjection(&program, fixture.i_call).?.gaps,
    );

    instructions[gap_id.index()].effects = .semantic_environment_read;
    var impure_plan = try Plan.init(std.testing.allocator, &program);
    defer impure_plan.deinit();
    try std.testing.expect(impure_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expect(impure_plan.storedPackServesInstruction(fixture.i_call, fixture.i_adjust));
    try std.testing.expect(impure_plan.invocationProjection(&program, fixture.i_call) == null);

    instructions[gap_id.index()].effects = .pure;
    instructions[gap_id.index()].block = ir.BlockId.fromIndex(fixture.blocks.len);
    var wrong_owner_plan = try Plan.init(std.testing.allocator, &program);
    defer wrong_owner_plan.deinit();
    try std.testing.expect(wrong_owner_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expect(wrong_owner_plan.storedPackServesInstruction(fixture.i_call, fixture.i_adjust));

    instructions[gap_id.index()].block = fixture.b_entry;
    instructions[gap_id.index()].operation = .{ .make_closure = .{ .function = fixture.f_entry, .bindings = &.{} } };
    values[gap_value.index()].type = .function;
    var closure_plan = try Plan.init(std.testing.allocator, &program);
    defer closure_plan.deinit();
    try std.testing.expect(closure_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expect(closure_plan.storedPackServesInstruction(fixture.i_call, fixture.i_adjust));
}

test "single-use open packs project through one acyclic direct successor" {
    const fixture = @import("fixtures.zig").open_pack_adjust_module;
    const consumer_block = ir.BlockId.fromIndex(fixture.blocks.len);
    const forwarding_block = ir.BlockId.fromIndex(fixture.blocks.len + 1);
    const producer_gap_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const consumer_gap_id = ir.InstructionId.fromIndex(fixture.instructions.len + 1);
    const producer_gap_value = ir.ValueId.fromIndex(fixture.values.len);
    const consumer_gap_value = ir.ValueId.fromIndex(fixture.values.len + 1);
    var values = fixture.values ++ [_]ir.Value{
        .{
            .id = producer_gap_value,
            .function = fixture.f_entry,
            .type = .integer,
            .origin = .{ .instruction_result = .{ .instruction = producer_gap_id, .index = 0 } },
        },
        .{
            .id = consumer_gap_value,
            .function = fixture.f_entry,
            .type = .integer,
            .origin = .{ .instruction_result = .{ .instruction = consumer_gap_id, .index = 0 } },
        },
    };
    var instructions = fixture.instructions ++ [_]ir.Instruction{
        .{
            .id = producer_gap_id,
            .block = fixture.b_entry,
            .operation = .{ .constant = .{ .integer = "1" } },
            .results = &.{producer_gap_value},
            .effects = .pure,
            .evidence = &.{fixture.proof},
        },
        .{
            .id = consumer_gap_id,
            .block = consumer_block,
            .operation = .{ .constant = .{ .integer = "2" } },
            .results = &.{consumer_gap_value},
            .effects = .pure,
            .evidence = &.{fixture.proof},
        },
    };
    instructions[fixture.i_adjust.index()].block = consumer_block;
    instructions[fixture.i_adjust.index()].operation = .{ .call = .{
        .callee = fixture.v_callee,
        .arguments = &.{},
        .argument_pack = fixture.p_results,
        .result_arity = .{ .fixed = 1 },
    } };
    instructions[fixture.i_adjust.index()].effects = .dynamic_call;
    const producer_ids = [_]ir.InstructionId{ fixture.i_get, fixture.i_call, producer_gap_id };
    const consumer_ids = [_]ir.InstructionId{ consumer_gap_id, fixture.i_adjust };
    var blocks = fixture.blocks ++ [_]ir.Block{
        .{
            .id = consumer_block,
            .function = fixture.f_entry,
            .instructions = &consumer_ids,
            .terminator = .{ .return_values = &.{fixture.v_first} },
        },
        .{
            .id = forwarding_block,
            .function = fixture.f_entry,
            .terminator = .{ .jump = .{ .target = consumer_block } },
        },
    };
    blocks[fixture.b_entry.index()].instructions = &producer_ids;
    blocks[fixture.b_entry.index()].terminator = .{ .jump = .{ .target = consumer_block } };
    const function_blocks = [_]ir.BlockId{ fixture.b_entry, consumer_block, forwarding_block };
    var functions = fixture.functions;
    functions[fixture.f_entry.index()].blocks = &function_blocks;
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;

    var argument_plan = try Plan.init(std.testing.allocator, &program);
    defer argument_plan.deinit();
    try std.testing.expectEqual(fixture.i_adjust, argument_plan.role(fixture.i_call).fused_invocation_producer);
    const argument_projection = argument_plan.invocationProjection(&program, fixture.i_call).?;
    try std.testing.expectEqual(pack_plan.ProjectionConsumer{ .instruction = fixture.i_adjust }, argument_projection.consumer);
    try std.testing.expectEqualSlices(ir.BlockId, &.{ fixture.b_entry, consumer_block }, argument_projection.blocks);
    try std.testing.expectEqualSlices(ir.InstructionId, &.{ producer_gap_id, consumer_gap_id }, argument_projection.gaps);

    values[fixture.v_first.index()].type = .{ .kind = .table };
    instructions[fixture.i_adjust.index()].operation = .{ .make_table_literal = .{
        .fields = &.{},
        .tail_pack = fixture.p_results,
    } };
    instructions[fixture.i_adjust.index()].effects = .table_constructor;
    var table_plan = try Plan.init(std.testing.allocator, &program);
    defer table_plan.deinit();
    try std.testing.expectEqual(fixture.i_adjust, table_plan.role(fixture.i_call).fused_invocation_producer);

    values[fixture.v_first.index()].type = .integer;
    instructions[fixture.i_adjust.index()].operation = .{ .constant = .{ .integer = "7" } };
    instructions[fixture.i_adjust.index()].effects = .pure;
    blocks[consumer_block.index()].terminator = .{ .return_expanded = .{
        .values = &.{fixture.v_first},
        .pack = fixture.p_results,
    } };
    var return_plan = try Plan.init(std.testing.allocator, &program);
    defer return_plan.deinit();
    try std.testing.expectEqual(consumer_block, return_plan.role(fixture.i_call).fused_return_producer);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .fused_invocation_return = fixture.i_call },
        return_plan.terminatorRole(consumer_block),
    );

    instructions[producer_gap_id.index()].effects = .semantic_environment_read;
    var impure_producer_plan = try Plan.init(std.testing.allocator, &program);
    defer impure_producer_plan.deinit();
    try std.testing.expect(impure_producer_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        impure_producer_plan.terminatorRole(consumer_block),
    );
    instructions[producer_gap_id.index()].effects = .pure;

    instructions[consumer_gap_id.index()].effects = .semantic_environment_read;
    var impure_consumer_plan = try Plan.init(std.testing.allocator, &program);
    defer impure_consumer_plan.deinit();
    try std.testing.expect(impure_consumer_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        impure_consumer_plan.terminatorRole(consumer_block),
    );
    instructions[consumer_gap_id.index()].effects = .pure;

    instructions[fixture.i_adjust.index()].operation = .{ .call = .{
        .callee = fixture.v_callee,
        .arguments = &.{},
        .argument_pack = fixture.p_results,
        .result_arity = .{ .fixed = 1 },
    } };
    instructions[fixture.i_adjust.index()].effects = .dynamic_call;
    blocks[consumer_block.index()].terminator = .{ .jump = .{ .target = fixture.b_entry } };
    var cyclic_plan = try Plan.init(std.testing.allocator, &program);
    defer cyclic_plan.deinit();
    try std.testing.expect(cyclic_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expect(cyclic_plan.storedPackServesInstruction(fixture.i_call, fixture.i_adjust));

    blocks[consumer_block.index()].terminator = .{ .jump = .{ .target = forwarding_block } };
    var bypass_reentry_plan = try Plan.init(std.testing.allocator, &program);
    defer bypass_reentry_plan.deinit();
    try std.testing.expect(bypass_reentry_plan.role(fixture.i_call) == .ordinary);

    blocks[consumer_block.index()].terminator = .{ .return_values = &.{fixture.v_first} };
    blocks[fixture.b_entry.index()].terminator = .{ .jump = .{ .target = forwarding_block } };
    var wider_plan = try Plan.init(std.testing.allocator, &program);
    defer wider_plan.deinit();
    try std.testing.expectEqual(fixture.i_adjust, wider_plan.role(fixture.i_call).fused_invocation_producer);
    const wider_projection = wider_plan.invocationProjection(&program, fixture.i_call).?;
    try std.testing.expectEqualSlices(
        ir.BlockId,
        &.{ fixture.b_entry, forwarding_block, consumer_block },
        wider_projection.blocks,
    );
    try std.testing.expectEqualSlices(
        ir.InstructionId,
        &.{ producer_gap_id, consumer_gap_id },
        wider_projection.gaps,
    );
}

test "stored argument pack composes with an open-result return producer" {
    const fixture = @import("fixtures.zig").open_pack_adjust_module;
    const consumer_block = ir.BlockId.fromIndex(fixture.blocks.len);
    const gap_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const returned_pack = ir.ValuePackId.fromIndex(fixture.value_packs.len);
    const packs = fixture.value_packs ++ [_]ir.ValuePack{.{
        .id = returned_pack,
        .function = fixture.f_entry,
        .origin = .{ .instruction_result = fixture.i_adjust },
        .evidence = &.{fixture.proof},
    }};
    var instructions = fixture.instructions ++ [_]ir.Instruction{.{
        .id = gap_id,
        .block = consumer_block,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "between_open_calls",
            .value = fixture.v_callee,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
        .evidence = &.{fixture.proof},
    }};
    instructions[fixture.i_adjust.index()] = .{
        .id = fixture.i_adjust,
        .block = consumer_block,
        .operation = .{ .call = .{
            .callee = fixture.v_callee,
            .arguments = &.{},
            .argument_pack = fixture.p_results,
            .result_arity = .{ .variadic = {} },
        } },
        .results = &.{},
        .pack_result = returned_pack,
        .effects = .dynamic_call,
        .evidence = &.{fixture.proof},
    };
    const producer_ids = [_]ir.InstructionId{ fixture.i_get, fixture.i_call };
    const consumer_ids = [_]ir.InstructionId{ gap_id, fixture.i_adjust };
    const blocks = [_]ir.Block{
        .{
            .id = fixture.b_entry,
            .function = fixture.f_entry,
            .instructions = &producer_ids,
            .terminator = .{ .jump = .{ .target = consumer_block } },
            .evidence = &.{fixture.proof},
        },
        .{
            .id = consumer_block,
            .function = fixture.f_entry,
            .instructions = &consumer_ids,
            .terminator = .{ .return_pack = returned_pack },
            .evidence = &.{fixture.proof},
        },
    };
    const function_blocks = [_]ir.BlockId{ fixture.b_entry, consumer_block };
    var functions = fixture.functions;
    functions[fixture.f_entry.index()].blocks = &function_blocks;
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = fixture.values[0..1];
    program.value_packs = &packs;

    var plan = try Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expect(plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expect(plan.storedPackServesInstruction(fixture.i_call, fixture.i_adjust));
    try std.testing.expectEqual(consumer_block, plan.role(fixture.i_adjust).fused_return_producer);
}

test "single-use open pack returns project across movable local gaps" {
    const fixture = @import("fixtures.zig").open_pack_adjust_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_adjust.index()].operation = .{ .constant = .{ .integer = "7" } };
    instructions[fixture.i_adjust.index()].effects = .pure;
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].terminator = .{ .return_pack = fixture.p_results };
    var program = fixture.program;
    program.instructions = &instructions;
    program.blocks = &blocks;

    var return_plan = try Plan.init(std.testing.allocator, &program);
    defer return_plan.deinit();
    try std.testing.expectEqual(fixture.b_entry, return_plan.role(fixture.i_call).fused_return_producer);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .fused_invocation_return = fixture.i_call },
        return_plan.terminatorRole(fixture.b_entry),
    );
    const projection = return_plan.invocationProjection(&program, fixture.i_call).?;
    try std.testing.expectEqual(pack_plan.ProjectionConsumer{ .terminator = fixture.b_entry }, projection.consumer);
    try std.testing.expectEqualSlices(ir.BlockId, &.{fixture.b_entry}, projection.blocks);
    try std.testing.expectEqualSlices(ir.InstructionId, &.{fixture.i_adjust}, projection.gaps);
    try std.testing.expect(pack_plan.invocationProjectionIsMovable(&program, projection));

    blocks[fixture.b_entry.index()].terminator = .{ .return_values = &.{} };
    try std.testing.expect(!pack_plan.invocationProjectionIsMovable(&program, projection));
    blocks[fixture.b_entry.index()].terminator = .{ .return_pack = fixture.p_results };

    instructions[fixture.i_adjust.index()].operation = .{ .make_closure = .{ .function = fixture.f_entry, .bindings = &.{} } };
    program.instructions = &instructions;
    var closure_plan = try Plan.init(std.testing.allocator, &program);
    defer closure_plan.deinit();
    try std.testing.expect(closure_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        closure_plan.terminatorRole(fixture.b_entry),
    );
}

test "unreachable pack uses do not block reachable fusion" {
    const fixture = @import("fixtures.zig").open_pack_adjust_module;
    const dead_block_id = ir.BlockId.fromIndex(fixture.blocks.len);
    const dead_adjust_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const dead_value_id = ir.ValueId.fromIndex(fixture.values.len);
    const values = fixture.values ++ [_]ir.Value{.{
        .id = dead_value_id,
        .function = fixture.f_entry,
        .origin = .{ .instruction_result = .{ .instruction = dead_adjust_id, .index = 0 } },
    }};
    const instructions = fixture.instructions ++ [_]ir.Instruction{.{
        .id = dead_adjust_id,
        .block = dead_block_id,
        .operation = .{ .adjust_pack = fixture.p_results },
        .results = &.{dead_value_id},
        .effects = .pure,
    }};
    const blocks = fixture.blocks ++ [_]ir.Block{.{
        .id = dead_block_id,
        .function = fixture.f_entry,
        .instructions = &.{dead_adjust_id},
        .terminator = .{ .return_values = &.{dead_value_id} },
    }};
    const function_blocks = [_]ir.BlockId{ fixture.b_entry, dead_block_id };
    var functions = fixture.functions;
    functions[fixture.f_entry.index()].blocks = &function_blocks;
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;

    var plan = try Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqual(fixture.i_adjust, plan.role(fixture.i_call).fused_invocation_producer);
    try std.testing.expectEqual(fixture.i_call, plan.role(fixture.i_adjust).fused_adjustment);
    try std.testing.expect(plan.role(dead_adjust_id) == .ordinary);
}
