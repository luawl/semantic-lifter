const std = @import("std");
const cfg = @import("cfg.zig");
const ir = @import("ir.zig");
const irreducible_normalize = @import("irreducible_normalize.zig");
const irreducible_region = @import("irreducible_region.zig");
const structure = @import("structure.zig");
const structural_overlap = @import("structural_overlap.zig");

fn isEffectfulPrefix(program: *const ir.Program, block: ir.Block) bool {
    if (block.instructions.len != 4) return false;
    const operations = [_]std.meta.Tag(ir.Operation){
        .constant,
        .place_write,
        .constant,
        .place_write,
    };
    for (block.instructions, operations) |instruction_id, expected| {
        if (instruction_id.index() >= program.instructions.len) return false;
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.id != instruction_id or std.meta.activeTag(instruction.operation) != expected) return false;
    }
    return true;
}

test "multi-arm tuple continuation clones preserve effect order" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const arm_a = ir.BlockId.fromIndex(1);
    const arm_b = ir.BlockId.fromIndex(2);
    const arm_c = ir.BlockId.fromIndex(3);
    const prefix = ir.BlockId.fromIndex(4);
    const reset = ir.BlockId.fromIndex(5);
    const exit = ir.BlockId.fromIndex(6);

    const selector = ir.ValueId.fromIndex(0);
    const control = ir.ValueId.fromIndex(1);
    const limit = ir.ValueId.fromIndex(2);
    const step = ir.ValueId.fromIndex(3);
    const initial = ir.ValueId.fromIndex(4);
    const false_value = ir.ValueId.fromIndex(5);
    const a_parameters = [_]ir.ValueId{
        ir.ValueId.fromIndex(6),
        ir.ValueId.fromIndex(7),
        ir.ValueId.fromIndex(8),
        ir.ValueId.fromIndex(9),
    };
    const b_parameters = [_]ir.ValueId{
        ir.ValueId.fromIndex(10),
        ir.ValueId.fromIndex(11),
        ir.ValueId.fromIndex(12),
        ir.ValueId.fromIndex(13),
    };
    const c_parameters = [_]ir.ValueId{
        ir.ValueId.fromIndex(14),
        ir.ValueId.fromIndex(15),
        ir.ValueId.fromIndex(16),
        ir.ValueId.fromIndex(17),
    };
    const a_results = [_]ir.ValueId{
        ir.ValueId.fromIndex(18),
        ir.ValueId.fromIndex(19),
        ir.ValueId.fromIndex(20),
        ir.ValueId.fromIndex(21),
    };
    const b_results = [_]ir.ValueId{
        ir.ValueId.fromIndex(22),
        ir.ValueId.fromIndex(23),
        ir.ValueId.fromIndex(24),
        ir.ValueId.fromIndex(25),
    };
    const c_results = [_]ir.ValueId{
        ir.ValueId.fromIndex(26),
        ir.ValueId.fromIndex(27),
        ir.ValueId.fromIndex(28),
        ir.ValueId.fromIndex(29),
    };
    const prefix_value_a = ir.ValueId.fromIndex(30);
    const prefix_value_b = ir.ValueId.fromIndex(31);
    const reset_value = ir.ValueId.fromIndex(32);

    const false_instruction = ir.InstructionId.fromIndex(0);
    const a_instruction = ir.InstructionId.fromIndex(1);
    const b_instruction = ir.InstructionId.fromIndex(2);
    const c_instruction = ir.InstructionId.fromIndex(3);
    const prefix_constant_a = ir.InstructionId.fromIndex(4);
    const prefix_write_a = ir.InstructionId.fromIndex(5);
    const prefix_constant_b = ir.InstructionId.fromIndex(6);
    const prefix_write_b = ir.InstructionId.fromIndex(7);
    const reset_constant = ir.InstructionId.fromIndex(8);
    const reset_write_a = ir.InstructionId.fromIndex(9);
    const reset_write_b = ir.InstructionId.fromIndex(10);
    const place_a = ir.PlaceId.fromIndex(0);
    const place_b = ir.PlaceId.fromIndex(1);

    const seed_tuple = [_]ir.ValueId{ control, limit, step, initial };
    const a_to_b = [_]ir.ValueId{ a_results[3], a_results[1], a_results[2], false_value };
    const b_to_c = [_]ir.ValueId{ b_results[3], b_results[1], b_results[2], false_value };
    const c_to_a = [_]ir.ValueId{ c_results[3], c_results[1], c_results[2], false_value };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{false_instruction}, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = arm_a, .arguments = &seed_tuple },
            .else_edge = .{ .target = arm_b, .arguments = &seed_tuple },
        } } },
        .{ .id = arm_a, .function = function_id, .parameters = &a_parameters, .instructions = &.{a_instruction}, .terminator = .{ .branch = .{
            .condition = a_results[0],
            .then_edge = .{ .target = arm_b, .arguments = &a_to_b },
            .else_edge = .{ .target = prefix },
        } } },
        .{ .id = arm_b, .function = function_id, .parameters = &b_parameters, .instructions = &.{b_instruction}, .terminator = .{ .branch = .{
            .condition = b_results[0],
            .then_edge = .{ .target = arm_c, .arguments = &b_to_c },
            .else_edge = .{ .target = prefix },
        } } },
        .{ .id = arm_c, .function = function_id, .parameters = &c_parameters, .instructions = &.{c_instruction}, .terminator = .{ .branch = .{
            .condition = c_results[0],
            .then_edge = .{ .target = arm_a, .arguments = &c_to_a },
            .else_edge = .{ .target = prefix },
        } } },
        .{ .id = prefix, .function = function_id, .instructions = &.{ prefix_constant_a, prefix_write_a, prefix_constant_b, prefix_write_b }, .terminator = .{ .jump = .{ .target = reset } } },
        .{ .id = reset, .function = function_id, .instructions = &.{ reset_constant, reset_write_a, reset_write_b }, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };

    var values: [33]ir.Value = undefined;
    values[0] = .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } };
    values[1] = .{ .id = control, .function = function_id, .type = .number, .origin = .{ .parameter = 1 } };
    values[2] = .{ .id = limit, .function = function_id, .type = .number, .origin = .{ .parameter = 2 } };
    values[3] = .{ .id = step, .function = function_id, .type = .number, .origin = .{ .parameter = 3 } };
    values[4] = .{ .id = initial, .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } };
    values[5] = .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_instruction, .index = 0 } } };
    for (a_parameters, 0..) |value_id, index| values[6 + index] = .{ .id = value_id, .function = function_id, .type = if (index == 3) .boolean else .number, .origin = .{ .block_parameter = .{ .block = arm_a, .index = @intCast(index) } } };
    for (b_parameters, 0..) |value_id, index| values[10 + index] = .{ .id = value_id, .function = function_id, .type = if (index == 3) .boolean else .number, .origin = .{ .block_parameter = .{ .block = arm_b, .index = @intCast(index) } } };
    for (c_parameters, 0..) |value_id, index| values[14 + index] = .{ .id = value_id, .function = function_id, .type = if (index == 3) .boolean else .number, .origin = .{ .block_parameter = .{ .block = arm_c, .index = @intCast(index) } } };
    for (a_results, 0..) |value_id, index| values[18 + index] = .{ .id = value_id, .function = function_id, .type = if (index == 0) .boolean else .dynamic, .origin = .{ .instruction_result = .{ .instruction = a_instruction, .index = @intCast(index) } } };
    for (b_results, 0..) |value_id, index| values[22 + index] = .{ .id = value_id, .function = function_id, .type = if (index == 0) .boolean else .dynamic, .origin = .{ .instruction_result = .{ .instruction = b_instruction, .index = @intCast(index) } } };
    for (c_results, 0..) |value_id, index| values[26 + index] = .{ .id = value_id, .function = function_id, .type = if (index == 0) .boolean else .dynamic, .origin = .{ .instruction_result = .{ .instruction = c_instruction, .index = @intCast(index) } } };
    values[30] = .{ .id = prefix_value_a, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = prefix_constant_a, .index = 0 } } };
    values[31] = .{ .id = prefix_value_b, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = prefix_constant_b, .index = 0 } } };
    values[32] = .{ .id = reset_value, .function = function_id, .type = .{ .kind = .nil_value }, .origin = .{ .instruction_result = .{ .instruction = reset_constant, .index = 0 } } };

    const instructions = [_]ir.Instruction{
        .{ .id = false_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = a_instruction, .block = arm_a, .operation = .{ .numeric_for_next = .{ .control = a_parameters[0], .limit = a_parameters[1], .step = a_parameters[2], .initial = a_parameters[3], .mode = .semantic_normalized } }, .results = &a_results, .effects = .dynamic_call },
        .{ .id = b_instruction, .block = arm_b, .operation = .{ .numeric_for_next = .{ .control = b_parameters[0], .limit = b_parameters[1], .step = b_parameters[2], .initial = b_parameters[3], .mode = .semantic_normalized } }, .results = &b_results, .effects = .dynamic_call },
        .{ .id = c_instruction, .block = arm_c, .operation = .{ .numeric_for_next = .{ .control = c_parameters[0], .limit = c_parameters[1], .step = c_parameters[2], .initial = c_parameters[3], .mode = .semantic_normalized } }, .results = &c_results, .effects = .dynamic_call },
        .{ .id = prefix_constant_a, .block = prefix, .operation = .{ .constant = .{ .number = 23 } }, .results = &.{prefix_value_a}, .effects = .pure },
        .{ .id = prefix_write_a, .block = prefix, .operation = .{ .place_write = .{ .place = place_a, .value = prefix_value_a } }, .results = &.{}, .effects = .place_write },
        .{ .id = prefix_constant_b, .block = prefix, .operation = .{ .constant = .{ .number = 30 } }, .results = &.{prefix_value_b}, .effects = .pure },
        .{ .id = prefix_write_b, .block = prefix, .operation = .{ .place_write = .{ .place = place_b, .value = prefix_value_b } }, .results = &.{}, .effects = .place_write },
        .{ .id = reset_constant, .block = reset, .operation = .{ .constant = .{ .nil_value = {} } }, .results = &.{reset_value}, .effects = .pure },
        .{ .id = reset_write_a, .block = reset, .operation = .{ .place_write = .{ .place = place_a, .value = reset_value } }, .results = &.{}, .effects = .place_write },
        .{ .id = reset_write_b, .block = reset, .operation = .{ .place_write = .{ .place = place_b, .value = reset_value } }, .results = &.{}, .effects = .place_write },
    };
    const places = [_]ir.Place{
        .{ .id = place_a, .function = function_id, .type = .number, .origin = .{ .local = 0 } },
        .{ .id = place_b, .function = function_id, .type = .number, .origin = .{ .local = 1 } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ selector, control, limit, step, initial },
        .local_places = &.{ place_a, place_b },
        .blocks = &.{ entry, arm_a, arm_b, arm_c, prefix, reset, exit },
        .entry_block = entry,
    };
    const program = ir.Program{
        .program_id = "generic-multi-arm-tuple-continuation-witness",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };

    var initial_graph = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer initial_graph.deinit();
    var initial_regions = try irreducible_region.analyze(std.testing.allocator, &initial_graph);
    defer initial_regions.deinit();
    try std.testing.expect(initial_regions.regions.len != 0);

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const normalized = try irreducible_normalize.normalizeFunctionWithScratchInArena(
        arena.allocator(),
        arena.allocator(),
        &program,
        0,
    );
    try std.testing.expect(normalized.cloned_blocks != 0);
    try std.testing.expect(normalized.rewritten_edges != 0);

    var cloned_prefix_count: usize = 0;
    for (normalized.program.blocks) |block| {
        if (isEffectfulPrefix(&normalized.program, block)) cloned_prefix_count += 1;
    }
    try std.testing.expect(cloned_prefix_count >= 2);

    for (normalized.program.edge_rewrites) |rewrite| {
        if (rewrite.rule != .node_split) continue;
        try std.testing.expectEqual(rewrite.from.arguments.len, rewrite.to.arguments.len);
    }

    var normalized_graph = try cfg.Analysis.init(std.testing.allocator, &normalized.program, normalized.program.functions[0]);
    defer normalized_graph.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &normalized_graph);
    defer plan.deinit();
}

test "mixed external entries compose a parameterized numeric loop frontier" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const transition = ir.BlockId.fromIndex(2);
    const loop = ir.BlockId.fromIndex(3);
    const iteration = ir.BlockId.fromIndex(4);
    const body = ir.BlockId.fromIndex(5);
    const exit = ir.BlockId.fromIndex(6);

    const selector = ir.ValueId.fromIndex(0);
    const control = ir.ValueId.fromIndex(1);
    const limit = ir.ValueId.fromIndex(2);
    const step = ir.ValueId.fromIndex(3);
    const initial = ir.ValueId.fromIndex(4);
    const false_value = ir.ValueId.fromIndex(5);
    const loop_parameters = [_]ir.ValueId{
        ir.ValueId.fromIndex(6),
        ir.ValueId.fromIndex(7),
        ir.ValueId.fromIndex(8),
        ir.ValueId.fromIndex(9),
    };
    const transition_results = [_]ir.ValueId{
        ir.ValueId.fromIndex(10),
        ir.ValueId.fromIndex(11),
        ir.ValueId.fromIndex(12),
        ir.ValueId.fromIndex(13),
    };
    const iteration_parameters = [_]ir.ValueId{
        ir.ValueId.fromIndex(14),
        ir.ValueId.fromIndex(15),
        ir.ValueId.fromIndex(16),
        ir.ValueId.fromIndex(17),
    };
    const iteration_results = [_]ir.ValueId{
        ir.ValueId.fromIndex(18),
        ir.ValueId.fromIndex(19),
        ir.ValueId.fromIndex(20),
        ir.ValueId.fromIndex(21),
    };

    const false_instruction = ir.InstructionId.fromIndex(0);
    const transition_instruction = ir.InstructionId.fromIndex(1);
    const iteration_instruction = ir.InstructionId.fromIndex(2);
    const owner_arguments = [_]ir.ValueId{ control, limit, step, initial };
    const transition_arguments = [_]ir.ValueId{
        transition_results[3],
        transition_results[1],
        transition_results[2],
        false_value,
    };
    const iteration_arguments = [_]ir.ValueId{
        loop_parameters[0],
        loop_parameters[1],
        loop_parameters[2],
        loop_parameters[3],
    };
    const reentry_arguments = [_]ir.ValueId{
        iteration_results[3],
        iteration_results[1],
        iteration_results[2],
        false_value,
    };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{false_instruction}, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = transition },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{
            .target = loop,
            .arguments = owner_arguments[0..],
        } } },
        .{ .id = transition, .function = function_id, .instructions = &.{transition_instruction}, .terminator = .{ .branch = .{
            .condition = transition_results[0],
            .then_edge = .{ .target = loop, .arguments = transition_arguments[0..] },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = loop, .function = function_id, .parameters = loop_parameters[0..], .terminator = .{ .jump = .{
            .target = iteration,
            .arguments = iteration_arguments[0..],
        } } },
        .{ .id = iteration, .function = function_id, .parameters = iteration_parameters[0..], .instructions = &.{iteration_instruction}, .terminator = .{ .branch = .{
            .condition = iteration_results[0],
            .then_edge = .{ .target = body, .arguments = reentry_arguments[0..] },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{
            .target = loop,
            .arguments = reentry_arguments[0..],
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };

    var values: [22]ir.Value = undefined;
    values[0] = .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } };
    values[1] = .{ .id = control, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } };
    values[2] = .{ .id = limit, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } };
    values[3] = .{ .id = step, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 3 } };
    values[4] = .{ .id = initial, .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } };
    values[5] = .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_instruction, .index = 0 } } };
    for (loop_parameters, 0..) |value_id, index| values[6 + index] = .{
        .id = value_id,
        .function = function_id,
        .type = if (index == 3) .boolean else .dynamic,
        .origin = .{ .block_parameter = .{ .block = loop, .index = @intCast(index) } },
    };
    for (transition_results, 0..) |value_id, index| values[10 + index] = .{
        .id = value_id,
        .function = function_id,
        .type = if (index == 0) .boolean else .dynamic,
        .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = @intCast(index) } },
    };
    for (iteration_parameters, 0..) |value_id, index| values[14 + index] = .{
        .id = value_id,
        .function = function_id,
        .type = if (index == 3) .boolean else .dynamic,
        .origin = .{ .block_parameter = .{ .block = iteration, .index = @intCast(index) } },
    };
    for (iteration_results, 0..) |value_id, index| values[18 + index] = .{
        .id = value_id,
        .function = function_id,
        .type = if (index == 0) .boolean else .dynamic,
        .origin = .{ .instruction_result = .{ .instruction = iteration_instruction, .index = @intCast(index) } },
    };

    const instructions = [_]ir.Instruction{
        .{ .id = false_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = transition_instruction, .block = transition, .operation = .{ .numeric_for_next = .{
            .control = control,
            .limit = limit,
            .step = step,
            .initial = initial,
            .mode = .semantic_normalized,
        } }, .results = transition_results[0..], .effects = .dynamic_call },
        .{ .id = iteration_instruction, .block = iteration, .operation = .{ .numeric_for_next = .{
            .control = iteration_parameters[0],
            .limit = iteration_parameters[1],
            .step = iteration_parameters[2],
            .initial = iteration_parameters[3],
            .mode = .semantic_normalized,
        } }, .results = iteration_results[0..], .effects = .dynamic_call },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ selector, control, limit, step, initial },
        .blocks = &.{ entry, owner, transition, loop, iteration, body, exit },
        .entry_block = entry,
    };
    const program = ir.Program{
        .program_id = "mixed-external-parameterized-loop-frontier",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var initial_analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer initial_analysis.deinit();
    var replay_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay_context.deinit();
    const incoming = [_]ir.CfgEdgeRef{
        .{ .source = owner, .kind = .jump, .target = loop },
        .{ .source = transition, .kind = .branch_then, .target = loop },
    };
    var split = (try structural_overlap.findCollisionSplitAllocWithAnalysisAndReplayContext(
        std.testing.allocator,
        &program,
        &initial_analysis,
        0,
        loop,
        incoming[0..],
        &replay_context,
    )).?;
    defer split.deinit();
    try std.testing.expect(split.closure.len >= 3);
    try std.testing.expectEqual(@as(usize, 2), split.incoming.len);

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const normalized = try irreducible_normalize.normalizeFunctionWithScratchInArena(
        arena.allocator(),
        arena.allocator(),
        &program,
        0,
    );
    try std.testing.expect(normalized.cloned_blocks != 0);

    var normalized_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &normalized.program,
        normalized.program.functions[0],
    );
    defer normalized_analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &normalized_analysis);
    defer plan.deinit();
}

test "nested cloned target bridge replays only the authenticated owner suffix" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const root = ir.BlockId.fromIndex(1);
    const owner = ir.BlockId.fromIndex(2);
    const current = ir.BlockId.fromIndex(3);
    const target = ir.BlockId.fromIndex(4);
    const sibling_target = ir.BlockId.fromIndex(5);
    const nested_target = ir.BlockId.fromIndex(6);
    const exit = ir.BlockId.fromIndex(7);

    const selector = ir.ValueId.fromIndex(0);
    const seed = ir.ValueId.fromIndex(1);
    const root_value = ir.ValueId.fromIndex(2);
    const owner_value = ir.ValueId.fromIndex(3);
    const current_value = ir.ValueId.fromIndex(4);
    const target_value = ir.ValueId.fromIndex(5);
    const sibling_target_value = ir.ValueId.fromIndex(6);
    const nested_target_value = ir.ValueId.fromIndex(7);
    const exit_value = ir.ValueId.fromIndex(8);

    // The root/owner pair has sibling continuation targets from distinct
    // split groups.  The later owner/current suffix still reaches the nested
    // target with a replayable tuple.
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner, .arguments = &.{seed} },
            .else_edge = .{ .target = current, .arguments = &.{seed} },
        } } },
        .{ .id = root, .function = function_id, .parameters = &.{root_value}, .terminator = .{ .jump = .{
            .target = sibling_target,
            .arguments = &.{root_value},
        } } },
        .{ .id = owner, .function = function_id, .parameters = &.{owner_value}, .terminator = .{ .jump = .{
            .target = nested_target,
            .arguments = &.{owner_value},
        } } },
        .{ .id = current, .function = function_id, .parameters = &.{current_value}, .terminator = .{ .jump = .{
            .target = nested_target,
            .arguments = &.{current_value},
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{target_value}, .terminator = .{ .jump = .{
            .target = exit,
            .arguments = &.{target_value},
        } } },
        .{ .id = sibling_target, .function = function_id, .parameters = &.{sibling_target_value}, .terminator = .{ .jump = .{
            .target = exit,
            .arguments = &.{sibling_target_value},
        } } },
        .{ .id = nested_target, .function = function_id, .parameters = &.{nested_target_value}, .terminator = .{ .jump = .{
            .target = exit,
            .arguments = &.{nested_target_value},
        } } },
        .{ .id = exit, .function = function_id, .parameters = &.{exit_value}, .terminator = .{ .return_values = &.{exit_value} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, seed },
        .blocks = &.{ entry, root, owner, current, target, sibling_target, nested_target, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = seed, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = root_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = root, .index = 0 } } },
        .{ .id = owner_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = owner, .index = 0 } } },
        .{ .id = current_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = current, .index = 0 } } },
        .{ .id = target_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = sibling_target_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = sibling_target, .index = 0 } } },
        .{ .id = nested_target_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = nested_target, .index = 0 } } },
        .{ .id = exit_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = exit, .index = 0 } } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .branch_then,
            .from = .{ .target = root, .arguments = &.{seed} },
            .to = .{ .target = owner, .arguments = &.{seed} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = root,
            .kind = .jump,
            .from = .{ .target = target, .arguments = &.{root_value} },
            .to = .{ .target = sibling_target, .arguments = &.{root_value} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(1),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = owner,
            .kind = .jump,
            .from = .{ .target = target, .arguments = &.{owner_value} },
            .to = .{ .target = nested_target, .arguments = &.{owner_value} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(2),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(3),
            .source = entry,
            .kind = .branch_else,
            .from = .{ .target = owner, .arguments = &.{seed} },
            .to = .{ .target = current, .arguments = &.{seed} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(3),
        },
    };
    var program: ir.Program = .{
        .program_id = "nested-cloned-target-owner-suffix",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();

    const incoming = ir.CfgEdgeRef{ .source = current, .kind = .jump, .target = nested_target };
    var replay_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay_context.deinit();
    try std.testing.expect(try replay_context.hasAuthenticatedContinuationBridgeForEdge(&analysis, incoming));

    var tampered_blocks = blocks;
    tampered_blocks[current.index()].terminator = .{ .jump = .{
        .target = nested_target,
        .arguments = &.{seed},
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, functions[0]);
    defer tampered_analysis.deinit();
    var tampered_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &tampered_program,
        function_id,
    );
    defer tampered_context.deinit();
    try std.testing.expect(!try tampered_context.hasAuthenticatedContinuationBridgeForEdge(&tampered_analysis, incoming));

    var tampered_rewrites = rewrites;
    tampered_rewrites[1].to.target = nested_target;
    var tampered_lineage_program = program;
    tampered_lineage_program.edge_rewrites = &tampered_rewrites;
    var tampered_lineage_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &tampered_lineage_program,
        functions[0],
    );
    defer tampered_lineage_analysis.deinit();
    var tampered_lineage_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &tampered_lineage_program,
        function_id,
    );
    defer tampered_lineage_context.deinit();
    try std.testing.expect(!try tampered_lineage_context.hasAuthenticatedContinuationBridgeForEdge(&tampered_lineage_analysis, incoming));
}

test "effectful external prefix authenticates a four-slot loop reentry" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const prefix = ir.BlockId.fromIndex(2);
    const candidate = ir.BlockId.fromIndex(3);
    const target = ir.BlockId.fromIndex(4);
    const prefix_exit = ir.BlockId.fromIndex(5);
    const candidate_exit = ir.BlockId.fromIndex(6);
    const target_exit = ir.BlockId.fromIndex(7);

    const selector = ir.ValueId.fromIndex(0);
    const owner_control = ir.ValueId.fromIndex(1);
    const owner_limit = ir.ValueId.fromIndex(2);
    const owner_step = ir.ValueId.fromIndex(3);
    const owner_initial = ir.ValueId.fromIndex(4);
    const false_value = ir.ValueId.fromIndex(5);
    const prefix_read = ir.ValueId.fromIndex(6);
    const prefix_constant = ir.ValueId.fromIndex(7);
    const prefix_condition = ir.ValueId.fromIndex(8);
    const candidate_control = ir.ValueId.fromIndex(9);
    const candidate_limit = ir.ValueId.fromIndex(10);
    const candidate_step = ir.ValueId.fromIndex(11);
    const candidate_initial = ir.ValueId.fromIndex(12);
    const target_control = ir.ValueId.fromIndex(13);
    const target_limit = ir.ValueId.fromIndex(14);
    const target_step = ir.ValueId.fromIndex(15);
    const target_initial = ir.ValueId.fromIndex(16);
    const candidate_has = ir.ValueId.fromIndex(17);
    const candidate_result_limit = ir.ValueId.fromIndex(18);
    const candidate_result_step = ir.ValueId.fromIndex(19);
    const candidate_next = ir.ValueId.fromIndex(20);
    const target_has = ir.ValueId.fromIndex(21);
    const target_result_limit = ir.ValueId.fromIndex(22);
    const target_result_step = ir.ValueId.fromIndex(23);
    const target_next = ir.ValueId.fromIndex(24);

    const false_instruction = ir.InstructionId.fromIndex(0);
    const prefix_read_instruction = ir.InstructionId.fromIndex(1);
    const prefix_constant_instruction = ir.InstructionId.fromIndex(2);
    const prefix_compare_instruction = ir.InstructionId.fromIndex(3);
    const prefix_write_instruction = ir.InstructionId.fromIndex(4);
    const candidate_instruction = ir.InstructionId.fromIndex(5);
    const target_instruction = ir.InstructionId.fromIndex(6);
    const prefix_place = ir.PlaceId.fromIndex(0);
    const written_place = ir.PlaceId.fromIndex(1);

    const owner_tuple = [_]ir.ValueId{ owner_control, owner_limit, owner_step, owner_initial };
    const candidate_tuple = [_]ir.ValueId{ candidate_next, candidate_result_limit, candidate_result_step, false_value };
    const target_tuple = [_]ir.ValueId{ target_next, target_result_limit, target_result_step, false_value };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = prefix },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = owner_tuple[0..],
        } } },
        .{ .id = prefix, .function = function_id, .instructions = &.{
            prefix_read_instruction,
            prefix_constant_instruction,
            prefix_compare_instruction,
            prefix_write_instruction,
        }, .terminator = .{ .branch = .{
            .condition = prefix_condition,
            .then_edge = .{ .target = candidate, .arguments = owner_tuple[0..] },
            .else_edge = .{ .target = prefix_exit },
        } } },
        .{ .id = candidate, .function = function_id, .parameters = &.{
            candidate_control,
            candidate_limit,
            candidate_step,
            candidate_initial,
        }, .instructions = &.{candidate_instruction}, .terminator = .{ .branch = .{
            .condition = candidate_has,
            .then_edge = .{ .target = target, .arguments = candidate_tuple[0..] },
            .else_edge = .{ .target = candidate_exit },
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{
            target_control,
            target_limit,
            target_step,
            target_initial,
        }, .instructions = &.{target_instruction}, .terminator = .{ .branch = .{
            .condition = target_has,
            .then_edge = .{ .target = target, .arguments = target_tuple[0..] },
            .else_edge = .{ .target = target_exit },
        } } },
        .{ .id = prefix_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = candidate_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = target_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };

    var values: [25]ir.Value = undefined;
    values[0] = .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } };
    values[1] = .{ .id = owner_control, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } };
    values[2] = .{ .id = owner_limit, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } };
    values[3] = .{ .id = owner_step, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 3 } };
    values[4] = .{ .id = owner_initial, .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } };
    values[5] = .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_instruction, .index = 0 } } };
    values[6] = .{ .id = prefix_read, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = prefix_read_instruction, .index = 0 } } };
    values[7] = .{ .id = prefix_constant, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = prefix_constant_instruction, .index = 0 } } };
    values[8] = .{ .id = prefix_condition, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = prefix_compare_instruction, .index = 0 } } };
    for ([_]ir.ValueId{ candidate_control, candidate_limit, candidate_step, candidate_initial }, 0..) |value_id, index| values[value_id.index()] = .{
        .id = value_id,
        .function = function_id,
        .type = if (index == 3) .boolean else .dynamic,
        .origin = .{ .block_parameter = .{ .block = candidate, .index = @intCast(index) } },
    };
    for ([_]ir.ValueId{ target_control, target_limit, target_step, target_initial }, 0..) |value_id, index| values[value_id.index()] = .{
        .id = value_id,
        .function = function_id,
        .type = if (index == 3) .boolean else .dynamic,
        .origin = .{ .block_parameter = .{ .block = target, .index = @intCast(index) } },
    };
    for ([_]ir.ValueId{ candidate_has, candidate_result_limit, candidate_result_step, candidate_next }, 0..) |value_id, index| values[value_id.index()] = .{
        .id = value_id,
        .function = function_id,
        .type = if (index == 0) .boolean else .dynamic,
        .origin = .{ .instruction_result = .{ .instruction = candidate_instruction, .index = @intCast(index) } },
    };
    for ([_]ir.ValueId{ target_has, target_result_limit, target_result_step, target_next }, 0..) |value_id, index| values[value_id.index()] = .{
        .id = value_id,
        .function = function_id,
        .type = if (index == 0) .boolean else .dynamic,
        .origin = .{ .instruction_result = .{ .instruction = target_instruction, .index = @intCast(index) } },
    };

    const places = [_]ir.Place{
        .{ .id = prefix_place, .function = function_id, .type = .dynamic, .origin = .{ .local = 0 } },
        .{ .id = written_place, .function = function_id, .type = .dynamic, .origin = .{ .local = 1 } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = false_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = prefix_read_instruction, .block = prefix, .operation = .{ .place_read = prefix_place }, .results = &.{prefix_read}, .effects = .place_read },
        .{ .id = prefix_constant_instruction, .block = prefix, .operation = .{ .constant = .{ .number = 17 } }, .results = &.{prefix_constant}, .effects = .pure },
        .{ .id = prefix_compare_instruction, .block = prefix, .operation = .{ .binary = .{ .operator = .not_equal, .left = prefix_read, .right = prefix_constant, .mode = .semantic } }, .results = &.{prefix_condition}, .effects = .semantic_table_read },
        .{ .id = prefix_write_instruction, .block = prefix, .operation = .{ .place_write = .{ .place = written_place, .value = prefix_constant } }, .results = &.{}, .effects = .place_write },
        .{ .id = candidate_instruction, .block = candidate, .operation = .{ .numeric_for_next = .{ .control = candidate_control, .limit = candidate_limit, .step = candidate_step, .initial = candidate_initial, .mode = .semantic_normalized } }, .results = &.{ candidate_has, candidate_result_limit, candidate_result_step, candidate_next }, .effects = .numeric_for_next },
        .{ .id = target_instruction, .block = target, .operation = .{ .numeric_for_next = .{ .control = target_control, .limit = target_limit, .step = target_step, .initial = target_initial, .mode = .semantic_normalized } }, .results = &.{ target_has, target_result_limit, target_result_step, target_next }, .effects = .numeric_for_next },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ selector, owner_control, owner_limit, owner_step, owner_initial },
        .local_places = &.{ prefix_place, written_place },
        .blocks = &.{ entry, owner, prefix, candidate, target, prefix_exit, candidate_exit, target_exit },
        .entry_block = entry,
    };
    const program = ir.Program{
        .program_id = "effectful-parameterized-loop-reentry",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var replay_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay_context.deinit();
    const incoming = ir.CfgEdgeRef{ .source = candidate, .kind = .branch_then, .target = target };
    try std.testing.expect(try replay_context.hasAuthenticatedIterationContextualProjectionForEdge(
        &analysis,
        incoming,
        owner_tuple[0..],
    ));

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const normalized = try irreducible_normalize.normalizeFunctionWithScratchInArena(
        arena.allocator(),
        arena.allocator(),
        &program,
        0,
    );
    var normalized_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &normalized.program,
        normalized.program.functions[0],
    );
    defer normalized_analysis.deinit();
    var normalized_plan = try structure.Plan.init(std.testing.allocator, &normalized_analysis);
    defer normalized_plan.deinit();

    var tampered_blocks = blocks;
    tampered_blocks[candidate.index()].terminator = .{ .branch = .{
        .condition = candidate_has,
        .then_edge = .{ .target = target, .arguments = &.{ owner_control, candidate_result_limit, candidate_result_step, false_value } },
        .else_edge = .{ .target = candidate_exit },
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, function);
    defer tampered_analysis.deinit();
    var tampered_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &tampered_program,
        function_id,
    );
    defer tampered_context.deinit();
    try std.testing.expect(!try tampered_context.hasAuthenticatedIterationContextualProjectionForEdge(
        &tampered_analysis,
        incoming,
        owner_tuple[0..],
    ));

    var removed_reentry_blocks = blocks;
    removed_reentry_blocks[target.index()].terminator = .{ .branch = .{
        .condition = target_has,
        .then_edge = .{ .target = target_exit },
        .else_edge = .{ .target = target_exit },
    } };
    var removed_reentry_program = program;
    removed_reentry_program.blocks = &removed_reentry_blocks;
    var removed_reentry_analysis = try cfg.Analysis.init(std.testing.allocator, &removed_reentry_program, function);
    defer removed_reentry_analysis.deinit();
    var removed_reentry_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &removed_reentry_program,
        function_id,
    );
    defer removed_reentry_context.deinit();
    try std.testing.expect(!try removed_reentry_context.hasAuthenticatedIterationContextualProjectionForEdge(
        &removed_reentry_analysis,
        incoming,
        owner_tuple[0..],
    ));
}
