const std = @import("std");
const ir = @import("ir.zig");
const node_split = @import("node_split.zig");
const irreducible_normalize = @import("irreducible_normalize.zig");
const validation = @import("validate.zig");

test "numeric iteration transitions replay four exact protocol results" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const transition_id = ir.InstructionId.fromIndex(0);
    const control = ir.ValueId.fromIndex(0);
    const limit = ir.ValueId.fromIndex(1);
    const step = ir.ValueId.fromIndex(2);
    const initial = ir.ValueId.fromIndex(3);
    const has_value = ir.ValueId.fromIndex(4);
    const normalized_limit = ir.ValueId.fromIndex(5);
    const normalized_step = ir.ValueId.fromIndex(6);
    const next_control = ir.ValueId.fromIndex(7);
    const base_values = [_]ir.Value{
        .{ .id = control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = source_id, .index = 1 } } },
        .{ .id = step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = source_id, .index = 2 } } },
        .{ .id = initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = source_id, .index = 3 } } },
        .{ .id = has_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 3 } } },
    };
    const base_instructions = [_]ir.Instruction{.{
        .id = transition_id,
        .block = source_id,
        .operation = .{ .numeric_for_next = .{
            .control = control,
            .limit = limit,
            .step = step,
            .initial = initial,
        } },
        .results = &.{ has_value, normalized_limit, normalized_step, next_control },
        .effects = .numeric_for_next,
    }};
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{ control, limit, step, initial },
        .instructions = &.{transition_id},
        .terminator = .{ .return_values = &.{ has_value, normalized_limit, normalized_step, next_control } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{source_id},
        .entry_block = source_id,
    }};
    var source_program: ir.Program = .{
        .program_id = "numeric-iteration-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&source_program, source));

    var changed_instructions = base_instructions;
    changed_instructions[0].operation.numeric_for_next.control = has_value;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[0].effects = .pure;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[0].pack_result = ir.ValuePackId.fromIndex(0);
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.instructions = &base_instructions;
    var changed_values = base_values;
    changed_values[initial.index()].type = .number;
    source_program.values = &changed_values;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_values = base_values;
    changed_values[has_value.index()].type = .dynamic;
    source_program.values = &changed_values;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.values = &base_values;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var values: std.ArrayList(ir.Value) = .empty;
    try values.appendSlice(allocator, &base_values);
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    var instructions: std.ArrayList(ir.Instruction) = .empty;
    try instructions.appendSlice(allocator, &base_instructions);
    const cloned = try node_split.cloneBlockInArena(
        allocator,
        &source_program,
        &instructions,
        &values,
        &packs,
        source,
        clone_id,
    );
    try std.testing.expectEqual(@as(usize, 8), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 0), cloned.cloned_packs);
    try std.testing.expectEqual(@as(usize, 1), cloned.cloned_instructions);

    const clone_control = ir.ValueId.fromIndex(8);
    const clone_limit = ir.ValueId.fromIndex(9);
    const clone_step = ir.ValueId.fromIndex(10);
    const clone_initial = ir.ValueId.fromIndex(11);
    const clone_has = ir.ValueId.fromIndex(12);
    const clone_normalized_limit = ir.ValueId.fromIndex(13);
    const clone_normalized_step = ir.ValueId.fromIndex(14);
    const clone_next_control = ir.ValueId.fromIndex(15);
    const clone_transition = ir.InstructionId.fromIndex(1);
    const cloned_operation = instructions.items[clone_transition.index()].operation.numeric_for_next;
    try std.testing.expectEqual(clone_control, cloned_operation.control);
    try std.testing.expectEqual(clone_limit, cloned_operation.limit);
    try std.testing.expectEqual(clone_step, cloned_operation.step);
    try std.testing.expectEqual(clone_initial, cloned_operation.initial);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_has, clone_normalized_limit, clone_normalized_step, clone_next_control },
        instructions.items[clone_transition.index()].results,
    );
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_has, clone_normalized_limit, clone_normalized_step, clone_next_control },
        cloned.block.terminator.return_values,
    );
    for (instructions.items[clone_transition.index()].results, 0..) |result_id, index| {
        const origin = values.items[result_id.index()].origin.instruction_result;
        try std.testing.expectEqual(clone_transition, origin.instruction);
        try std.testing.expectEqual(index, origin.index);
    }

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{ control, limit, step, initial } };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_transition = instructions.items[clone_transition.index()];
    instructions.items[clone_transition.index()].operation.numeric_for_next.limit = limit;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_transition.index()] = saved_transition;

    instructions.items[clone_transition.index()].effects = .pure;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_transition.index()] = saved_transition;

    values.items[clone_normalized_step.index()].type = .dynamic;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}

test "generic iteration transitions preserve variable arity and mapped state" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const transition_id = ir.InstructionId.fromIndex(0);
    const iterator = ir.ValueId.fromIndex(0);
    const state = ir.ValueId.fromIndex(1);
    const control = ir.ValueId.fromIndex(2);
    const initial = ir.ValueId.fromIndex(3);
    const has_value = ir.ValueId.fromIndex(4);
    const prepared_iterator = ir.ValueId.fromIndex(5);
    const prepared_state = ir.ValueId.fromIndex(6);
    const first = ir.ValueId.fromIndex(7);
    const second = ir.ValueId.fromIndex(8);
    const base_values = [_]ir.Value{
        .{ .id = iterator, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = state, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = source_id, .index = 1 } } },
        .{ .id = control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = source_id, .index = 2 } } },
        .{ .id = initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = source_id, .index = 3 } } },
        .{ .id = has_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 0 } } },
        .{ .id = prepared_iterator, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 1 } } },
        .{ .id = prepared_state, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 2 } } },
        .{ .id = first, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 3 } } },
        .{ .id = second, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 4 } } },
    };
    const base_instructions = [_]ir.Instruction{.{
        .id = transition_id,
        .block = source_id,
        .operation = .{ .generic_for_next = .{
            .iterator = iterator,
            .state = state,
            .control = control,
            .initial = initial,
            .variable_count = 2,
        } },
        .results = &.{ has_value, prepared_iterator, prepared_state, first, second },
        .effects = .generic_for_next,
    }};
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{ iterator, state, control, initial },
        .instructions = &.{transition_id},
        .terminator = .{ .return_values = &.{ has_value, prepared_iterator, prepared_state, first, second } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{source_id},
        .entry_block = source_id,
    }};
    var source_program: ir.Program = .{
        .program_id = "generic-iteration-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&source_program, source));

    var changed_instructions = base_instructions;
    changed_instructions[0].operation.generic_for_next.variable_count = 0;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[0].operation.generic_for_next.variable_count = 1;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[0].operation.generic_for_next.iterator = has_value;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[0].effects = .numeric_for_next;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.instructions = &base_instructions;
    var changed_values = base_values;
    changed_values[initial.index()].type = .number;
    source_program.values = &changed_values;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_values = base_values;
    changed_values[has_value.index()].type = .dynamic;
    source_program.values = &changed_values;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.values = &base_values;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var values: std.ArrayList(ir.Value) = .empty;
    try values.appendSlice(allocator, &base_values);
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    var instructions: std.ArrayList(ir.Instruction) = .empty;
    try instructions.appendSlice(allocator, &base_instructions);
    const cloned = try node_split.cloneBlockInArena(
        allocator,
        &source_program,
        &instructions,
        &values,
        &packs,
        source,
        clone_id,
    );
    try std.testing.expectEqual(@as(usize, 9), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 0), cloned.cloned_packs);
    try std.testing.expectEqual(@as(usize, 1), cloned.cloned_instructions);

    const clone_iterator = ir.ValueId.fromIndex(9);
    const clone_state = ir.ValueId.fromIndex(10);
    const clone_control = ir.ValueId.fromIndex(11);
    const clone_initial = ir.ValueId.fromIndex(12);
    const clone_has = ir.ValueId.fromIndex(13);
    const clone_prepared_iterator = ir.ValueId.fromIndex(14);
    const clone_prepared_state = ir.ValueId.fromIndex(15);
    const clone_first = ir.ValueId.fromIndex(16);
    const clone_second = ir.ValueId.fromIndex(17);
    const clone_transition = ir.InstructionId.fromIndex(1);
    const cloned_operation = instructions.items[clone_transition.index()].operation.generic_for_next;
    try std.testing.expectEqual(clone_iterator, cloned_operation.iterator);
    try std.testing.expectEqual(clone_state, cloned_operation.state);
    try std.testing.expectEqual(clone_control, cloned_operation.control);
    try std.testing.expectEqual(clone_initial, cloned_operation.initial);
    try std.testing.expectEqual(@as(u16, 2), cloned_operation.variable_count);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_has, clone_prepared_iterator, clone_prepared_state, clone_first, clone_second },
        instructions.items[clone_transition.index()].results,
    );
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_has, clone_prepared_iterator, clone_prepared_state, clone_first, clone_second },
        cloned.block.terminator.return_values,
    );

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{ iterator, state, control, initial } };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_transition = instructions.items[clone_transition.index()];
    instructions.items[clone_transition.index()].operation.generic_for_next.variable_count = 1;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_transition.index()] = saved_transition;

    instructions.items[clone_transition.index()].operation.generic_for_next.control = control;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_transition.index()] = saved_transition;

    instructions.items[clone_transition.index()].effects = .numeric_for_next;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_transition.index()] = saved_transition;

    values.items[clone_has.index()].type = .dynamic;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}

test "irreducible iteration transitions normalize for core while readable admission stays explicit" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const primary = ir.BlockId.fromIndex(1);
    const secondary = ir.BlockId.fromIndex(2);
    const numeric_id = ir.InstructionId.fromIndex(0);
    const generic_id = ir.InstructionId.fromIndex(1);
    const selector = ir.ValueId.fromIndex(0);
    const numeric_control = ir.ValueId.fromIndex(1);
    const numeric_limit = ir.ValueId.fromIndex(2);
    const numeric_step = ir.ValueId.fromIndex(3);
    const numeric_initial = ir.ValueId.fromIndex(4);
    const iterator = ir.ValueId.fromIndex(5);
    const state = ir.ValueId.fromIndex(6);
    const generic_control = ir.ValueId.fromIndex(7);
    const generic_initial = ir.ValueId.fromIndex(8);
    const secondary_numeric_control = ir.ValueId.fromIndex(9);
    const secondary_numeric_limit = ir.ValueId.fromIndex(10);
    const secondary_numeric_step = ir.ValueId.fromIndex(11);
    const secondary_numeric_initial = ir.ValueId.fromIndex(12);
    const secondary_iterator = ir.ValueId.fromIndex(13);
    const secondary_state = ir.ValueId.fromIndex(14);
    const secondary_generic_control = ir.ValueId.fromIndex(15);
    const secondary_generic_initial = ir.ValueId.fromIndex(16);
    const numeric_has = ir.ValueId.fromIndex(17);
    const normalized_limit = ir.ValueId.fromIndex(18);
    const normalized_step = ir.ValueId.fromIndex(19);
    const next_numeric_control = ir.ValueId.fromIndex(20);
    const generic_has = ir.ValueId.fromIndex(21);
    const prepared_iterator = ir.ValueId.fromIndex(22);
    const prepared_state = ir.ValueId.fromIndex(23);
    const first_variable = ir.ValueId.fromIndex(24);
    const second_variable = ir.ValueId.fromIndex(25);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const edge_arguments = [_]ir.ValueId{
        numeric_control,
        numeric_limit,
        numeric_step,
        numeric_initial,
        iterator,
        state,
        generic_control,
        generic_initial,
    };
    const secondary_parameters = [_]ir.ValueId{
        secondary_numeric_control,
        secondary_numeric_limit,
        secondary_numeric_step,
        secondary_numeric_initial,
        secondary_iterator,
        secondary_state,
        secondary_generic_control,
        secondary_generic_initial,
    };
    const blocks = [_]ir.Block{
        .{
            .id = entry,
            .function = function_id,
            .terminator = .{ .branch = .{
                .condition = selector,
                .then_edge = .{ .target = primary },
                .else_edge = .{ .target = secondary, .arguments = &edge_arguments },
            } },
            .evidence = &.{evidence_id},
        },
        .{
            .id = primary,
            .function = function_id,
            .terminator = .{ .jump = .{ .target = secondary, .arguments = &edge_arguments } },
            .evidence = &.{evidence_id},
        },
        .{
            .id = secondary,
            .function = function_id,
            .parameters = &secondary_parameters,
            .instructions = &.{ numeric_id, generic_id },
            .terminator = .{ .jump = .{ .target = primary } },
            .evidence = &.{evidence_id},
        },
    };
    const function_parameters = [_]ir.ValueId{
        selector,
        numeric_control,
        numeric_limit,
        numeric_step,
        numeric_initial,
        iterator,
        state,
        generic_control,
        generic_initial,
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &function_parameters,
        .blocks = &.{ entry, primary, secondary },
        .entry_block = entry,
        .evidence = &.{evidence_id},
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = numeric_control, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = numeric_limit, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } },
        .{ .id = numeric_step, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 3 } },
        .{ .id = numeric_initial, .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } },
        .{ .id = iterator, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 5 } },
        .{ .id = state, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 6 } },
        .{ .id = generic_control, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 7 } },
        .{ .id = generic_initial, .function = function_id, .type = .boolean, .origin = .{ .parameter = 8 } },
        .{ .id = secondary_numeric_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = secondary, .index = 0 } } },
        .{ .id = secondary_numeric_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = secondary, .index = 1 } } },
        .{ .id = secondary_numeric_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = secondary, .index = 2 } } },
        .{ .id = secondary_numeric_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = secondary, .index = 3 } } },
        .{ .id = secondary_iterator, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = secondary, .index = 4 } } },
        .{ .id = secondary_state, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = secondary, .index = 5 } } },
        .{ .id = secondary_generic_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = secondary, .index = 6 } } },
        .{ .id = secondary_generic_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = secondary, .index = 7 } } },
        .{ .id = numeric_has, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = numeric_id, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = numeric_id, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = numeric_id, .index = 2 } } },
        .{ .id = next_numeric_control, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = numeric_id, .index = 3 } } },
        .{ .id = generic_has, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = generic_id, .index = 0 } } },
        .{ .id = prepared_iterator, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = generic_id, .index = 1 } } },
        .{ .id = prepared_state, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = generic_id, .index = 2 } } },
        .{ .id = first_variable, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = generic_id, .index = 3 } } },
        .{ .id = second_variable, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = generic_id, .index = 4 } } },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = numeric_id,
            .block = secondary,
            .operation = .{ .numeric_for_next = .{
                .control = secondary_numeric_control,
                .limit = secondary_numeric_limit,
                .step = secondary_numeric_step,
                .initial = secondary_numeric_initial,
            } },
            .results = &.{ numeric_has, normalized_limit, normalized_step, next_numeric_control },
            .effects = .numeric_for_next,
            .evidence = &.{evidence_id},
        },
        .{
            .id = generic_id,
            .block = secondary,
            .operation = .{ .generic_for_next = .{
                .iterator = secondary_iterator,
                .state = secondary_state,
                .control = secondary_generic_control,
                .initial = secondary_generic_initial,
                .variable_count = 2,
            } },
            .results = &.{ generic_has, prepared_iterator, prepared_state, first_variable, second_variable },
            .effects = .generic_for_next,
            .evidence = &.{evidence_id},
        },
    };
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .dynamic_fixture,
        .locator = "fixture:irreducible-iteration-node-split",
    }};
    const program: ir.Program = .{
        .program_id = "irreducible-iteration-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    var source_report = try validation.validate(std.testing.allocator, &program, .core);
    defer source_report.deinit();
    try std.testing.expect(source_report.isClean());

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const normalized = try irreducible_normalize.normalizeInArena(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 1), normalized.cloned_blocks);
    try std.testing.expectEqual(@as(usize, 17), normalized.cloned_values);
    try std.testing.expectEqual(@as(usize, 2), normalized.cloned_instructions);
    try std.testing.expectEqual(@as(usize, 1), normalized.rewritten_edges);
    try std.testing.expectEqual(ir.EdgeRewriteRule.node_split, normalized.program.edge_rewrites[0].rule);

    var core_report = try validation.validate(std.testing.allocator, &normalized.program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try validation.validate(std.testing.allocator, &normalized.program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.contains(.unsupported_readable_iteration_protocol));

    const rerun = try irreducible_normalize.normalizeInArena(arena.allocator(), &normalized.program);
    try std.testing.expectEqual(@as(usize, 0), rerun.cloned_blocks);
    try std.testing.expectEqual(normalized.program.blocks.len, rerun.program.blocks.len);
    try std.testing.expectEqual(normalized.program.instructions.len, rerun.program.instructions.len);
    try std.testing.expectEqual(normalized.program.edge_rewrites.len, rerun.program.edge_rewrites.len);
}
