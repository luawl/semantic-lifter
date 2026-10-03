const std = @import("std");
const ir = @import("ir.zig");
const node_split = @import("node_split.zig");

test "parameterized replay binds the complete clone mapping" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const exit_id = ir.BlockId.fromIndex(2);
    const source_parameter = ir.ValueId.fromIndex(0);
    const clone_parameter = ir.ValueId.fromIndex(1);
    const incoming_value = ir.ValueId.fromIndex(2);
    const condition = ir.ValueId.fromIndex(3);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const base_blocks = [_]ir.Block{
        .{
            .id = source_id,
            .function = function_id,
            .name_hint = "mapped_entry",
            .parameters = &.{source_parameter},
            .terminator = .{ .branch = .{
                .condition = condition,
                .then_edge = .{ .target = source_id, .arguments = &.{source_parameter} },
                .else_edge = .{ .target = exit_id, .arguments = &.{source_parameter} },
            } },
            .evidence = &.{evidence_id},
        },
        .{
            .id = clone_id,
            .function = function_id,
            .name_hint = "mapped_entry",
            .parameters = &.{clone_parameter},
            .terminator = .{ .branch = .{
                .condition = condition,
                .then_edge = .{ .target = clone_id, .arguments = &.{clone_parameter} },
                .else_edge = .{ .target = exit_id, .arguments = &.{clone_parameter} },
            } },
            .evidence = &.{evidence_id},
        },
        .{ .id = exit_id, .function = function_id, .terminator = .{ .return_values = &.{} }, .evidence = &.{evidence_id} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ incoming_value, condition },
        .blocks = &.{ source_id, clone_id, exit_id },
        .entry_block = source_id,
        .evidence = &.{evidence_id},
    }};
    const base_values = [_]ir.Value{
        .{ .id = source_parameter, .function = function_id, .type = .integer, .name_hint = "mapped_value", .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = clone_parameter, .function = function_id, .type = .integer, .name_hint = "mapped_value", .origin = .{ .block_parameter = .{ .block = clone_id, .index = 0 } } },
        .{ .id = incoming_value, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
    };
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .structural_derivation, .locator = "fixture:parameterized-node-split-replay" }};
    var program: ir.Program = .{
        .program_id = "parameterized-node-split-replay",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &base_blocks,
        .instructions = &.{},
        .values = &base_values,
        .evidence = &evidence,
    };
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{incoming_value} };
    const replayed = (try node_split.replayAlloc(std.testing.allocator, &program, incoming, clone_id)).?;
    defer std.testing.allocator.free(replayed.arguments);
    try std.testing.expectEqual(clone_id, replayed.target);
    try std.testing.expectEqualSlices(ir.ValueId, &.{incoming_value}, replayed.arguments);

    var changed_values = base_values;
    changed_values[clone_parameter.index()].type = .number;
    program.values = &changed_values;
    try std.testing.expect(try node_split.replayAlloc(std.testing.allocator, &program, incoming, clone_id) == null);

    changed_values = base_values;
    changed_values[clone_parameter.index()].name_hint = "changed";
    program.values = &changed_values;
    try std.testing.expect(try node_split.replayAlloc(std.testing.allocator, &program, incoming, clone_id) == null);

    changed_values = base_values;
    changed_values[clone_parameter.index()].origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } };
    program.values = &changed_values;
    try std.testing.expect(try node_split.replayAlloc(std.testing.allocator, &program, incoming, clone_id) == null);

    program.values = &base_values;
    var changed_blocks = base_blocks;
    changed_blocks[clone_id.index()].terminator.branch.else_edge.arguments = &.{source_parameter};
    program.blocks = &changed_blocks;
    try std.testing.expect(try node_split.replayAlloc(std.testing.allocator, &program, incoming, clone_id) == null);

    changed_blocks = base_blocks;
    changed_blocks[clone_id.index()].terminator.branch.then_edge.target = source_id;
    program.blocks = &changed_blocks;
    try std.testing.expect(try node_split.replayAlloc(std.testing.allocator, &program, incoming, clone_id) == null);

    changed_blocks = base_blocks;
    changed_blocks[clone_id.index()].evidence = &.{};
    program.blocks = &changed_blocks;
    try std.testing.expect(try node_split.replayAlloc(std.testing.allocator, &program, incoming, clone_id) == null);

    program.blocks = &base_blocks;
    try std.testing.expect(try node_split.replayAlloc(std.testing.allocator, &program, .{ .target = source_id }, clone_id) == null);
}

test "grouped replay isolates sibling clone batches with shared source blocks" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source_a = ir.BlockId.fromIndex(1);
    const source_b = ir.BlockId.fromIndex(2);
    const source_c = ir.BlockId.fromIndex(3);
    const clone_a = ir.BlockId.fromIndex(4);
    const clone_b_first = ir.BlockId.fromIndex(5);
    const clone_c = ir.BlockId.fromIndex(6);
    const clone_b_second = ir.BlockId.fromIndex(7);
    const clone_a_second = ir.BlockId.fromIndex(8);
    const source_b_parameter = ir.ValueId.fromIndex(0);
    const clone_b_first_parameter = ir.ValueId.fromIndex(1);
    const clone_b_second_parameter = ir.ValueId.fromIndex(2);
    const condition = ir.ValueId.fromIndex(3);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const first_group = ir.NodeSplitGroupId.fromIndex(0);
    const second_group = ir.NodeSplitGroupId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = clone_a } }, .evidence = &.{evidence_id} },
        .{ .id = source_a, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = source_b, .arguments = &.{condition} },
            .else_edge = .{ .target = clone_c },
        } }, .evidence = &.{evidence_id} },
        .{ .id = source_b, .function = function_id, .parameters = &.{source_b_parameter}, .terminator = .{ .return_values = &.{source_b_parameter} }, .evidence = &.{evidence_id} },
        .{ .id = source_c, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = source_b, .arguments = &.{condition} },
            .else_edge = .{ .target = source_a },
        } }, .evidence = &.{evidence_id} },
        .{ .id = clone_a, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = clone_b_first, .arguments = &.{condition} },
            .else_edge = .{ .target = clone_c },
        } }, .evidence = &.{evidence_id} },
        .{ .id = clone_b_first, .function = function_id, .parameters = &.{clone_b_first_parameter}, .terminator = .{ .return_values = &.{clone_b_first_parameter} }, .evidence = &.{evidence_id} },
        .{ .id = clone_c, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = clone_b_second, .arguments = &.{condition} },
            .else_edge = .{ .target = clone_a_second },
        } }, .evidence = &.{evidence_id} },
        .{ .id = clone_b_second, .function = function_id, .parameters = &.{clone_b_second_parameter}, .terminator = .{ .return_values = &.{clone_b_second_parameter} }, .evidence = &.{evidence_id} },
        .{ .id = clone_a_second, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = clone_b_second, .arguments = &.{condition} },
            .else_edge = .{ .target = clone_c },
        } }, .evidence = &.{evidence_id} },
    };
    const values = [_]ir.Value{
        .{ .id = source_b_parameter, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = source_b, .index = 0 } } },
        .{ .id = clone_b_first_parameter, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = clone_b_first, .index = 0 } } },
        .{ .id = clone_b_second_parameter, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = clone_b_second, .index = 0 } } },
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, source_a, source_b, source_c, clone_a, clone_b_first, clone_c, clone_b_second, clone_a_second },
        .entry_block = entry,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .structural_derivation, .locator = "fixture:grouped-node-split-replay" }};
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{ .id = ir.EdgeRewriteId.fromIndex(0), .source = clone_a, .kind = .branch_then, .from = .{ .target = source_b, .arguments = &.{condition} }, .to = .{ .target = clone_b_first, .arguments = &.{condition} }, .rule = .node_split, .node_split_group = first_group },
        .{ .id = ir.EdgeRewriteId.fromIndex(1), .source = entry, .kind = .jump, .from = .{ .target = source_a }, .to = .{ .target = clone_a }, .rule = .node_split, .node_split_group = first_group },
        .{ .id = ir.EdgeRewriteId.fromIndex(2), .source = clone_c, .kind = .branch_then, .from = .{ .target = source_b, .arguments = &.{condition} }, .to = .{ .target = clone_b_second, .arguments = &.{condition} }, .rule = .node_split, .node_split_group = second_group },
        .{ .id = ir.EdgeRewriteId.fromIndex(3), .source = clone_c, .kind = .branch_else, .from = .{ .target = source_a }, .to = .{ .target = clone_a_second }, .rule = .node_split, .node_split_group = second_group },
        .{ .id = ir.EdgeRewriteId.fromIndex(4), .source = clone_a_second, .kind = .branch_then, .from = .{ .target = source_b, .arguments = &.{condition} }, .to = .{ .target = clone_b_second, .arguments = &.{condition} }, .rule = .node_split, .node_split_group = second_group },
        .{ .id = ir.EdgeRewriteId.fromIndex(5), .source = clone_a_second, .kind = .branch_else, .from = .{ .target = source_c }, .to = .{ .target = clone_c }, .rule = .node_split, .node_split_group = second_group },
        .{ .id = ir.EdgeRewriteId.fromIndex(6), .source = clone_a, .kind = .branch_else, .from = .{ .target = source_c }, .to = .{ .target = clone_c }, .rule = .node_split, .node_split_group = second_group },
        .{ .id = ir.EdgeRewriteId.fromIndex(7), .source = source_a, .kind = .branch_else, .from = .{ .target = source_c }, .to = .{ .target = clone_c }, .rule = .node_split, .node_split_group = second_group },
    };
    const program: ir.Program = .{
        .program_id = "grouped-node-split-replay",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
        .edge_rewrites = &rewrites,
    };

    try std.testing.expect(try node_split.replayAllocForGroup(std.testing.allocator, &program, .{ .target = source_a }, clone_a, first_group) != null);
    try std.testing.expect(try node_split.replayAllocForGroup(std.testing.allocator, &program, .{ .target = source_c }, clone_c, second_group) != null);
    try std.testing.expect(try node_split.replayAllocForGroup(std.testing.allocator, &program, .{ .target = source_a }, clone_a, second_group) == null);
    try std.testing.expect(try node_split.replayAlloc(std.testing.allocator, &program, .{ .target = source_a }, clone_a) != null);
}

test "dynamic error levels remap and bind node split replay" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const incoming_value = ir.ValueId.fromIndex(0);
    const message = ir.ValueId.fromIndex(1);
    const source_level = ir.ValueId.fromIndex(2);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{source_level},
        .terminator = .{ .throw_error = .{
            .value = message,
            .level = 0,
            .dynamic_level = source_level,
        } },
        .evidence = &.{evidence_id},
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ incoming_value, message },
        .blocks = &.{source_id},
        .entry_block = source_id,
        .evidence = &.{evidence_id},
    }};
    const initial_values = [_]ir.Value{
        .{ .id = incoming_value, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = message, .function = function_id, .type = .string, .origin = .{ .parameter = 1 } },
        .{ .id = source_level, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
    };
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .structural_derivation, .locator = "fixture:dynamic-error-level-node-split" }};
    var source_program: ir.Program = .{
        .program_id = "dynamic-error-level-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &.{},
        .values = &initial_values,
        .evidence = &evidence,
    };
    var instructions: std.ArrayList(ir.Instruction) = .empty;
    var values: std.ArrayList(ir.Value) = .empty;
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    try values.appendSlice(allocator, &initial_values);

    const cloned = try node_split.cloneBlockInArena(
        allocator,
        &source_program,
        &instructions,
        &values,
        &packs,
        source,
        clone_id,
    );
    const clone_level = cloned.block.parameters[0];
    try std.testing.expectEqual(message, cloned.block.terminator.throw_error.value);
    try std.testing.expectEqual(clone_level, cloned.block.terminator.throw_error.dynamic_level.?);

    const blocks = [_]ir.Block{ source, cloned.block };
    var replay_functions = functions;
    replay_functions[0].blocks = &.{ source_id, clone_id };
    source_program.functions = &replay_functions;
    source_program.blocks = &blocks;
    source_program.instructions = instructions.items;
    source_program.values = values.items;
    source_program.value_packs = packs.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{incoming_value} };
    const replayed = (try node_split.replayAlloc(allocator, &source_program, incoming, clone_id)).?;
    try std.testing.expectEqual(clone_id, replayed.target);
    try std.testing.expectEqualSlices(ir.ValueId, incoming.arguments, replayed.arguments);

    var changed_blocks = blocks;
    changed_blocks[clone_id.index()].terminator.throw_error.dynamic_level = source_level;
    source_program.blocks = &changed_blocks;
    try std.testing.expect(try node_split.replayAlloc(allocator, &source_program, incoming, clone_id) == null);
}

test "pure instruction cloning and replay bind fresh dependent identities" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const incoming_value = ir.ValueId.fromIndex(0);
    const source_parameter = ir.ValueId.fromIndex(1);
    const first_result = ir.ValueId.fromIndex(2);
    const second_result = ir.ValueId.fromIndex(3);
    const first_instruction = ir.InstructionId.fromIndex(0);
    const second_instruction = ir.InstructionId.fromIndex(1);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const source = ir.Block{
        .id = source_id,
        .function = function_id,
        .name_hint = "pure_entry",
        .parameters = &.{source_parameter},
        .instructions = &.{ first_instruction, second_instruction },
        .terminator = .{ .return_values = &.{second_result} },
        .evidence = &.{evidence_id},
    };
    const base_values = [_]ir.Value{
        .{ .id = incoming_value, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = source_parameter, .function = function_id, .type = .integer, .name_hint = "input", .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = first_result, .function = function_id, .type = .integer, .name_hint = "first", .origin = .{ .instruction_result = .{ .instruction = first_instruction, .index = 0 } } },
        .{ .id = second_result, .function = function_id, .type = .integer, .name_hint = "second", .origin = .{ .instruction_result = .{ .instruction = second_instruction, .index = 0 } } },
    };
    const base_instructions = [_]ir.Instruction{
        .{
            .id = first_instruction,
            .block = source_id,
            .operation = .{ .copy = source_parameter },
            .results = &.{first_result},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
        .{
            .id = second_instruction,
            .block = source_id,
            .operation = .{ .unary = .{ .operator = .negate, .operand = first_result } },
            .results = &.{second_result},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{incoming_value},
        .blocks = &.{source_id},
        .entry_block = source_id,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .structural_derivation, .locator = "fixture:pure-node-split-replay" }};
    const source_program: ir.Program = .{
        .program_id = "pure-node-split-replay",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
        .evidence = &evidence,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&source_program, source));
    var dynamic_instructions = base_instructions;
    dynamic_instructions[second_instruction.index()].operation.unary.operand = incoming_value;
    var dynamic_values = base_values;
    dynamic_values[incoming_value.index()].type = .dynamic;
    var dynamic_program = source_program;
    dynamic_program.instructions = &dynamic_instructions;
    dynamic_program.values = &dynamic_values;
    try std.testing.expect(!node_split.instructionsAreCloneable(&dynamic_program, source));

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var values: std.ArrayList(ir.Value) = .empty;
    try values.appendSlice(allocator, &base_values);
    var instructions: std.ArrayList(ir.Instruction) = .empty;
    try instructions.appendSlice(allocator, &base_instructions);
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    try packs.appendSlice(allocator, source_program.value_packs);
    const cloned = try node_split.cloneBlockInArena(allocator, &source_program, &instructions, &values, &packs, source, clone_id);
    try std.testing.expectEqual(@as(usize, 3), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_instructions);
    try std.testing.expectEqualSlices(ir.InstructionId, &.{ ir.InstructionId.fromIndex(2), ir.InstructionId.fromIndex(3) }, cloned.block.instructions);
    try std.testing.expectEqual(ir.ValueId.fromIndex(4), instructions.items[2].operation.copy);
    try std.testing.expectEqual(ir.ValueId.fromIndex(5), instructions.items[3].operation.unary.operand);
    try std.testing.expectEqual(ir.OperatorMode.semantic, instructions.items[3].operation.unary.mode);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ir.ValueId.fromIndex(6)}, cloned.block.terminator.return_values);
    try std.testing.expectEqual(ir.InstructionId.fromIndex(3), values.items[6].origin.instruction_result.instruction);

    var blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{incoming_value} };
    const replayed = (try node_split.replayAlloc(allocator, &program, incoming, clone_id)).?;
    try std.testing.expectEqual(clone_id, replayed.target);
    try std.testing.expectEqualSlices(ir.ValueId, incoming.arguments, replayed.arguments);

    const later_terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = second_result } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .value = ir.ValueId.fromIndex(6) } },
    };
    program.solver_terms = &later_terms;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);
    program.solver_terms = &.{};

    const clone_first_instruction = ir.InstructionId.fromIndex(2);
    const clone_second_instruction = ir.InstructionId.fromIndex(3);
    const clone_first_result = ir.ValueId.fromIndex(5);
    const clone_second_result = ir.ValueId.fromIndex(6);
    const saved_first = instructions.items[clone_first_instruction.index()];
    const saved_second = instructions.items[clone_second_instruction.index()];
    const saved_result = values.items[clone_second_result.index()];

    instructions.items[clone_first_instruction.index()].operation = .{ .copy = source_parameter };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_first_instruction.index()] = saved_first;

    instructions.items[clone_second_instruction.index()].effects = .place_read;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_second_instruction.index()] = saved_second;

    instructions.items[clone_second_instruction.index()].evidence = &.{};
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_second_instruction.index()] = saved_second;

    instructions.items[clone_second_instruction.index()].claims = &.{ir.ClaimId.fromIndex(0)};
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_second_instruction.index()] = saved_second;

    instructions.items[clone_second_instruction.index()].pack_result = ir.ValuePackId.fromIndex(0);
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_second_instruction.index()] = saved_second;

    values.items[clone_second_result.index()].type = .number;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    values.items[clone_second_result.index()] = saved_result;

    values.items[clone_second_result.index()].origin = .{ .instruction_result = .{ .instruction = clone_first_instruction, .index = 0 } };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    values.items[clone_second_result.index()] = saved_result;

    blocks[clone_id.index()].terminator = .{ .return_values = &.{clone_first_result} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}

test "clone remapping refreshes aliased program slices after capacity growth" {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const parameter_id = ir.ValueId.fromIndex(0);
    const result_id = ir.ValueId.fromIndex(1);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const source = ir.Block{
        .id = source_id,
        .function = function_id,
        .name_hint = "external_parameter_use",
        .instructions = &.{instruction_id},
        .terminator = .{ .return_values = &.{result_id} },
    };
    const base_values = [_]ir.Value{
        .{ .id = parameter_id, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = result_id, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } } },
    };
    const base_instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = source_id,
        .operation = .{ .binary = .{ .operator = .add, .left = parameter_id, .right = parameter_id } },
        .results = &.{result_id},
        .effects = .pure,
    }};
    var functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{parameter_id},
        .blocks = &.{source_id},
        .entry_block = source_id,
    }};
    const source_program: ir.Program = .{
        .program_id = "clone-slice-refresh",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
    };

    var values: std.ArrayList(ir.Value) = .empty;
    defer values.deinit(allocator);
    try values.appendSlice(allocator, &base_values);
    try values.shrinkAndFreePrecise(allocator, values.items.len);
    var instructions: std.ArrayList(ir.Instruction) = .empty;
    defer instructions.deinit(allocator);
    try instructions.appendSlice(allocator, &base_instructions);
    try instructions.shrinkAndFreePrecise(allocator, instructions.items.len);
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    defer packs.deinit(allocator);

    var aliased_program = source_program;
    aliased_program.values = values.items;
    aliased_program.instructions = instructions.items;
    aliased_program.value_packs = packs.items;
    const old_values_pointer = values.items.ptr;
    const cloned = try node_split.cloneBlockInArena(
        allocator,
        &aliased_program,
        &instructions,
        &values,
        &packs,
        source,
        clone_id,
    );
    defer allocator.free(cloned.block.parameters);
    defer allocator.free(cloned.block.instructions);
    defer switch (cloned.block.terminator) {
        .return_values => |returned| allocator.free(returned),
        else => {},
    };
    defer for (cloned.block.instructions) |id| allocator.free(instructions.items[id.index()].results);

    try std.testing.expect(values.items.ptr != old_values_pointer);
    try std.testing.expect(values.capacity > base_values.len);
    try std.testing.expect(instructions.capacity > base_instructions.len);
    try std.testing.expectEqual(parameter_id, instructions.items[1].operation.binary.left);
    try std.testing.expectEqual(parameter_id, instructions.items[1].operation.binary.right);
    try std.testing.expectEqual(result_id, instructions.items[0].results[0]);
    try std.testing.expectEqual(ir.ValueId.fromIndex(2), instructions.items[1].results[0]);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ir.ValueId.fromIndex(2)}, cloned.block.terminator.return_values);
    try std.testing.expectEqual(@as(usize, 1), cloned.cloned_instructions);
}

test "raw table-read replay binds operands mode and effects" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const table_value = ir.ValueId.fromIndex(0);
    const key_value = ir.ValueId.fromIndex(1);
    const incoming_value = ir.ValueId.fromIndex(2);
    const source_parameter = ir.ValueId.fromIndex(3);
    const clone_parameter = ir.ValueId.fromIndex(4);
    const source_result = ir.ValueId.fromIndex(5);
    const clone_result = ir.ValueId.fromIndex(6);
    const source_instruction = ir.InstructionId.fromIndex(0);
    const clone_instruction = ir.InstructionId.fromIndex(1);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const base_blocks = [_]ir.Block{
        .{
            .id = source_id,
            .function = function_id,
            .parameters = &.{source_parameter},
            .instructions = &.{source_instruction},
            .terminator = .{ .return_values = &.{source_result} },
            .evidence = &.{evidence_id},
        },
        .{
            .id = clone_id,
            .function = function_id,
            .parameters = &.{clone_parameter},
            .instructions = &.{clone_instruction},
            .terminator = .{ .return_values = &.{clone_result} },
            .evidence = &.{evidence_id},
        },
    };
    const values = [_]ir.Value{
        .{ .id = table_value, .function = function_id, .type = .{ .kind = .table }, .origin = .{ .parameter = 0 } },
        .{ .id = key_value, .function = function_id, .type = .string, .origin = .{ .parameter = 1 } },
        .{ .id = incoming_value, .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = source_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = clone_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone_id, .index = 0 } } },
        .{ .id = source_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = source_instruction, .index = 0 } } },
        .{ .id = clone_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = clone_instruction, .index = 0 } } },
    };
    const base_instructions = [_]ir.Instruction{
        .{
            .id = source_instruction,
            .block = source_id,
            .operation = .{ .table_get = .{ .table = table_value, .key = key_value, .mode = .raw } },
            .results = &.{source_result},
            .effects = .raw_table_read,
            .evidence = &.{evidence_id},
        },
        .{
            .id = clone_instruction,
            .block = clone_id,
            .operation = .{ .table_get = .{ .table = table_value, .key = key_value, .mode = .raw } },
            .results = &.{clone_result},
            .effects = .raw_table_read,
            .evidence = &.{evidence_id},
        },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ table_value, key_value, incoming_value },
        .blocks = &.{ source_id, clone_id },
        .entry_block = source_id,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .structural_derivation, .locator = "fixture:raw-read-node-split" }};
    var program: ir.Program = .{
        .program_id = "raw-read-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &base_blocks,
        .instructions = &base_instructions,
        .values = &values,
        .evidence = &evidence,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&program, base_blocks[source_id.index()]));
    var unowned_functions = functions;
    unowned_functions[function_id.index()].parameters = &.{ key_value, incoming_value };
    var unowned_program = program;
    unowned_program.functions = &unowned_functions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&unowned_program, base_blocks[source_id.index()]));

    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{incoming_value} };
    const replayed = (try node_split.replayAlloc(std.testing.allocator, &program, incoming, clone_id)).?;
    defer std.testing.allocator.free(replayed.arguments);

    var changed_instructions = base_instructions;
    changed_instructions[clone_instruction.index()].operation.table_get.table = incoming_value;
    program.instructions = &changed_instructions;
    try std.testing.expect(try node_split.replayAlloc(std.testing.allocator, &program, incoming, clone_id) == null);

    changed_instructions = base_instructions;
    changed_instructions[clone_instruction.index()].operation.table_get.mode = .semantic;
    program.instructions = &changed_instructions;
    try std.testing.expect(try node_split.replayAlloc(std.testing.allocator, &program, incoming, clone_id) == null);

    changed_instructions = base_instructions;
    changed_instructions[clone_instruction.index()].effects = .pure;
    program.instructions = &changed_instructions;
    try std.testing.expect(try node_split.replayAlloc(std.testing.allocator, &program, incoming, clone_id) == null);

    var semantic_instructions = base_instructions;
    semantic_instructions[source_instruction.index()].operation.table_get.mode = .semantic;
    semantic_instructions[source_instruction.index()].effects = .semantic_table_read;
    semantic_instructions[clone_instruction.index()].operation.table_get.mode = .semantic;
    semantic_instructions[clone_instruction.index()].effects = .semantic_table_read;
    program.instructions = &semantic_instructions;
    const semantic_replayed = (try node_split.replayAlloc(std.testing.allocator, &program, incoming, clone_id)).?;
    defer std.testing.allocator.free(semantic_replayed.arguments);

    semantic_instructions[clone_instruction.index()].effects = .raw_table_read;
    try std.testing.expect(try node_split.replayAlloc(std.testing.allocator, &program, incoming, clone_id) == null);
}

test "fixed call cloning remaps arguments and replay binds invocation semantics" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const callee = ir.ValueId.fromIndex(0);
    const external_argument = ir.ValueId.fromIndex(1);
    const source_argument = ir.ValueId.fromIndex(2);
    const source_result = ir.ValueId.fromIndex(3);
    const source_call = ir.InstructionId.fromIndex(0);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .name_hint = "call_entry",
        .parameters = &.{source_argument},
        .instructions = &.{source_call},
        .terminator = .{ .return_values = &.{source_result} },
        .evidence = &.{evidence_id},
    };
    const base_values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = external_argument, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = source_argument, .function = function_id, .name_hint = "mapped_argument", .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = source_result, .function = function_id, .name_hint = "call_result", .origin = .{ .instruction_result = .{ .instruction = source_call, .index = 0 } } },
    };
    const base_instructions = [_]ir.Instruction{.{
        .id = source_call,
        .block = source_id,
        .operation = .{ .call = .{
            .callee = callee,
            .arguments = &.{ source_argument, external_argument },
            .result_arity = .{ .fixed = 1 },
        } },
        .results = &.{source_result},
        .effects = .dynamic_call,
        .evidence = &.{evidence_id},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ callee, external_argument },
        .blocks = &.{source_id},
        .entry_block = source_id,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .structural_derivation,
        .locator = "fixture:fixed-call-node-split",
    }};
    const source_program: ir.Program = .{
        .program_id = "fixed-call-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
        .evidence = &evidence,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&source_program, source));

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var values: std.ArrayList(ir.Value) = .empty;
    try values.appendSlice(allocator, &base_values);
    var instructions: std.ArrayList(ir.Instruction) = .empty;
    try instructions.appendSlice(allocator, &base_instructions);
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    try packs.appendSlice(allocator, source_program.value_packs);
    const cloned = try node_split.cloneBlockInArena(allocator, &source_program, &instructions, &values, &packs, source, clone_id);
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 1), cloned.cloned_instructions);
    const clone_call = ir.InstructionId.fromIndex(1);
    const clone_argument = ir.ValueId.fromIndex(4);
    const clone_result = ir.ValueId.fromIndex(5);
    try std.testing.expectEqual(callee, instructions.items[clone_call.index()].operation.call.callee);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_argument, external_argument },
        instructions.items[clone_call.index()].operation.call.arguments,
    );
    try std.testing.expectEqual(@as(u16, 1), instructions.items[clone_call.index()].operation.call.result_arity.fixed);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_result}, cloned.block.terminator.return_values);
    try std.testing.expectEqual(clone_call, values.items[clone_result.index()].origin.instruction_result.instruction);

    var blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{external_argument} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved = instructions.items[clone_call.index()];
    instructions.items[clone_call.index()].operation.call.arguments = &.{ source_argument, external_argument };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_call.index()] = saved;

    instructions.items[clone_call.index()].operation.call.callee = external_argument;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_call.index()] = saved;

    instructions.items[clone_call.index()].operation.call.result_arity = .{ .fixed = 0 };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_call.index()] = saved;

    instructions.items[clone_call.index()].effects = .raw_table_read;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_call.index()] = saved;

    blocks[clone_id.index()].terminator = .{ .return_values = &.{source_result} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}
