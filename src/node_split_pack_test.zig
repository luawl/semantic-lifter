const std = @import("std");
const ir = @import("ir.zig");
const node_split = @import("node_split.zig");

test "variadic call packs clone into mapped adjust-pack results" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const call_id = ir.InstructionId.fromIndex(0);
    const adjust_id = ir.InstructionId.fromIndex(1);
    const callee = ir.ValueId.fromIndex(0);
    const source_parameter = ir.ValueId.fromIndex(1);
    const first_result = ir.ValueId.fromIndex(2);
    const second_result = ir.ValueId.fromIndex(3);
    const source_pack = ir.ValuePackId.fromIndex(0);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const pack_prefix = [_]ir.ValueType{ .integer, .string };
    const base_values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = source_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = first_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 0 } } },
        .{ .id = second_result, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 1 } } },
    };
    const base_packs = [_]ir.ValuePack{.{
        .id = source_pack,
        .function = function_id,
        .origin = .{ .instruction_result = call_id },
        .shape = .{ .prefix = &pack_prefix, .tail = .open },
        .evidence = &.{evidence_id},
    }};
    const base_instructions = [_]ir.Instruction{
        .{
            .id = call_id,
            .block = source_id,
            .operation = .{ .call = .{
                .callee = callee,
                .arguments = &.{source_parameter},
                .result_arity = .{ .variadic = {} },
            } },
            .results = &.{},
            .pack_result = source_pack,
            .effects = .dynamic_call,
            .evidence = &.{evidence_id},
        },
        .{
            .id = adjust_id,
            .block = source_id,
            .operation = .{ .adjust_pack = source_pack },
            .results = &.{ first_result, second_result },
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
    };
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{source_parameter},
        .instructions = &.{ call_id, adjust_id },
        .terminator = .{ .return_values = &.{ first_result, second_result } },
        .evidence = &.{evidence_id},
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{callee},
        .blocks = &.{source_id},
        .entry_block = source_id,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .structural_derivation,
        .locator = "fixture:variadic-pack-node-split",
    }};
    var source_program: ir.Program = .{
        .program_id = "variadic-pack-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
        .value_packs = &base_packs,
        .evidence = &evidence,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&source_program, source));

    var changed_instructions = base_instructions;
    changed_instructions[call_id.index()].pack_result = null;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[call_id.index()].operation.call.argument_pack = source_pack;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[adjust_id.index()].operation.adjust_pack = ir.ValuePackId.fromIndex(1);
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.instructions = &base_instructions;
    var changed_source = source;
    changed_source.terminator = .{ .return_pack = source_pack };
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, changed_source));

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var values: std.ArrayList(ir.Value) = .empty;
    try values.appendSlice(allocator, &base_values);
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    try packs.appendSlice(allocator, &base_packs);
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
    try std.testing.expectEqual(@as(usize, 3), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 1), cloned.cloned_packs);
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_instructions);

    const clone_call = ir.InstructionId.fromIndex(2);
    const clone_adjust = ir.InstructionId.fromIndex(3);
    const clone_parameter = ir.ValueId.fromIndex(4);
    const clone_first = ir.ValueId.fromIndex(5);
    const clone_second = ir.ValueId.fromIndex(6);
    const clone_pack = ir.ValuePackId.fromIndex(1);
    try std.testing.expectEqual(clone_pack, instructions.items[clone_call.index()].pack_result.?);
    try std.testing.expectEqual(clone_pack, instructions.items[clone_adjust.index()].operation.adjust_pack);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_parameter}, instructions.items[clone_call.index()].operation.call.arguments);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ clone_first, clone_second }, instructions.items[clone_adjust.index()].results);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ clone_first, clone_second }, cloned.block.terminator.return_values);
    try std.testing.expectEqual(clone_call, packs.items[clone_pack.index()].origin.instruction_result);
    try std.testing.expectEqualSlices(ir.ValueType, &pack_prefix, packs.items[clone_pack.index()].shape.prefix);

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    program.value_packs = packs.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{source_parameter} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_adjust = instructions.items[clone_adjust.index()];
    instructions.items[clone_adjust.index()].operation.adjust_pack = source_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_adjust.index()] = saved_adjust;

    const saved_call = instructions.items[clone_call.index()];
    instructions.items[clone_call.index()].pack_result = source_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_call.index()] = saved_call;

    const saved_pack = packs.items[clone_pack.index()];
    packs.items[clone_pack.index()].origin = .{ .instruction_result = call_id };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    packs.items[clone_pack.index()] = saved_pack;

    packs.items[clone_pack.index()].shape = .{ .prefix = &.{ .number, .string }, .tail = .open };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    packs.items[clone_pack.index()] = saved_pack;

    packs.items[clone_pack.index()].evidence = &.{};
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}

test "a local result pack maps into a later call argument tail" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const producer_id = ir.InstructionId.fromIndex(0);
    const forward_id = ir.InstructionId.fromIndex(1);
    const adjust_id = ir.InstructionId.fromIndex(2);
    const callee = ir.ValueId.fromIndex(0);
    const source_parameter = ir.ValueId.fromIndex(1);
    const adjusted = ir.ValueId.fromIndex(2);
    const producer_pack = ir.ValuePackId.fromIndex(0);
    const forwarded_pack = ir.ValuePackId.fromIndex(1);
    const pack_prefix = [_]ir.ValueType{.integer};
    const base_values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = source_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = adjusted, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 0 } } },
    };
    const base_packs = [_]ir.ValuePack{
        .{
            .id = producer_pack,
            .function = function_id,
            .origin = .{ .instruction_result = producer_id },
            .shape = .{ .prefix = &pack_prefix, .tail = .open },
        },
        .{
            .id = forwarded_pack,
            .function = function_id,
            .origin = .{ .instruction_result = forward_id },
            .shape = .{ .prefix = &pack_prefix, .tail = .open },
        },
    };
    const base_instructions = [_]ir.Instruction{
        .{
            .id = producer_id,
            .block = source_id,
            .operation = .{ .call = .{
                .callee = callee,
                .arguments = &.{source_parameter},
                .result_arity = .{ .variadic = {} },
            } },
            .results = &.{},
            .pack_result = producer_pack,
            .effects = .dynamic_call,
        },
        .{
            .id = forward_id,
            .block = source_id,
            .operation = .{ .call = .{
                .callee = callee,
                .arguments = &.{source_parameter},
                .argument_pack = producer_pack,
                .result_arity = .{ .variadic = {} },
            } },
            .results = &.{},
            .pack_result = forwarded_pack,
            .effects = .dynamic_call,
        },
        .{
            .id = adjust_id,
            .block = source_id,
            .operation = .{ .adjust_pack = forwarded_pack },
            .results = &.{adjusted},
            .effects = .pure,
        },
    };
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{source_parameter},
        .instructions = &.{ producer_id, forward_id, adjust_id },
        .terminator = .{ .return_values = &.{adjusted} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{callee},
        .blocks = &.{source_id},
        .entry_block = source_id,
    }};
    var source_program: ir.Program = .{
        .program_id = "local-argument-pack-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
        .value_packs = &base_packs,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&source_program, source));

    var reordered = source;
    reordered.instructions = &.{ forward_id, producer_id, adjust_id };
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, reordered));

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var values: std.ArrayList(ir.Value) = .empty;
    try values.appendSlice(allocator, &base_values);
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    try packs.appendSlice(allocator, &base_packs);
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
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_packs);
    try std.testing.expectEqual(@as(usize, 3), cloned.cloned_instructions);

    const clone_producer = ir.InstructionId.fromIndex(3);
    const clone_forward = ir.InstructionId.fromIndex(4);
    const clone_adjust = ir.InstructionId.fromIndex(5);
    const clone_producer_pack = ir.ValuePackId.fromIndex(2);
    const clone_forwarded_pack = ir.ValuePackId.fromIndex(3);
    try std.testing.expectEqual(clone_producer_pack, instructions.items[clone_producer.index()].pack_result.?);
    try std.testing.expectEqual(clone_producer_pack, instructions.items[clone_forward.index()].operation.call.argument_pack.?);
    try std.testing.expectEqual(clone_forwarded_pack, instructions.items[clone_forward.index()].pack_result.?);
    try std.testing.expectEqual(clone_forwarded_pack, instructions.items[clone_adjust.index()].operation.adjust_pack);

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    program.value_packs = packs.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{source_parameter} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_forward = instructions.items[clone_forward.index()];
    instructions.items[clone_forward.index()].operation.call.argument_pack = producer_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_forward.index()] = saved_forward;

    instructions.items[clone_forward.index()].operation.call.argument_pack = null;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_forward.index()] = saved_forward;

    instructions.items[clone_forward.index()].pack_result = forwarded_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}

test "canonical function varargs are shared while local result packs remain fresh" {
    const function_id = ir.FunctionId.fromIndex(0);
    const other_function = ir.FunctionId.fromIndex(1);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const vararg_adjust_id = ir.InstructionId.fromIndex(0);
    const call_id = ir.InstructionId.fromIndex(1);
    const result_adjust_id = ir.InstructionId.fromIndex(2);
    const callee = ir.ValueId.fromIndex(0);
    const source_parameter = ir.ValueId.fromIndex(1);
    const first_vararg = ir.ValueId.fromIndex(2);
    const second_vararg = ir.ValueId.fromIndex(3);
    const final_result = ir.ValueId.fromIndex(4);
    const vararg_pack = ir.ValuePackId.fromIndex(0);
    const result_pack = ir.ValuePackId.fromIndex(1);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const result_prefix = [_]ir.ValueType{.integer};
    const base_values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = source_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = first_vararg, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = vararg_adjust_id, .index = 0 } } },
        .{ .id = second_vararg, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = vararg_adjust_id, .index = 1 } } },
        .{ .id = final_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = result_adjust_id, .index = 0 } } },
    };
    const base_packs = [_]ir.ValuePack{
        .{
            .id = vararg_pack,
            .function = function_id,
            .origin = .{ .varargs = function_id },
            .shape = .open_unknown,
            .evidence = &.{evidence_id},
        },
        .{
            .id = result_pack,
            .function = function_id,
            .origin = .{ .instruction_result = call_id },
            .shape = .{ .prefix = &result_prefix, .tail = .open },
            .evidence = &.{evidence_id},
        },
    };
    const base_instructions = [_]ir.Instruction{
        .{
            .id = vararg_adjust_id,
            .block = source_id,
            .operation = .{ .adjust_pack = vararg_pack },
            .results = &.{ first_vararg, second_vararg },
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
        .{
            .id = call_id,
            .block = source_id,
            .operation = .{ .call = .{
                .callee = callee,
                .arguments = &.{ source_parameter, first_vararg },
                .argument_pack = vararg_pack,
                .result_arity = .{ .variadic = {} },
            } },
            .results = &.{},
            .pack_result = result_pack,
            .effects = .dynamic_call,
            .evidence = &.{evidence_id},
        },
        .{
            .id = result_adjust_id,
            .block = source_id,
            .operation = .{ .adjust_pack = result_pack },
            .results = &.{final_result},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
    };
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{source_parameter},
        .instructions = &.{ vararg_adjust_id, call_id, result_adjust_id },
        .terminator = .{ .return_values = &.{final_result} },
        .evidence = &.{evidence_id},
    };
    const base_functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{callee},
        .blocks = &.{source_id},
        .entry_block = source_id,
        .is_variadic = true,
        .vararg_pack = vararg_pack,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .structural_derivation,
        .locator = "fixture:function-vararg-node-split",
    }};
    var source_program: ir.Program = .{
        .program_id = "function-vararg-node-split",
        .entry_function = function_id,
        .functions = &base_functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
        .value_packs = &base_packs,
        .evidence = &evidence,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&source_program, source));

    var changed_functions = base_functions;
    changed_functions[0].is_variadic = false;
    source_program.functions = &changed_functions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_functions = base_functions;
    changed_functions[0].vararg_pack = null;
    source_program.functions = &changed_functions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_functions = base_functions;
    changed_functions[0].vararg_pack = result_pack;
    source_program.functions = &changed_functions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_functions = base_functions;
    changed_functions[0].id = other_function;
    source_program.functions = &changed_functions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.functions = &base_functions;
    var changed_packs = base_packs;
    changed_packs[vararg_pack.index()].id = ir.ValuePackId.fromIndex(2);
    source_program.value_packs = &changed_packs;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_packs = base_packs;
    changed_packs[vararg_pack.index()].function = other_function;
    source_program.value_packs = &changed_packs;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_packs = base_packs;
    changed_packs[vararg_pack.index()].origin = .{ .varargs = other_function };
    source_program.value_packs = &changed_packs;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_packs = base_packs;
    changed_packs[vararg_pack.index()].origin = .{ .instruction_result = call_id };
    source_program.value_packs = &changed_packs;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_packs = base_packs;
    changed_packs[vararg_pack.index()].shape.tail = .closed;
    source_program.value_packs = &changed_packs;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_packs = base_packs;
    changed_packs[vararg_pack.index()].shape.prefix = &.{ir.ValueType.integer};
    source_program.value_packs = &changed_packs;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.value_packs = &base_packs;
    var changed_instructions = base_instructions;
    changed_instructions[call_id.index()].operation.call.argument_pack = result_pack;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.instructions = &base_instructions;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var values: std.ArrayList(ir.Value) = .empty;
    try values.appendSlice(allocator, &base_values);
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    try packs.appendSlice(allocator, &base_packs);
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
    try std.testing.expectEqual(@as(usize, 4), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 1), cloned.cloned_packs);
    try std.testing.expectEqual(@as(usize, 3), cloned.cloned_instructions);

    const clone_vararg_adjust = ir.InstructionId.fromIndex(3);
    const clone_call = ir.InstructionId.fromIndex(4);
    const clone_result_adjust = ir.InstructionId.fromIndex(5);
    const clone_parameter = ir.ValueId.fromIndex(5);
    const clone_first_vararg = ir.ValueId.fromIndex(6);
    const clone_result = ir.ValueId.fromIndex(8);
    const clone_result_pack = ir.ValuePackId.fromIndex(2);
    try std.testing.expectEqual(vararg_pack, instructions.items[clone_vararg_adjust.index()].operation.adjust_pack);
    try std.testing.expectEqual(vararg_pack, instructions.items[clone_call.index()].operation.call.argument_pack.?);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_parameter, clone_first_vararg },
        instructions.items[clone_call.index()].operation.call.arguments,
    );
    try std.testing.expectEqual(clone_result_pack, instructions.items[clone_call.index()].pack_result.?);
    try std.testing.expectEqual(clone_result_pack, instructions.items[clone_result_adjust.index()].operation.adjust_pack);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_result}, cloned.block.terminator.return_values);
    try std.testing.expectEqual(call_id, packs.items[result_pack.index()].origin.instruction_result);
    try std.testing.expectEqual(clone_call, packs.items[clone_result_pack.index()].origin.instruction_result);

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    program.value_packs = packs.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{source_parameter} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_clone_call = instructions.items[clone_call.index()];
    instructions.items[clone_call.index()].operation.call.argument_pack = clone_result_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_call.index()] = saved_clone_call;

    const saved_clone_vararg_adjust = instructions.items[clone_vararg_adjust.index()];
    instructions.items[clone_vararg_adjust.index()].operation.adjust_pack = clone_result_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_vararg_adjust.index()] = saved_clone_vararg_adjust;

    instructions.items[clone_result_adjust.index()].operation.adjust_pack = result_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}

test "namecall replay binds receiver method arguments and pack identities" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const namecall_id = ir.InstructionId.fromIndex(0);
    const adjust_id = ir.InstructionId.fromIndex(1);
    const incoming_receiver = ir.ValueId.fromIndex(0);
    const fixed_argument = ir.ValueId.fromIndex(1);
    const source_receiver = ir.ValueId.fromIndex(2);
    const source_result = ir.ValueId.fromIndex(3);
    const vararg_pack = ir.ValuePackId.fromIndex(0);
    const result_pack = ir.ValuePackId.fromIndex(1);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const result_prefix = [_]ir.ValueType{.integer};
    const base_values = [_]ir.Value{
        .{ .id = incoming_receiver, .function = function_id, .type = .{ .kind = .table }, .origin = .{ .parameter = 0 } },
        .{ .id = fixed_argument, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = source_receiver, .function = function_id, .type = .{ .kind = .table }, .name_hint = "receiver", .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = source_result, .function = function_id, .type = .integer, .name_hint = "namecall_result", .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 0 } } },
    };
    const base_packs = [_]ir.ValuePack{
        .{
            .id = vararg_pack,
            .function = function_id,
            .origin = .{ .varargs = function_id },
            .shape = .open_unknown,
            .evidence = &.{evidence_id},
        },
        .{
            .id = result_pack,
            .function = function_id,
            .origin = .{ .instruction_result = namecall_id },
            .shape = .{ .prefix = &result_prefix, .tail = .open },
            .evidence = &.{evidence_id},
        },
    };
    const base_instructions = [_]ir.Instruction{
        .{
            .id = namecall_id,
            .block = source_id,
            .operation = .{ .namecall = .{
                .receiver = source_receiver,
                .method = "apply",
                .arguments = &.{ source_receiver, fixed_argument },
                .argument_pack = vararg_pack,
                .result_arity = .{ .variadic = {} },
            } },
            .results = &.{},
            .pack_result = result_pack,
            .effects = .namecall,
            .evidence = &.{evidence_id},
        },
        .{
            .id = adjust_id,
            .block = source_id,
            .operation = .{ .adjust_pack = result_pack },
            .results = &.{source_result},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
    };
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .name_hint = "namecall_entry",
        .parameters = &.{source_receiver},
        .instructions = &.{ namecall_id, adjust_id },
        .terminator = .{ .return_values = &.{source_result} },
        .evidence = &.{evidence_id},
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ incoming_receiver, fixed_argument },
        .blocks = &.{source_id},
        .entry_block = source_id,
        .is_variadic = true,
        .vararg_pack = vararg_pack,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .structural_derivation,
        .locator = "fixture:namecall-node-split",
    }};
    var source_program: ir.Program = .{
        .program_id = "namecall-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
        .value_packs = &base_packs,
        .evidence = &evidence,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&source_program, source));

    var changed_instructions = base_instructions;
    changed_instructions[namecall_id.index()].operation.namecall.method = "";
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));
    changed_instructions = base_instructions;
    changed_instructions[namecall_id.index()].effects = .pure;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.instructions = &base_instructions;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var values: std.ArrayList(ir.Value) = .empty;
    try values.appendSlice(allocator, &base_values);
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    try packs.appendSlice(allocator, &base_packs);
    var instructions: std.ArrayList(ir.Instruction) = .empty;
    try instructions.appendSlice(allocator, &base_instructions);
    const cloned = try node_split.cloneBlockInArena(allocator, &source_program, &instructions, &values, &packs, source, clone_id);

    const clone_namecall = ir.InstructionId.fromIndex(2);
    const clone_adjust = ir.InstructionId.fromIndex(3);
    const clone_receiver = ir.ValueId.fromIndex(4);
    const clone_result = ir.ValueId.fromIndex(5);
    const clone_result_pack = ir.ValuePackId.fromIndex(2);
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 1), cloned.cloned_packs);
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_instructions);
    const cloned_namecall = instructions.items[clone_namecall.index()].operation.namecall;
    try std.testing.expectEqual(clone_receiver, cloned_namecall.receiver);
    try std.testing.expectEqualStrings("apply", cloned_namecall.method);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ clone_receiver, fixed_argument }, cloned_namecall.arguments);
    try std.testing.expectEqual(vararg_pack, cloned_namecall.argument_pack.?);
    try std.testing.expect(cloned_namecall.result_arity == .variadic);
    try std.testing.expectEqual(clone_result_pack, instructions.items[clone_namecall.index()].pack_result.?);
    try std.testing.expectEqual(clone_result_pack, instructions.items[clone_adjust.index()].operation.adjust_pack);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_result}, cloned.block.terminator.return_values);
    try std.testing.expectEqual(clone_namecall, packs.items[clone_result_pack.index()].origin.instruction_result);

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    program.value_packs = packs.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{incoming_receiver} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_namecall = instructions.items[clone_namecall.index()];
    instructions.items[clone_namecall.index()].operation.namecall.receiver = source_receiver;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_namecall.index()] = saved_namecall;

    instructions.items[clone_namecall.index()].operation.namecall.method = "other";
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_namecall.index()] = saved_namecall;

    instructions.items[clone_namecall.index()].operation.namecall.arguments = &.{ fixed_argument, clone_receiver };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_namecall.index()] = saved_namecall;

    instructions.items[clone_namecall.index()].operation.namecall.argument_pack = clone_result_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_namecall.index()] = saved_namecall;

    instructions.items[clone_namecall.index()].operation.namecall.result_arity = .{ .fixed = 0 };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_namecall.index()] = saved_namecall;

    instructions.items[clone_namecall.index()].pack_result = result_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_namecall.index()] = saved_namecall;

    instructions.items[clone_namecall.index()].effects = .pure;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}
