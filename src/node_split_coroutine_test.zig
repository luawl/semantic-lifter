const std = @import("std");
const ir = @import("ir.zig");
const node_split = @import("node_split.zig");
const solver_equivalence = @import("solver_equivalence.zig");

test "coroutine creation replays callee and fresh thread identity" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const create_id = ir.InstructionId.fromIndex(0);
    const incoming_callee = ir.ValueId.fromIndex(0);
    const source_callee = ir.ValueId.fromIndex(1);
    const source_thread = ir.ValueId.fromIndex(2);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const base_values = [_]ir.Value{
        .{ .id = incoming_callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{
            .id = source_callee,
            .function = function_id,
            .type = .function,
            .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } },
        },
        .{
            .id = source_thread,
            .function = function_id,
            .type = .{ .kind = .thread },
            .origin = .{ .instruction_result = .{ .instruction = create_id, .index = 0 } },
        },
    };
    const base_instructions = [_]ir.Instruction{.{
        .id = create_id,
        .block = source_id,
        .operation = .{ .coroutine_create = .{ .callee = source_callee } },
        .results = &.{source_thread},
        .effects = .coroutine_create,
        .evidence = &.{evidence_id},
    }};
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{source_callee},
        .instructions = &.{create_id},
        .terminator = .{ .return_values = &.{source_thread} },
        .evidence = &.{evidence_id},
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{incoming_callee},
        .blocks = &.{source_id},
        .entry_block = source_id,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .structural_derivation,
        .locator = "fixture:coroutine-create-node-split",
    }};
    var source_program: ir.Program = .{
        .program_id = "coroutine-create-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
        .evidence = &evidence,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&source_program, source));

    var changed_values = base_values;
    changed_values[source_thread.index()].type = .integer;
    source_program.values = &changed_values;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.values = &base_values;
    var changed_instructions = base_instructions;
    changed_instructions[0].operation.coroutine_create.callee = source_thread;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[0].effects = .pure;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.instructions = &base_instructions;
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
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 0), cloned.cloned_packs);
    try std.testing.expectEqual(@as(usize, 1), cloned.cloned_instructions);

    const clone_create = ir.InstructionId.fromIndex(1);
    const clone_callee = ir.ValueId.fromIndex(3);
    const clone_thread = ir.ValueId.fromIndex(4);
    try std.testing.expectEqual(clone_callee, instructions.items[clone_create.index()].operation.coroutine_create.callee);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_thread}, instructions.items[clone_create.index()].results);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_thread}, cloned.block.terminator.return_values);

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    try std.testing.expectEqual(
        solver_equivalence.DynamicRelation.distinct,
        solver_equivalence.dynamicDescriptorRelation(
            solver_equivalence.dynamicValueDescriptor(&program, source_thread).?,
            solver_equivalence.dynamicValueDescriptor(&program, clone_thread).?,
        ),
    );
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{incoming_callee} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_create = instructions.items[clone_create.index()];
    instructions.items[clone_create.index()].operation.coroutine_create.callee = source_callee;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_create.index()] = saved_create;

    values.items[clone_thread.index()].type = .integer;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    values.items[clone_thread.index()] = base_values[source_thread.index()];
    values.items[clone_thread.index()].id = clone_thread;
    values.items[clone_thread.index()].origin = .{ .instruction_result = .{ .instruction = clone_create, .index = 0 } };

    instructions.items[clone_create.index()].effects = .pure;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}

test "coroutine resume replays local thread status results and packs" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const create_id = ir.InstructionId.fromIndex(0);
    const fixed_resume_id = ir.InstructionId.fromIndex(1);
    const open_resume_id = ir.InstructionId.fromIndex(2);
    const adjust_id = ir.InstructionId.fromIndex(3);
    const incoming_callee = ir.ValueId.fromIndex(0);
    const incoming_argument = ir.ValueId.fromIndex(1);
    const source_callee = ir.ValueId.fromIndex(2);
    const source_argument = ir.ValueId.fromIndex(3);
    const source_thread = ir.ValueId.fromIndex(4);
    const fixed_status = ir.ValueId.fromIndex(5);
    const fixed_payload = ir.ValueId.fromIndex(6);
    const adjusted_status = ir.ValueId.fromIndex(7);
    const adjusted_payload = ir.ValueId.fromIndex(8);
    const vararg_pack = ir.ValuePackId.fromIndex(0);
    const resume_pack = ir.ValuePackId.fromIndex(1);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const resume_prefix = [_]ir.ValueType{ .boolean, .string };
    const base_values = [_]ir.Value{
        .{ .id = incoming_callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = incoming_argument, .function = function_id, .type = .string, .origin = .{ .parameter = 1 } },
        .{
            .id = source_callee,
            .function = function_id,
            .type = .function,
            .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } },
        },
        .{
            .id = source_argument,
            .function = function_id,
            .type = .string,
            .origin = .{ .block_parameter = .{ .block = source_id, .index = 1 } },
        },
        .{
            .id = source_thread,
            .function = function_id,
            .type = .{ .kind = .thread },
            .origin = .{ .instruction_result = .{ .instruction = create_id, .index = 0 } },
        },
        .{
            .id = fixed_status,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .instruction_result = .{ .instruction = fixed_resume_id, .index = 0 } },
        },
        .{
            .id = fixed_payload,
            .function = function_id,
            .type = .string,
            .origin = .{ .instruction_result = .{ .instruction = fixed_resume_id, .index = 1 } },
        },
        .{
            .id = adjusted_status,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 0 } },
        },
        .{
            .id = adjusted_payload,
            .function = function_id,
            .type = .string,
            .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 1 } },
        },
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
            .id = resume_pack,
            .function = function_id,
            .origin = .{ .instruction_result = open_resume_id },
            .shape = .{ .prefix = &resume_prefix, .tail = .open },
            .evidence = &.{evidence_id},
        },
    };
    const base_instructions = [_]ir.Instruction{
        .{
            .id = create_id,
            .block = source_id,
            .operation = .{ .coroutine_create = .{ .callee = source_callee } },
            .results = &.{source_thread},
            .effects = .coroutine_create,
            .evidence = &.{evidence_id},
        },
        .{
            .id = fixed_resume_id,
            .block = source_id,
            .operation = .{ .coroutine_resume = .{
                .thread = source_thread,
                .arguments = &.{source_argument},
                .argument_pack = vararg_pack,
                .result_arity = .{ .fixed = 2 },
            } },
            .results = &.{ fixed_status, fixed_payload },
            .effects = .coroutine_resume,
            .evidence = &.{evidence_id},
        },
        .{
            .id = open_resume_id,
            .block = source_id,
            .operation = .{ .coroutine_resume = .{
                .thread = source_thread,
                .arguments = &.{fixed_payload},
                .argument_pack = vararg_pack,
                .result_arity = .{ .variadic = {} },
            } },
            .results = &.{},
            .pack_result = resume_pack,
            .effects = .coroutine_resume,
            .evidence = &.{evidence_id},
        },
        .{
            .id = adjust_id,
            .block = source_id,
            .operation = .{ .adjust_pack = resume_pack },
            .results = &.{ adjusted_status, adjusted_payload },
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
    };
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{ source_callee, source_argument },
        .instructions = &.{ create_id, fixed_resume_id, open_resume_id, adjust_id },
        .terminator = .{ .return_values = &.{ adjusted_status, adjusted_payload } },
        .evidence = &.{evidence_id},
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ incoming_callee, incoming_argument },
        .blocks = &.{source_id},
        .entry_block = source_id,
        .is_variadic = true,
        .vararg_pack = vararg_pack,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .structural_derivation,
        .locator = "fixture:coroutine-resume-node-split",
    }};
    var source_program: ir.Program = .{
        .program_id = "coroutine-resume-node-split",
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
    changed_instructions[fixed_resume_id.index()].operation.coroutine_resume.thread = source_argument;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[open_resume_id.index()].effects = .pure;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.instructions = &base_instructions;
    var changed_packs = base_packs;
    const invalid_prefix = [_]ir.ValueType{ .integer, .string };
    changed_packs[resume_pack.index()].shape.prefix = &invalid_prefix;
    source_program.value_packs = &changed_packs;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.value_packs = &base_packs;
    var reordered = source;
    reordered.instructions = &.{ fixed_resume_id, create_id, open_resume_id, adjust_id };
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
    try std.testing.expectEqual(@as(usize, 7), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 1), cloned.cloned_packs);
    try std.testing.expectEqual(@as(usize, 4), cloned.cloned_instructions);

    const clone_create = ir.InstructionId.fromIndex(4);
    const clone_fixed_resume = ir.InstructionId.fromIndex(5);
    const clone_open_resume = ir.InstructionId.fromIndex(6);
    const clone_adjust = ir.InstructionId.fromIndex(7);
    const clone_callee = ir.ValueId.fromIndex(9);
    const clone_argument = ir.ValueId.fromIndex(10);
    const clone_thread = ir.ValueId.fromIndex(11);
    const clone_fixed_status = ir.ValueId.fromIndex(12);
    const clone_fixed_payload = ir.ValueId.fromIndex(13);
    const clone_adjusted_status = ir.ValueId.fromIndex(14);
    const clone_adjusted_payload = ir.ValueId.fromIndex(15);
    const clone_resume_pack = ir.ValuePackId.fromIndex(2);
    try std.testing.expectEqual(clone_callee, instructions.items[clone_create.index()].operation.coroutine_create.callee);
    try std.testing.expectEqual(clone_thread, instructions.items[clone_fixed_resume.index()].operation.coroutine_resume.thread);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{clone_argument},
        instructions.items[clone_fixed_resume.index()].operation.coroutine_resume.arguments,
    );
    try std.testing.expectEqual(vararg_pack, instructions.items[clone_fixed_resume.index()].operation.coroutine_resume.argument_pack.?);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_fixed_status, clone_fixed_payload },
        instructions.items[clone_fixed_resume.index()].results,
    );
    try std.testing.expectEqual(clone_thread, instructions.items[clone_open_resume.index()].operation.coroutine_resume.thread);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{clone_fixed_payload},
        instructions.items[clone_open_resume.index()].operation.coroutine_resume.arguments,
    );
    try std.testing.expectEqual(clone_resume_pack, instructions.items[clone_open_resume.index()].pack_result.?);
    try std.testing.expectEqual(clone_resume_pack, instructions.items[clone_adjust.index()].operation.adjust_pack);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_adjusted_status, clone_adjusted_payload },
        cloned.block.terminator.return_values,
    );

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    program.value_packs = packs.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{ incoming_callee, incoming_argument } };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_fixed_resume = instructions.items[clone_fixed_resume.index()];
    instructions.items[clone_fixed_resume.index()].operation.coroutine_resume.thread = source_thread;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_fixed_resume.index()] = saved_fixed_resume;

    instructions.items[clone_fixed_resume.index()].operation.coroutine_resume.arguments = &.{source_argument};
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_fixed_resume.index()] = saved_fixed_resume;

    const saved_open_resume = instructions.items[clone_open_resume.index()];
    instructions.items[clone_open_resume.index()].pack_result = resume_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_open_resume.index()] = saved_open_resume;

    const saved_status = values.items[clone_fixed_status.index()];
    values.items[clone_fixed_status.index()].type = .integer;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    values.items[clone_fixed_status.index()] = saved_status;

    const saved_pack = packs.items[clone_resume_pack.index()];
    packs.items[clone_resume_pack.index()].shape.prefix = &invalid_prefix;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    packs.items[clone_resume_pack.index()] = saved_pack;

    instructions.items[clone_open_resume.index()].effects = .pure;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}

test "coroutine yield replays ordinary fixed and variadic results" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const fixed_yield_id = ir.InstructionId.fromIndex(0);
    const open_yield_id = ir.InstructionId.fromIndex(1);
    const adjust_id = ir.InstructionId.fromIndex(2);
    const incoming_argument = ir.ValueId.fromIndex(0);
    const source_argument = ir.ValueId.fromIndex(1);
    const fixed_result = ir.ValueId.fromIndex(2);
    const adjusted_first = ir.ValueId.fromIndex(3);
    const adjusted_second = ir.ValueId.fromIndex(4);
    const vararg_pack = ir.ValuePackId.fromIndex(0);
    const yield_pack = ir.ValuePackId.fromIndex(1);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const yield_prefix = [_]ir.ValueType{ .string, .string };
    const base_values = [_]ir.Value{
        .{ .id = incoming_argument, .function = function_id, .type = .string, .origin = .{ .parameter = 0 } },
        .{
            .id = source_argument,
            .function = function_id,
            .type = .string,
            .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } },
        },
        .{
            .id = fixed_result,
            .function = function_id,
            .type = .string,
            .origin = .{ .instruction_result = .{ .instruction = fixed_yield_id, .index = 0 } },
        },
        .{
            .id = adjusted_first,
            .function = function_id,
            .type = .string,
            .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 0 } },
        },
        .{
            .id = adjusted_second,
            .function = function_id,
            .type = .string,
            .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 1 } },
        },
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
            .id = yield_pack,
            .function = function_id,
            .origin = .{ .instruction_result = open_yield_id },
            .shape = .{ .prefix = &yield_prefix, .tail = .open },
            .evidence = &.{evidence_id},
        },
    };
    const base_instructions = [_]ir.Instruction{
        .{
            .id = fixed_yield_id,
            .block = source_id,
            .operation = .{ .coroutine_yield = .{
                .arguments = &.{source_argument},
                .argument_pack = vararg_pack,
                .result_arity = .{ .fixed = 1 },
            } },
            .results = &.{fixed_result},
            .effects = .coroutine_yield,
            .evidence = &.{evidence_id},
        },
        .{
            .id = open_yield_id,
            .block = source_id,
            .operation = .{ .coroutine_yield = .{
                .arguments = &.{fixed_result},
                .argument_pack = vararg_pack,
                .result_arity = .{ .variadic = {} },
            } },
            .results = &.{},
            .pack_result = yield_pack,
            .effects = .coroutine_yield,
            .evidence = &.{evidence_id},
        },
        .{
            .id = adjust_id,
            .block = source_id,
            .operation = .{ .adjust_pack = yield_pack },
            .results = &.{ adjusted_first, adjusted_second },
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
    };
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{source_argument},
        .instructions = &.{ fixed_yield_id, open_yield_id, adjust_id },
        .terminator = .{ .return_values = &.{ adjusted_first, adjusted_second } },
        .evidence = &.{evidence_id},
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{incoming_argument},
        .blocks = &.{source_id},
        .entry_block = source_id,
        .is_variadic = true,
        .vararg_pack = vararg_pack,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .structural_derivation,
        .locator = "fixture:coroutine-yield-node-split",
    }};
    var source_program: ir.Program = .{
        .program_id = "coroutine-yield-node-split",
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
    changed_instructions[open_yield_id.index()].operation.coroutine_yield.arguments = &.{adjusted_first};
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[open_yield_id.index()].effects = .pure;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.instructions = &base_instructions;
    var reordered = source;
    reordered.instructions = &.{ open_yield_id, fixed_yield_id, adjust_id };
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
    try std.testing.expectEqual(@as(usize, 4), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 1), cloned.cloned_packs);
    try std.testing.expectEqual(@as(usize, 3), cloned.cloned_instructions);

    const clone_fixed_yield = ir.InstructionId.fromIndex(3);
    const clone_open_yield = ir.InstructionId.fromIndex(4);
    const clone_adjust = ir.InstructionId.fromIndex(5);
    const clone_argument = ir.ValueId.fromIndex(5);
    const clone_fixed_result = ir.ValueId.fromIndex(6);
    const clone_adjusted_first = ir.ValueId.fromIndex(7);
    const clone_adjusted_second = ir.ValueId.fromIndex(8);
    const clone_yield_pack = ir.ValuePackId.fromIndex(2);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{clone_argument},
        instructions.items[clone_fixed_yield.index()].operation.coroutine_yield.arguments,
    );
    try std.testing.expectEqual(vararg_pack, instructions.items[clone_fixed_yield.index()].operation.coroutine_yield.argument_pack.?);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_fixed_result}, instructions.items[clone_fixed_yield.index()].results);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{clone_fixed_result},
        instructions.items[clone_open_yield.index()].operation.coroutine_yield.arguments,
    );
    try std.testing.expectEqual(clone_yield_pack, instructions.items[clone_open_yield.index()].pack_result.?);
    try std.testing.expectEqual(clone_yield_pack, instructions.items[clone_adjust.index()].operation.adjust_pack);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_adjusted_first, clone_adjusted_second },
        cloned.block.terminator.return_values,
    );

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    program.value_packs = packs.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{incoming_argument} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_fixed_yield = instructions.items[clone_fixed_yield.index()];
    instructions.items[clone_fixed_yield.index()].operation.coroutine_yield.arguments = &.{source_argument};
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_fixed_yield.index()] = saved_fixed_yield;

    const saved_open_yield = instructions.items[clone_open_yield.index()];
    instructions.items[clone_open_yield.index()].operation.coroutine_yield.result_arity = .{ .fixed = 0 };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_open_yield.index()] = saved_open_yield;

    instructions.items[clone_open_yield.index()].pack_result = yield_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_open_yield.index()] = saved_open_yield;

    const changed_prefix = [_]ir.ValueType{ .string, .integer };
    const saved_pack = packs.items[clone_yield_pack.index()];
    packs.items[clone_yield_pack.index()].shape.prefix = &changed_prefix;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    packs.items[clone_yield_pack.index()] = saved_pack;

    instructions.items[clone_open_yield.index()].effects = .pure;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}

test "coroutine yield replays resumed values and local argument packs" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const producer_id = ir.InstructionId.fromIndex(0);
    const fixed_yield_id = ir.InstructionId.fromIndex(1);
    const open_yield_id = ir.InstructionId.fromIndex(2);
    const adjust_id = ir.InstructionId.fromIndex(3);
    const callee = ir.ValueId.fromIndex(0);
    const source_parameter = ir.ValueId.fromIndex(1);
    const fixed_first = ir.ValueId.fromIndex(2);
    const fixed_second = ir.ValueId.fromIndex(3);
    const adjusted_first = ir.ValueId.fromIndex(4);
    const adjusted_second = ir.ValueId.fromIndex(5);
    const vararg_pack = ir.ValuePackId.fromIndex(0);
    const producer_pack = ir.ValuePackId.fromIndex(1);
    const yield_pack = ir.ValuePackId.fromIndex(2);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const producer_prefix = [_]ir.ValueType{ .integer, .{ .kind = .nil_value }, .integer };
    const yield_prefix = [_]ir.ValueType{ .string, .integer };
    const base_values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = source_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = fixed_first, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = fixed_yield_id, .index = 0 } } },
        .{ .id = fixed_second, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = fixed_yield_id, .index = 1 } } },
        .{ .id = adjusted_first, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 0 } } },
        .{ .id = adjusted_second, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 1 } } },
    };
    const base_packs = [_]ir.ValuePack{
        .{ .id = vararg_pack, .function = function_id, .origin = .{ .varargs = function_id }, .evidence = &.{evidence_id} },
        .{
            .id = producer_pack,
            .function = function_id,
            .origin = .{ .instruction_result = producer_id },
            .shape = .{ .prefix = &producer_prefix, .tail = .open },
            .evidence = &.{evidence_id},
        },
        .{
            .id = yield_pack,
            .function = function_id,
            .origin = .{ .instruction_result = open_yield_id },
            .shape = .{ .prefix = &yield_prefix, .tail = .open },
            .evidence = &.{evidence_id},
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
            .evidence = &.{evidence_id},
        },
        .{
            .id = fixed_yield_id,
            .block = source_id,
            .operation = .{ .coroutine_yield = .{
                .arguments = &.{source_parameter},
                .argument_pack = vararg_pack,
                .result_arity = .{ .fixed = 2 },
            } },
            .results = &.{ fixed_first, fixed_second },
            .effects = .coroutine_yield,
            .evidence = &.{evidence_id},
        },
        .{
            .id = open_yield_id,
            .block = source_id,
            .operation = .{ .coroutine_yield = .{
                .arguments = &.{ fixed_first, fixed_second },
                .argument_pack = producer_pack,
                .result_arity = .{ .variadic = {} },
            } },
            .results = &.{},
            .pack_result = yield_pack,
            .effects = .coroutine_yield,
            .evidence = &.{evidence_id},
        },
        .{
            .id = adjust_id,
            .block = source_id,
            .operation = .{ .adjust_pack = yield_pack },
            .results = &.{ adjusted_first, adjusted_second },
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
    };
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{source_parameter},
        .instructions = &.{ producer_id, fixed_yield_id, open_yield_id, adjust_id },
        .terminator = .{ .return_values = &.{ adjusted_first, adjusted_second } },
        .evidence = &.{evidence_id},
    };
    const functions = [_]ir.Function{.{
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
        .locator = "fixture:coroutine-yield-node-split",
    }};
    var source_program: ir.Program = .{
        .program_id = "coroutine-yield-node-split",
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
    changed_instructions[fixed_yield_id.index()].operation.coroutine_yield.argument_pack = yield_pack;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[fixed_yield_id.index()].operation.coroutine_yield.result_arity = .{ .fixed = 1 };
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[open_yield_id.index()].effects = .pure;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.instructions = &base_instructions;
    var reordered = source;
    reordered.instructions = &.{ open_yield_id, producer_id, fixed_yield_id, adjust_id };
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
    try std.testing.expectEqual(@as(usize, 5), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_packs);
    try std.testing.expectEqual(@as(usize, 4), cloned.cloned_instructions);

    const clone_producer = ir.InstructionId.fromIndex(4);
    const clone_fixed_yield = ir.InstructionId.fromIndex(5);
    const clone_open_yield = ir.InstructionId.fromIndex(6);
    const clone_adjust = ir.InstructionId.fromIndex(7);
    const clone_parameter = ir.ValueId.fromIndex(6);
    const clone_fixed_first = ir.ValueId.fromIndex(7);
    const clone_fixed_second = ir.ValueId.fromIndex(8);
    const clone_adjusted_first = ir.ValueId.fromIndex(9);
    const clone_adjusted_second = ir.ValueId.fromIndex(10);
    const clone_producer_pack = ir.ValuePackId.fromIndex(3);
    const clone_yield_pack = ir.ValuePackId.fromIndex(4);
    try std.testing.expectEqual(clone_producer_pack, instructions.items[clone_producer.index()].pack_result.?);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{clone_parameter},
        instructions.items[clone_fixed_yield.index()].operation.coroutine_yield.arguments,
    );
    try std.testing.expectEqual(vararg_pack, instructions.items[clone_fixed_yield.index()].operation.coroutine_yield.argument_pack.?);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_fixed_first, clone_fixed_second },
        instructions.items[clone_fixed_yield.index()].results,
    );
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_fixed_first, clone_fixed_second },
        instructions.items[clone_open_yield.index()].operation.coroutine_yield.arguments,
    );
    try std.testing.expectEqual(clone_producer_pack, instructions.items[clone_open_yield.index()].operation.coroutine_yield.argument_pack.?);
    try std.testing.expectEqual(clone_yield_pack, instructions.items[clone_open_yield.index()].pack_result.?);
    try std.testing.expectEqual(clone_yield_pack, instructions.items[clone_adjust.index()].operation.adjust_pack);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_adjusted_first, clone_adjusted_second },
        cloned.block.terminator.return_values,
    );

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    program.value_packs = packs.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{source_parameter} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_fixed_yield = instructions.items[clone_fixed_yield.index()];
    instructions.items[clone_fixed_yield.index()].operation.coroutine_yield.arguments = &.{source_parameter};
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_fixed_yield.index()] = saved_fixed_yield;

    instructions.items[clone_fixed_yield.index()].operation.coroutine_yield.argument_pack = null;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_fixed_yield.index()] = saved_fixed_yield;

    const saved_open_yield = instructions.items[clone_open_yield.index()];
    instructions.items[clone_open_yield.index()].operation.coroutine_yield.arguments = &.{ clone_fixed_second, clone_fixed_first };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_open_yield.index()] = saved_open_yield;

    instructions.items[clone_open_yield.index()].operation.coroutine_yield.argument_pack = producer_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_open_yield.index()] = saved_open_yield;

    instructions.items[clone_open_yield.index()].pack_result = yield_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_open_yield.index()] = saved_open_yield;

    instructions.items[clone_open_yield.index()].effects = .pure;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}
