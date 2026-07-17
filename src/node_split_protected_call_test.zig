const std = @import("std");
const ir = @import("ir.zig");
const node_split = @import("node_split.zig");

test "protected calls replay status results handlers and argument packs" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const fixed_id = ir.InstructionId.fromIndex(0);
    const producer_id = ir.InstructionId.fromIndex(1);
    const forward_id = ir.InstructionId.fromIndex(2);
    const adjust_id = ir.InstructionId.fromIndex(3);
    const callee = ir.ValueId.fromIndex(0);
    const source_handler = ir.ValueId.fromIndex(1);
    const source_argument = ir.ValueId.fromIndex(2);
    const fixed_status = ir.ValueId.fromIndex(3);
    const fixed_payload = ir.ValueId.fromIndex(4);
    const adjusted_status = ir.ValueId.fromIndex(5);
    const adjusted_payload = ir.ValueId.fromIndex(6);
    const vararg_pack = ir.ValuePackId.fromIndex(0);
    const producer_pack = ir.ValuePackId.fromIndex(1);
    const forwarded_pack = ir.ValuePackId.fromIndex(2);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const producer_prefix = [_]ir.ValueType{ .boolean, .string };
    const forwarded_prefix = [_]ir.ValueType{ .boolean, .integer };
    const base_values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = source_handler, .function = function_id, .type = .function, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = source_argument, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_id, .index = 1 } } },
        .{ .id = fixed_status, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = fixed_id, .index = 0 } } },
        .{ .id = fixed_payload, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = fixed_id, .index = 1 } } },
        .{ .id = adjusted_status, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 0 } } },
        .{ .id = adjusted_payload, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 1 } } },
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
            .id = forwarded_pack,
            .function = function_id,
            .origin = .{ .instruction_result = forward_id },
            .shape = .{ .prefix = &forwarded_prefix, .tail = .open },
            .evidence = &.{evidence_id},
        },
    };
    const base_instructions = [_]ir.Instruction{
        .{
            .id = fixed_id,
            .block = source_id,
            .operation = .{ .protected_call = .{
                .callee = callee,
                .error_handler = source_handler,
                .arguments = &.{source_argument},
                .argument_pack = vararg_pack,
                .result_arity = .{ .fixed = 2 },
            } },
            .results = &.{ fixed_status, fixed_payload },
            .effects = .protected_invocation,
            .evidence = &.{evidence_id},
        },
        .{
            .id = producer_id,
            .block = source_id,
            .operation = .{ .protected_call = .{
                .callee = callee,
                .arguments = &.{ fixed_status, fixed_payload },
                .result_arity = .{ .variadic = {} },
            } },
            .results = &.{},
            .pack_result = producer_pack,
            .effects = .protected_invocation,
            .evidence = &.{evidence_id},
        },
        .{
            .id = forward_id,
            .block = source_id,
            .operation = .{ .protected_call = .{
                .callee = callee,
                .error_handler = source_handler,
                .arguments = &.{source_argument},
                .argument_pack = producer_pack,
                .result_arity = .{ .variadic = {} },
            } },
            .results = &.{},
            .pack_result = forwarded_pack,
            .effects = .protected_invocation,
            .evidence = &.{evidence_id},
        },
        .{
            .id = adjust_id,
            .block = source_id,
            .operation = .{ .adjust_pack = forwarded_pack },
            .results = &.{ adjusted_status, adjusted_payload },
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
    };
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{ source_handler, source_argument },
        .instructions = &.{ fixed_id, producer_id, forward_id, adjust_id },
        .terminator = .{ .return_values = &.{ adjusted_status, adjusted_payload } },
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
        .locator = "fixture:protected-call-node-split",
    }};
    var source_program: ir.Program = .{
        .program_id = "protected-call-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
        .value_packs = &base_packs,
        .evidence = &evidence,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&source_program, source));

    var changed_values = base_values;
    changed_values[fixed_status.index()].type = .integer;
    source_program.values = &changed_values;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.values = &base_values;
    var changed_packs = base_packs;
    const invalid_prefix = [_]ir.ValueType{ .integer, .string };
    changed_packs[producer_pack.index()].shape.prefix = &invalid_prefix;
    source_program.value_packs = &changed_packs;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.value_packs = &base_packs;
    var changed_instructions = base_instructions;
    changed_instructions[fixed_id.index()].operation.protected_call.error_handler = fixed_status;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[fixed_id.index()].operation.protected_call.argument_pack = producer_pack;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[fixed_id.index()].operation.protected_call.result_arity = .{ .fixed = 0 };
    changed_instructions[fixed_id.index()].results = &.{};
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[fixed_id.index()].effects = .pure;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.instructions = &base_instructions;
    var reordered = source;
    reordered.instructions = &.{ fixed_id, forward_id, producer_id, adjust_id };
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
    try std.testing.expectEqual(@as(usize, 6), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_packs);
    try std.testing.expectEqual(@as(usize, 4), cloned.cloned_instructions);

    const clone_fixed = ir.InstructionId.fromIndex(4);
    const clone_producer = ir.InstructionId.fromIndex(5);
    const clone_forward = ir.InstructionId.fromIndex(6);
    const clone_adjust = ir.InstructionId.fromIndex(7);
    const clone_handler = ir.ValueId.fromIndex(7);
    const clone_argument = ir.ValueId.fromIndex(8);
    const clone_fixed_status = ir.ValueId.fromIndex(9);
    const clone_fixed_payload = ir.ValueId.fromIndex(10);
    const clone_adjusted_status = ir.ValueId.fromIndex(11);
    const clone_adjusted_payload = ir.ValueId.fromIndex(12);
    const clone_producer_pack = ir.ValuePackId.fromIndex(3);
    const clone_forwarded_pack = ir.ValuePackId.fromIndex(4);
    try std.testing.expectEqual(clone_handler, instructions.items[clone_fixed.index()].operation.protected_call.error_handler.?);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_argument}, instructions.items[clone_fixed.index()].operation.protected_call.arguments);
    try std.testing.expectEqual(vararg_pack, instructions.items[clone_fixed.index()].operation.protected_call.argument_pack.?);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ clone_fixed_status, clone_fixed_payload }, instructions.items[clone_fixed.index()].results);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_fixed_status, clone_fixed_payload },
        instructions.items[clone_producer.index()].operation.protected_call.arguments,
    );
    try std.testing.expectEqual(clone_handler, instructions.items[clone_forward.index()].operation.protected_call.error_handler.?);
    try std.testing.expectEqual(clone_producer_pack, instructions.items[clone_forward.index()].operation.protected_call.argument_pack.?);
    try std.testing.expectEqual(clone_producer_pack, instructions.items[clone_producer.index()].pack_result.?);
    try std.testing.expectEqual(clone_forwarded_pack, instructions.items[clone_forward.index()].pack_result.?);
    try std.testing.expectEqual(clone_forwarded_pack, instructions.items[clone_adjust.index()].operation.adjust_pack);
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
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{ source_handler, source_argument } };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_fixed = instructions.items[clone_fixed.index()];
    instructions.items[clone_fixed.index()].operation.protected_call.error_handler = null;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_fixed.index()] = saved_fixed;

    instructions.items[clone_fixed.index()].operation.protected_call.error_handler = source_handler;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_fixed.index()] = saved_fixed;

    instructions.items[clone_fixed.index()].operation.protected_call.argument_pack = null;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_fixed.index()] = saved_fixed;

    const saved_producer = instructions.items[clone_producer.index()];
    instructions.items[clone_producer.index()].operation.protected_call.error_handler = clone_handler;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_producer.index()] = saved_producer;

    const saved_forward = instructions.items[clone_forward.index()];
    instructions.items[clone_forward.index()].operation.protected_call.argument_pack = producer_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_forward.index()] = saved_forward;

    instructions.items[clone_forward.index()].pack_result = forwarded_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_forward.index()] = saved_forward;

    const saved_pack = packs.items[clone_forwarded_pack.index()];
    packs.items[clone_forwarded_pack.index()].shape.prefix = &invalid_prefix;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    packs.items[clone_forwarded_pack.index()] = saved_pack;

    instructions.items[clone_forward.index()].effects = .pure;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}
