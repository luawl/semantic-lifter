const std = @import("std");
const ir = @import("ir.zig");
const node_split = @import("node_split.zig");

test "string interpolation replays exact segments mapped values and dynamic effects" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const constant_id = ir.InstructionId.fromIndex(0);
    const first_id = ir.InstructionId.fromIndex(1);
    const second_id = ir.InstructionId.fromIndex(2);
    const external_value = ir.ValueId.fromIndex(0);
    const source_parameter = ir.ValueId.fromIndex(1);
    const constant_value = ir.ValueId.fromIndex(2);
    const first_value = ir.ValueId.fromIndex(3);
    const second_value = ir.ValueId.fromIndex(4);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const first_segments = [_][]const u8{ "prefix:", ":middle:", ":suffix" };
    const second_segments = [_][]const u8{ "", "%", "!" };
    const base_values = [_]ir.Value{
        .{ .id = external_value, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = source_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = constant_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = constant_id, .index = 0 } } },
        .{ .id = first_value, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = first_id, .index = 0 } } },
        .{ .id = second_value, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = second_id, .index = 0 } } },
    };
    const base_instructions = [_]ir.Instruction{
        .{
            .id = constant_id,
            .block = source_id,
            .operation = .{ .constant = .{ .integer = "7" } },
            .results = &.{constant_value},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
        .{
            .id = first_id,
            .block = source_id,
            .operation = .{ .string_interpolate = .{
                .segments = &first_segments,
                .values = &.{ source_parameter, constant_value },
            } },
            .results = &.{first_value},
            .effects = .string_interpolation,
            .evidence = &.{evidence_id},
        },
        .{
            .id = second_id,
            .block = source_id,
            .operation = .{ .string_interpolate = .{
                .segments = &second_segments,
                .values = &.{ first_value, external_value },
            } },
            .results = &.{second_value},
            .effects = .string_interpolation,
            .evidence = &.{evidence_id},
        },
    };
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{source_parameter},
        .instructions = &.{ constant_id, first_id, second_id },
        .terminator = .{ .return_values = &.{second_value} },
        .evidence = &.{evidence_id},
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{external_value},
        .blocks = &.{source_id},
        .entry_block = source_id,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .structural_derivation,
        .locator = "fixture:interpolation-node-split",
    }};
    var source_program: ir.Program = .{
        .program_id = "interpolation-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
        .evidence = &evidence,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&source_program, source));

    var changed_instructions = base_instructions;
    changed_instructions[first_id.index()].operation.string_interpolate.segments = &.{ "missing", "segment" };
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[first_id.index()].operation.string_interpolate.values = &.{ source_parameter, second_value };
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[first_id.index()].effects = .pure;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.instructions = &base_instructions;
    var changed_values = base_values;
    changed_values[first_value.index()].type = .integer;
    source_program.values = &changed_values;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.values = &base_values;
    var reordered = source;
    reordered.instructions = &.{ first_id, constant_id, second_id };
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, reordered));

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
    try std.testing.expectEqual(@as(usize, 4), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 0), cloned.cloned_packs);
    try std.testing.expectEqual(@as(usize, 3), cloned.cloned_instructions);

    const clone_constant = ir.InstructionId.fromIndex(3);
    const clone_first = ir.InstructionId.fromIndex(4);
    const clone_second = ir.InstructionId.fromIndex(5);
    const clone_parameter = ir.ValueId.fromIndex(5);
    const clone_constant_value = ir.ValueId.fromIndex(6);
    const clone_first_value = ir.ValueId.fromIndex(7);
    const clone_second_value = ir.ValueId.fromIndex(8);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_parameter, clone_constant_value },
        instructions.items[clone_first.index()].operation.string_interpolate.values,
    );
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_first_value, external_value },
        instructions.items[clone_second.index()].operation.string_interpolate.values,
    );
    for (first_segments, instructions.items[clone_first.index()].operation.string_interpolate.segments) |expected, actual| {
        try std.testing.expectEqualStrings(expected, actual);
    }
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_second_value}, cloned.block.terminator.return_values);

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{source_parameter} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_first = instructions.items[clone_first.index()];
    instructions.items[clone_first.index()].operation.string_interpolate.segments = &.{ "prefix:", ":changed:", ":suffix" };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_first.index()] = saved_first;

    instructions.items[clone_first.index()].operation.string_interpolate.values = &.{ clone_constant_value, clone_parameter };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_first.index()] = saved_first;

    instructions.items[clone_first.index()].operation.string_interpolate.values = &.{ source_parameter, clone_constant_value };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_first.index()] = saved_first;

    const saved_second = instructions.items[clone_second.index()];
    instructions.items[clone_second.index()].operation.string_interpolate.values = &.{ external_value, clone_first_value };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_second.index()] = saved_second;

    values.items[clone_second_value.index()].type = .integer;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    values.items[clone_second_value.index()] = base_values[second_value.index()];
    values.items[clone_second_value.index()].id = clone_second_value;
    values.items[clone_second_value.index()].origin = .{ .instruction_result = .{ .instruction = clone_second, .index = 0 } };

    instructions.items[clone_second.index()].effects = .pure;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);

    try std.testing.expectEqual(clone_constant, values.items[clone_constant_value.index()].origin.instruction_result.instruction);
}
