const std = @import("std");
const ir = @import("ir.zig");
const node_split = @import("node_split.zig");

test "closures replay exact ordered value and shared-place captures" {
    const parent_id = ir.FunctionId.fromIndex(0);
    const child_id = ir.FunctionId.fromIndex(1);
    const source_id = ir.BlockId.fromIndex(0);
    const child_block_id = ir.BlockId.fromIndex(1);
    const clone_id = ir.BlockId.fromIndex(2);
    const constant_id = ir.InstructionId.fromIndex(0);
    const closure_id = ir.InstructionId.fromIndex(1);
    const external_value = ir.ValueId.fromIndex(0);
    const source_parameter = ir.ValueId.fromIndex(1);
    const constant_value = ir.ValueId.fromIndex(2);
    const closure_value = ir.ValueId.fromIndex(3);
    const captured_constant = ir.ValueId.fromIndex(4);
    const captured_parameter = ir.ValueId.fromIndex(5);
    const captured_external = ir.ValueId.fromIndex(6);
    const local_place = ir.PlaceId.fromIndex(0);
    const captured_place = ir.PlaceId.fromIndex(1);
    const constant_capture = ir.CaptureId.fromIndex(0);
    const place_capture = ir.CaptureId.fromIndex(1);
    const parameter_capture = ir.CaptureId.fromIndex(2);
    const external_capture = ir.CaptureId.fromIndex(3);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const invalid_evidence_id = ir.EvidenceId.fromIndex(1);
    const bindings = [_]ir.CaptureBinding{
        .{ .value = constant_value },
        .{ .place = local_place },
        .{ .value = source_parameter },
        .{ .value = external_value },
    };
    const base_values = [_]ir.Value{
        .{ .id = external_value, .function = parent_id, .type = .string, .origin = .{ .parameter = 0 } },
        .{ .id = source_parameter, .function = parent_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = constant_value, .function = parent_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = constant_id, .index = 0 } } },
        .{ .id = closure_value, .function = parent_id, .type = .function, .origin = .{ .instruction_result = .{ .instruction = closure_id, .index = 0 } } },
        .{ .id = captured_constant, .function = child_id, .type = .integer, .origin = .{ .capture = constant_capture } },
        .{ .id = captured_parameter, .function = child_id, .type = .integer, .origin = .{ .capture = parameter_capture } },
        .{ .id = captured_external, .function = child_id, .type = .string, .origin = .{ .capture = external_capture } },
    };
    const places = [_]ir.Place{
        .{ .id = local_place, .function = parent_id, .type = .integer, .origin = .{ .local = 0 }, .evidence = &.{evidence_id} },
        .{ .id = captured_place, .function = child_id, .type = .integer, .origin = .{ .capture = place_capture }, .evidence = &.{evidence_id} },
    };
    const captures = [_]ir.Capture{
        .{ .id = constant_capture, .function = child_id, .kind = .{ .immutable_value = captured_constant }, .evidence = &.{evidence_id} },
        .{ .id = place_capture, .function = child_id, .kind = .{ .shared_place = captured_place }, .evidence = &.{evidence_id} },
        .{ .id = parameter_capture, .function = child_id, .kind = .{ .immutable_value = captured_parameter }, .evidence = &.{evidence_id} },
        .{ .id = external_capture, .function = child_id, .kind = .{ .immutable_value = captured_external }, .evidence = &.{evidence_id} },
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
            .id = closure_id,
            .block = source_id,
            .operation = .{ .make_closure = .{ .function = child_id, .bindings = &bindings } },
            .results = &.{closure_value},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
    };
    const source: ir.Block = .{
        .id = source_id,
        .function = parent_id,
        .parameters = &.{source_parameter},
        .instructions = &.{ constant_id, closure_id },
        .terminator = .{ .return_values = &.{closure_value} },
        .evidence = &.{evidence_id},
    };
    const child_block: ir.Block = .{
        .id = child_block_id,
        .function = child_id,
        .terminator = .{ .return_values = &.{ captured_constant, captured_parameter, captured_external } },
        .evidence = &.{evidence_id},
    };
    const functions = [_]ir.Function{
        .{
            .id = parent_id,
            .parameters = &.{external_value},
            .local_places = &.{local_place},
            .blocks = &.{source_id},
            .entry_block = source_id,
            .evidence = &.{evidence_id},
        },
        .{
            .id = child_id,
            .lexical_parent = parent_id,
            .captures = &.{ constant_capture, place_capture, parameter_capture, external_capture },
            .blocks = &.{child_block_id},
            .entry_block = child_block_id,
            .evidence = &.{evidence_id},
        },
    };
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .structural_derivation,
        .locator = "fixture:closure-node-split",
    }};
    const blocks = [_]ir.Block{ source, child_block };
    var source_program: ir.Program = .{
        .program_id = "closure-node-split",
        .entry_function = parent_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &base_instructions,
        .values = &base_values,
        .places = &places,
        .captures = &captures,
        .evidence = &evidence,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&source_program, source));

    var changed_instructions = base_instructions;
    changed_instructions[closure_id.index()].operation.make_closure.bindings = &.{
        .{ .value = closure_value },
        .{ .place = local_place },
        .{ .value = source_parameter },
        .{ .value = external_value },
    };
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[closure_id.index()].operation.make_closure.bindings = &.{
        .{ .place = local_place },
        .{ .place = local_place },
        .{ .value = source_parameter },
        .{ .value = external_value },
    };
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[closure_id.index()].operation.make_closure.function = parent_id;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[closure_id.index()].effects = .dynamic_call;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.instructions = &base_instructions;
    var changed_values = base_values;
    changed_values[closure_value.index()].type = .integer;
    source_program.values = &changed_values;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_values = base_values;
    changed_values[captured_constant.index()].origin = .{ .capture = external_capture };
    source_program.values = &changed_values;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.values = &base_values;
    var changed_functions = functions;
    changed_functions[child_id.index()].evidence = &.{invalid_evidence_id};
    source_program.functions = &changed_functions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.functions = &functions;
    var changed_captures = captures;
    changed_captures[constant_capture.index()].evidence = &.{invalid_evidence_id};
    source_program.captures = &changed_captures;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.captures = &captures;
    var changed_places = places;
    changed_places[local_place.index()].origin = .{ .instruction = closure_id };
    source_program.places = &changed_places;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_places = places;
    changed_places[local_place.index()].evidence = &.{invalid_evidence_id};
    source_program.places = &changed_places;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_places = places;
    changed_places[captured_place.index()].evidence = &.{invalid_evidence_id};
    source_program.places = &changed_places;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.places = &places;
    var changed_evidence = evidence;
    changed_evidence[evidence_id.index()].locator = "";
    source_program.evidence = &changed_evidence;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.evidence = &evidence;
    source_program.places = &places;
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
    try std.testing.expectEqual(@as(usize, 3), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 0), cloned.cloned_packs);
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_instructions);

    const clone_constant = ir.InstructionId.fromIndex(2);
    const clone_closure = ir.InstructionId.fromIndex(3);
    const clone_parameter = ir.ValueId.fromIndex(7);
    const clone_constant_value = ir.ValueId.fromIndex(8);
    const clone_closure_value = ir.ValueId.fromIndex(9);
    const cloned_operation = instructions.items[clone_closure.index()].operation.make_closure;
    try std.testing.expect(cloned_operation.bindings.ptr != bindings[0..].ptr);
    try std.testing.expectEqual(child_id, cloned_operation.function);
    try std.testing.expectEqual(@as(usize, 4), cloned_operation.bindings.len);
    try std.testing.expectEqual(clone_constant_value, cloned_operation.bindings[0].value);
    try std.testing.expectEqual(local_place, cloned_operation.bindings[1].place);
    try std.testing.expectEqual(clone_parameter, cloned_operation.bindings[2].value);
    try std.testing.expectEqual(external_value, cloned_operation.bindings[3].value);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_closure_value}, cloned.block.terminator.return_values);

    const replay_blocks = [_]ir.Block{ source, child_block, cloned.block };
    var program = source_program;
    program.blocks = &replay_blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{source_parameter} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_closure = instructions.items[clone_closure.index()];
    instructions.items[clone_closure.index()].operation.make_closure.function = parent_id;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_closure.index()] = saved_closure;

    instructions.items[clone_closure.index()].operation.make_closure.bindings = &.{
        .{ .value = clone_parameter },
        .{ .place = local_place },
        .{ .value = clone_constant_value },
        .{ .value = external_value },
    };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_closure.index()] = saved_closure;

    instructions.items[clone_closure.index()].operation.make_closure.bindings = &bindings;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_closure.index()] = saved_closure;

    values.items[clone_closure_value.index()].type = .integer;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    values.items[clone_closure_value.index()] = base_values[closure_value.index()];
    values.items[clone_closure_value.index()].id = clone_closure_value;
    values.items[clone_closure_value.index()].origin = .{ .instruction_result = .{ .instruction = clone_closure, .index = 0 } };

    changed_captures = captures;
    changed_captures[place_capture.index()].evidence = &.{invalid_evidence_id};
    program.captures = &changed_captures;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    program.captures = &captures;

    instructions.items[clone_closure.index()].effects = .dynamic_call;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    try std.testing.expectEqual(clone_constant, values.items[clone_constant_value.index()].origin.instruction_result.instruction);
}
