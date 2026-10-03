const std = @import("std");
const ir = @import("ir.zig");
const node_split = @import("node_split.zig");
const node_split_instruction = @import("node_split_instruction.zig");
const solver_equivalence = @import("solver_equivalence.zig");

test "function reference clones retain declared function identity" {
    const fixture = @import("fixtures.zig").function_reference_module;
    const source = fixture.blocks[fixture.b_entry.index()];
    const clone_id = ir.BlockId.fromIndex(fixture.blocks.len);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var values: std.ArrayList(ir.Value) = .empty;
    try values.appendSlice(allocator, &fixture.values);
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    var instructions: std.ArrayList(ir.Instruction) = .empty;
    try instructions.appendSlice(allocator, &fixture.instructions);
    const cloned = try node_split.cloneBlockInArena(
        allocator,
        &fixture.program,
        &instructions,
        &values,
        &packs,
        source,
        clone_id,
    );
    try std.testing.expectEqual(@as(usize, 4), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 4), cloned.cloned_instructions);

    const clone_left_a = ir.ValueId.fromIndex(fixture.values.len);
    const clone_left_b = ir.ValueId.fromIndex(fixture.values.len + 1);
    const clone_left_copy = ir.ValueId.fromIndex(fixture.values.len + 2);
    const clone_right = ir.ValueId.fromIndex(fixture.values.len + 3);
    const blocks = fixture.blocks ++ [_]ir.Block{cloned.block};
    var program = fixture.program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    for ([_]struct { source: ir.ValueId, clone: ir.ValueId }{
        .{ .source = fixture.v_left_a, .clone = clone_left_a },
        .{ .source = fixture.v_left_b, .clone = clone_left_b },
        .{ .source = fixture.v_left_copy, .clone = clone_left_copy },
        .{ .source = fixture.v_right, .clone = clone_right },
    }) |pair| {
        try std.testing.expectEqual(
            solver_equivalence.DynamicRelation.equivalent,
            solver_equivalence.dynamicDescriptorRelation(
                solver_equivalence.dynamicValueDescriptor(&program, pair.source).?,
                solver_equivalence.dynamicValueDescriptor(&program, pair.clone).?,
            ),
        );
    }
    try std.testing.expectEqual(
        solver_equivalence.DynamicRelation.distinct,
        solver_equivalence.dynamicDescriptorRelation(
            solver_equivalence.dynamicValueDescriptor(&program, clone_left_a).?,
            solver_equivalence.dynamicValueDescriptor(&program, clone_right).?,
        ),
    );
}

test "runtime shift clones retain and compare semantic behavior" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };
    var source_values = fixture.values;
    source_values[fixture.v_left.index()].type = u32_type;
    source_values[fixture.v_right.index()].type = u32_type;
    source_values[fixture.v_sum.index()].type = u32_type;
    source_values[fixture.v_factor.index()].type = u32_type;
    source_values[fixture.v_result.index()].type = u32_type;
    var source_instructions = fixture.instructions;
    source_instructions[fixture.i_sum.index()].operation = .{ .binary = .{
        .operator = .shift_left,
        .left = fixture.v_left,
        .right = fixture.v_right,
        .mode = .primitive,
        .shift_behavior = .zero_saturating,
    } };
    var source_program = fixture.program;
    source_program.values = &source_values;
    source_program.instructions = &source_instructions;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var values: std.ArrayList(ir.Value) = .empty;
    try values.appendSlice(allocator, &source_values);
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    var instructions: std.ArrayList(ir.Instruction) = .empty;
    try instructions.appendSlice(allocator, &source_instructions);
    const cloned = try node_split.cloneBlockInArena(
        allocator,
        &source_program,
        &instructions,
        &values,
        &packs,
        fixture.blocks[fixture.b_add.index()],
        ir.BlockId.fromIndex(fixture.blocks.len),
    );
    const cloned_shift = instructions.items[cloned.block.instructions[0].index()].operation;
    try std.testing.expectEqual(ir.ShiftBehavior.zero_saturating, cloned_shift.binary.shift_behavior.?);

    var different_behavior = cloned_shift;
    different_behavior.binary.shift_behavior = .luau_bit32;
    try std.testing.expect(!node_split_instruction.sameOperation(cloned_shift, different_behavior));
}

test "semantic dynamic operators clone only with their complete effect boundary" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const negated = ir.ValueId.fromIndex(2);
    const result = ir.ValueId.fromIndex(3);
    const negate_id = ir.InstructionId.fromIndex(0);
    const add_id = ir.InstructionId.fromIndex(1);
    const source = ir.Block{
        .id = source_id,
        .function = function_id,
        .instructions = &.{ negate_id, add_id },
        .terminator = .{ .return_values = &.{result} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ left, right },
        .blocks = &.{source_id},
        .entry_block = source_id,
    }};
    const values = [_]ir.Value{
        .{ .id = left, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = right, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = negated, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = negate_id, .index = 0 } } },
        .{ .id = result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = add_id, .index = 0 } } },
    };
    const base_instructions = [_]ir.Instruction{
        .{
            .id = negate_id,
            .block = source_id,
            .operation = .{ .unary = .{ .operator = .negate, .operand = left, .mode = .semantic } },
            .results = &.{negated},
            .effects = .dynamic_call,
        },
        .{
            .id = add_id,
            .block = source_id,
            .operation = .{ .binary = .{ .operator = .add, .left = negated, .right = right, .mode = .semantic } },
            .results = &.{result},
            .effects = .dynamic_call,
        },
    };
    var program: ir.Program = .{
        .program_id = "semantic-dynamic-operator-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &values,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&program, source));

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var cloned_values: std.ArrayList(ir.Value) = .empty;
    try cloned_values.appendSlice(allocator, &values);
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    var cloned_instructions: std.ArrayList(ir.Instruction) = .empty;
    try cloned_instructions.appendSlice(allocator, &base_instructions);
    const cloned = try node_split.cloneBlockInArena(
        allocator,
        &program,
        &cloned_instructions,
        &cloned_values,
        &packs,
        source,
        clone_id,
    );
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_instructions);
    try std.testing.expect(node_split_instruction.sameOperation(
        base_instructions[negate_id.index()].operation,
        cloned_instructions.items[cloned.block.instructions[0].index()].operation,
    ));
    try std.testing.expect(node_split_instruction.sameEffects(
        ir.EffectSummary.dynamic_call,
        cloned_instructions.items[cloned.block.instructions[0].index()].effects,
    ));

    var refused_instructions = base_instructions;
    refused_instructions[negate_id.index()].effects = .pure;
    program.instructions = &refused_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, source));
    refused_instructions = base_instructions;
    refused_instructions[negate_id.index()].operation.unary.mode = .primitive;
    program.instructions = &refused_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, source));
}

test "lexical place reads require canonical local or captured ownership" {
    const parent_id = ir.FunctionId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(1);
    const parent_block_id = ir.BlockId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(1);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const result_id = ir.ValueId.fromIndex(0);
    const place_id = ir.PlaceId.fromIndex(0);
    const capture_id = ir.CaptureId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = parent_block_id, .function = parent_id, .terminator = .{ .return_values = &.{} } },
        .{
            .id = source_id,
            .function = function_id,
            .instructions = &.{instruction_id},
            .terminator = .{ .return_values = &.{result_id} },
        },
    };
    const base_functions = [_]ir.Function{
        .{ .id = parent_id, .blocks = &.{parent_block_id}, .entry_block = parent_block_id },
        .{
            .id = function_id,
            .lexical_parent = parent_id,
            .captures = &.{capture_id},
            .blocks = &.{source_id},
            .entry_block = source_id,
        },
    };
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = source_id,
        .operation = .{ .place_read = place_id },
        .results = &.{result_id},
        .effects = .place_read,
    }};
    const values = [_]ir.Value{.{
        .id = result_id,
        .function = function_id,
        .type = .integer,
        .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } },
    }};
    const base_places = [_]ir.Place{.{
        .id = place_id,
        .function = function_id,
        .type = .integer,
        .origin = .{ .capture = capture_id },
    }};
    const base_captures = [_]ir.Capture{.{
        .id = capture_id,
        .function = function_id,
        .kind = .{ .shared_place = place_id },
    }};
    var program: ir.Program = .{
        .program_id = "canonical-node-split-place",
        .entry_function = parent_id,
        .functions = &base_functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &base_places,
        .captures = &base_captures,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&program, blocks[source_id.index()]));

    var changed_functions = base_functions;
    changed_functions[function_id.index()].captures = &.{};
    program.functions = &changed_functions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, blocks[source_id.index()]));

    changed_functions = base_functions;
    changed_functions[function_id.index()].captures = &.{ capture_id, capture_id };
    program.functions = &changed_functions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, blocks[source_id.index()]));

    program.functions = &base_functions;
    var changed_captures = base_captures;
    changed_captures[capture_id.index()].kind = .{ .immutable_value = result_id };
    program.captures = &changed_captures;
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, blocks[source_id.index()]));

    changed_captures = base_captures;
    changed_captures[capture_id.index()].function = parent_id;
    program.captures = &changed_captures;
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, blocks[source_id.index()]));

    program.captures = &base_captures;
    var local_places = base_places;
    local_places[place_id.index()].origin = .{ .local = 0 };
    changed_functions = base_functions;
    changed_functions[function_id.index()].captures = &.{};
    changed_functions[function_id.index()].local_places = &.{place_id};
    program.functions = &changed_functions;
    program.places = &local_places;
    try std.testing.expect(node_split.instructionsAreCloneable(&program, blocks[source_id.index()]));

    changed_functions[function_id.index()].local_places = &.{ place_id, place_id };
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, blocks[source_id.index()]));
}

test "zero-result place writes clone ordered effects without value identities" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const source_parameter = ir.ValueId.fromIndex(0);
    const source_result = ir.ValueId.fromIndex(1);
    const write_id = ir.InstructionId.fromIndex(0);
    const read_id = ir.InstructionId.fromIndex(1);
    const place_id = ir.PlaceId.fromIndex(0);
    const source = ir.Block{
        .id = source_id,
        .function = function_id,
        .parameters = &.{source_parameter},
        .instructions = &.{ write_id, read_id },
        .terminator = .{ .return_values = &.{source_result} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .local_places = &.{place_id},
        .blocks = &.{source_id},
        .entry_block = source_id,
    }};
    const base_values = [_]ir.Value{
        .{ .id = source_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = source_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } } },
    };
    const base_instructions = [_]ir.Instruction{
        .{
            .id = write_id,
            .block = source_id,
            .operation = .{ .place_write = .{ .place = place_id, .value = source_parameter } },
            .results = &.{},
            .effects = .place_write,
        },
        .{
            .id = read_id,
            .block = source_id,
            .operation = .{ .place_read = place_id },
            .results = &.{source_result},
            .effects = .place_read,
        },
    };
    const places = [_]ir.Place{.{
        .id = place_id,
        .function = function_id,
        .type = .integer,
        .origin = .{ .local = 0 },
    }};
    const source_program: ir.Program = .{
        .program_id = "zero-result-place-write-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
        .places = &places,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&source_program, source));

    var ambient_instructions = base_instructions;
    ambient_instructions[write_id.index()].operation = .{ .environment_set = .{
        .target = .{ .ambient = {} },
        .name = "observed",
        .value = source_parameter,
        .mode = .semantic,
    } };
    ambient_instructions[write_id.index()].effects = .semantic_environment_write;
    var ambient_program = source_program;
    ambient_program.instructions = &ambient_instructions;
    try std.testing.expect(node_split.instructionsAreCloneable(&ambient_program, source));
    ambient_instructions[write_id.index()].operation.environment_set.mode = .raw;
    ambient_instructions[write_id.index()].effects = .raw_table_write;
    try std.testing.expect(!node_split.instructionsAreCloneable(&ambient_program, source));

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
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_instructions);

    const clone_parameter = ir.ValueId.fromIndex(2);
    const clone_result = ir.ValueId.fromIndex(3);
    const clone_write_id = ir.InstructionId.fromIndex(2);
    const clone_read_id = ir.InstructionId.fromIndex(3);
    try std.testing.expectEqual(@as(usize, 0), instructions.items[clone_write_id.index()].results.len);
    try std.testing.expectEqual(place_id, instructions.items[clone_write_id.index()].operation.place_write.place);
    try std.testing.expectEqual(clone_parameter, instructions.items[clone_write_id.index()].operation.place_write.value);
    try std.testing.expectEqual(clone_result, instructions.items[clone_read_id.index()].results[0]);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_result}, cloned.block.terminator.return_values);

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{source_parameter} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_write = instructions.items[clone_write_id.index()];
    instructions.items[clone_write_id.index()].operation.place_write.value = source_parameter;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_write_id.index()] = saved_write;

    instructions.items[clone_write_id.index()].effects = .pure;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_write_id.index()] = saved_write;

    instructions.items[clone_write_id.index()].results = &.{clone_result};
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}

test "entry external captures are clone-safe only through canonical bindings" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const value_id = ir.ValueId.fromIndex(0);
    const place_id = ir.PlaceId.fromIndex(0);
    const capture_id = ir.CaptureId.fromIndex(0);
    const binding_id = ir.ExternalBindingId.fromIndex(0);
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{instruction_id},
        .terminator = .{ .return_values = &.{} },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .captures = &.{capture_id},
        .local_places = &.{place_id},
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = block_id,
        .operation = .{ .place_write = .{ .place = place_id, .value = value_id } },
        .results = &.{},
        .effects = .place_write,
    }};
    const values = [_]ir.Value{.{
        .id = value_id,
        .function = function_id,
        .type = .integer,
        .origin = .{ .capture = capture_id },
    }};
    const places = [_]ir.Place{.{
        .id = place_id,
        .function = function_id,
        .type = .integer,
        .origin = .{ .local = 0 },
    }};
    const captures = [_]ir.Capture{.{
        .id = capture_id,
        .function = function_id,
        .kind = .{ .immutable_value = value_id },
    }};
    const bindings = [_]ir.ExternalBinding{.{
        .id = binding_id,
        .kind = .immutable_value,
        .type = .integer,
    }};
    var program: ir.Program = .{
        .program_id = "entry-binding-node-split",
        .entry_function = function_id,
        .entry_bindings = &.{binding_id},
        .external_bindings = &bindings,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
        .captures = &captures,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&program, blocks[0]));

    program.entry_bindings = &.{};
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, blocks[0]));

    program.entry_bindings = &.{binding_id};
    var mismatched_bindings = bindings;
    mismatched_bindings[0].kind = .shared_place;
    program.external_bindings = &mismatched_bindings;
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, blocks[0]));

    mismatched_bindings = bindings;
    mismatched_bindings[0].type = .number;
    program.external_bindings = &mismatched_bindings;
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, blocks[0]));
}

test "only canonical pure entry constants are reusable by a cloned block" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(1);
    const constant_id = ir.InstructionId.fromIndex(0);
    const copy_id = ir.InstructionId.fromIndex(1);
    const constant_value = ir.ValueId.fromIndex(0);
    const copied_value = ir.ValueId.fromIndex(1);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{constant_id}, .terminator = .{ .jump = .{ .target = source_id } } },
        .{ .id = source_id, .function = function_id, .instructions = &.{copy_id}, .terminator = .{ .return_values = &.{copied_value} } },
    };
    var functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ entry, source_id },
        .entry_block = entry,
    }};
    var instructions = [_]ir.Instruction{
        .{ .id = constant_id, .block = entry, .operation = .{ .constant = .{ .number = 41 } }, .results = &.{constant_value}, .effects = .pure },
        .{ .id = copy_id, .block = source_id, .operation = .{ .copy = constant_value }, .results = &.{copied_value}, .effects = .pure },
    };
    const values = [_]ir.Value{
        .{ .id = constant_value, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = constant_id, .index = 0 } } },
        .{ .id = copied_value, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = copy_id, .index = 0 } } },
    };
    var program: ir.Program = .{
        .program_id = "entry-constant-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    try std.testing.expect(node_split_instruction.sequenceIsCloneable(&program, blocks[1]));

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var clone_instructions: std.ArrayList(ir.Instruction) = .empty;
    try clone_instructions.appendSlice(arena.allocator(), &instructions);
    var clone_values: std.ArrayList(ir.Value) = .empty;
    try clone_values.appendSlice(arena.allocator(), &values);
    var clone_packs: std.ArrayList(ir.ValuePack) = .empty;
    const clone_id = ir.BlockId.fromIndex(blocks.len);
    const cloned = try node_split.cloneBlockInArena(
        arena.allocator(),
        &program,
        &clone_instructions,
        &clone_values,
        &clone_packs,
        blocks[1],
        clone_id,
    );
    const cloned_copy_id = cloned.block.instructions[0];
    try std.testing.expectEqual(constant_value, clone_instructions.items[cloned_copy_id.index()].operation.copy);

    const parameter = ir.ValueId.fromIndex(values.len);
    const parameters = [_]ir.ValueId{parameter};
    var parameter_values = values ++ [_]ir.Value{.{
        .id = parameter,
        .function = function_id,
        .type = .number,
        .origin = .{ .parameter = 0 },
    }};
    functions[0].parameters = &parameters;
    instructions[0].operation = .{ .copy = parameter };
    program.values = &parameter_values;
    program.instructions = &instructions;
    try std.testing.expect(!node_split_instruction.sequenceIsCloneable(&program, blocks[1]));

    const non_entry = ir.BlockId.fromIndex(2);
    const non_entry_blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = non_entry } } },
        blocks[1],
        .{ .id = non_entry, .function = function_id, .instructions = &.{constant_id}, .terminator = .{ .jump = .{ .target = source_id } } },
    };
    functions[0].parameters = &.{};
    functions[0].blocks = &.{ entry, source_id, non_entry };
    instructions[0] = .{ .id = constant_id, .block = non_entry, .operation = .{ .constant = .{ .number = 41 } }, .results = &.{constant_value}, .effects = .pure };
    program.functions = &functions;
    program.blocks = &non_entry_blocks;
    program.instructions = &instructions;
    program.values = &values;
    try std.testing.expect(!node_split_instruction.sequenceIsCloneable(&program, non_entry_blocks[1]));
}

test "fixed zero-result calls require explicit operands arity and full dynamic effects" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const call_id = ir.InstructionId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(0);
    const argument = ir.ValueId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = argument, .function = function_id, .origin = .{ .parameter = 1 } },
    };
    const base_instructions = [_]ir.Instruction{.{
        .id = call_id,
        .block = block_id,
        .operation = .{ .call = .{
            .callee = callee,
            .arguments = &.{argument},
            .result_arity = .{ .fixed = 0 },
        } },
        .results = &.{},
        .effects = .dynamic_call,
    }};
    const block: ir.Block = .{
        .id = block_id,
        .function = function_id,
        .instructions = &.{call_id},
        .terminator = .{ .return_values = &.{} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ callee, argument },
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    var program: ir.Program = .{
        .program_id = "fixed-zero-result-call-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{block},
        .instructions = &base_instructions,
        .values = &values,
    };
    try std.testing.expect(node_split.instructionsAreCloneable(&program, block));

    var changed = base_instructions;
    changed[call_id.index()].effects = .pure;
    program.instructions = &changed;
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, block));

    changed = base_instructions;
    changed[call_id.index()].operation.call.result_arity = .{ .variadic = {} };
    program.instructions = &changed;
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, block));

    changed = base_instructions;
    changed[call_id.index()].operation.call.result_arity = .{ .fixed = 2 };
    program.instructions = &changed;
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, block));

    changed = base_instructions;
    changed[call_id.index()].operation.call.argument_pack = ir.ValuePackId.fromIndex(0);
    program.instructions = &changed;
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, block));

    changed = base_instructions;
    changed[call_id.index()].claims = &.{ir.ClaimId.fromIndex(0)};
    program.instructions = &changed;
    try std.testing.expect(!node_split.instructionsAreCloneable(&program, block));
}

test "fixed call replay maps every multi-result position into downstream uses" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const first_call_id = ir.InstructionId.fromIndex(0);
    const second_call_id = ir.InstructionId.fromIndex(1);
    const callee = ir.ValueId.fromIndex(0);
    const external_argument = ir.ValueId.fromIndex(1);
    const source_parameter = ir.ValueId.fromIndex(2);
    const source_first_result = ir.ValueId.fromIndex(3);
    const source_second_result = ir.ValueId.fromIndex(4);
    const base_values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = external_argument, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = source_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = source_first_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = first_call_id, .index = 0 } } },
        .{ .id = source_second_result, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = first_call_id, .index = 1 } } },
    };
    const base_instructions = [_]ir.Instruction{
        .{
            .id = first_call_id,
            .block = source_id,
            .operation = .{ .call = .{
                .callee = callee,
                .arguments = &.{source_parameter},
                .result_arity = .{ .fixed = 2 },
            } },
            .results = &.{ source_first_result, source_second_result },
            .effects = .dynamic_call,
        },
        .{
            .id = second_call_id,
            .block = source_id,
            .operation = .{ .call = .{
                .callee = callee,
                .arguments = &.{ source_second_result, source_first_result },
                .result_arity = .{ .fixed = 0 },
            } },
            .results = &.{},
            .effects = .dynamic_call,
        },
    };
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{source_parameter},
        .instructions = &.{ first_call_id, second_call_id },
        .terminator = .{ .return_values = &.{ source_first_result, source_second_result } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ callee, external_argument },
        .blocks = &.{source_id},
        .entry_block = source_id,
    }};
    const source_program: ir.Program = .{
        .program_id = "fixed-call-chain-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &.{source},
        .instructions = &base_instructions,
        .values = &base_values,
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
    try std.testing.expectEqual(@as(usize, 3), cloned.cloned_values);
    try std.testing.expectEqual(@as(usize, 2), cloned.cloned_instructions);

    const clone_parameter = ir.ValueId.fromIndex(5);
    const clone_first_result = ir.ValueId.fromIndex(6);
    const clone_second_result = ir.ValueId.fromIndex(7);
    const clone_first_call = ir.InstructionId.fromIndex(2);
    const clone_second_call = ir.InstructionId.fromIndex(3);
    try std.testing.expectEqual(callee, instructions.items[clone_first_call.index()].operation.call.callee);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_parameter}, instructions.items[clone_first_call.index()].operation.call.arguments);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_first_result, clone_second_result },
        instructions.items[clone_first_call.index()].results,
    );
    try std.testing.expectEqualSlices(
        ir.ValueId,
        &.{ clone_second_result, clone_first_result },
        instructions.items[clone_second_call.index()].operation.call.arguments,
    );
    try std.testing.expectEqual(@as(usize, 0), instructions.items[clone_second_call.index()].results.len);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ clone_first_result, clone_second_result }, cloned.block.terminator.return_values);
    try std.testing.expectEqual(@as(u16, 0), values.items[clone_first_result.index()].origin.instruction_result.index);
    try std.testing.expectEqual(@as(u16, 1), values.items[clone_second_result.index()].origin.instruction_result.index);

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{external_argument} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_first = instructions.items[clone_first_call.index()];
    instructions.items[clone_first_call.index()].operation.call.arguments = &.{source_parameter};
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_first_call.index()] = saved_first;

    instructions.items[clone_first_call.index()].operation.call.result_arity = .{ .fixed = 1 };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_first_call.index()] = saved_first;

    const saved_second = instructions.items[clone_second_call.index()];
    instructions.items[clone_second_call.index()].operation.call.arguments = &.{ clone_first_result, clone_second_result };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_second_call.index()] = saved_second;

    instructions.items[clone_second_call.index()].effects = .pure;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_second_call.index()] = saved_second;

    const saved_second_value = values.items[clone_second_result.index()];
    values.items[clone_second_result.index()].type = .number;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    values.items[clone_second_result.index()] = saved_second_value;

    values.items[clone_second_result.index()].origin.instruction_result.index = 0;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}
