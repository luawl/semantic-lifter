const std = @import("std");
const ir = @import("ir.zig");
const node_split = @import("node_split.zig");
const solver_equivalence = @import("solver_equivalence.zig");

test "table constructors replay ordered fields and direct or local tail packs" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const clone_id = ir.BlockId.fromIndex(1);
    const empty_id = ir.InstructionId.fromIndex(0);
    const direct_id = ir.InstructionId.fromIndex(1);
    const producer_id = ir.InstructionId.fromIndex(2);
    const local_id = ir.InstructionId.fromIndex(3);
    const callee = ir.ValueId.fromIndex(0);
    const external_key = ir.ValueId.fromIndex(1);
    const source_parameter = ir.ValueId.fromIndex(2);
    const empty_table = ir.ValueId.fromIndex(3);
    const direct_table = ir.ValueId.fromIndex(4);
    const local_table = ir.ValueId.fromIndex(5);
    const vararg_pack = ir.ValuePackId.fromIndex(0);
    const producer_pack = ir.ValuePackId.fromIndex(1);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const producer_prefix = [_]ir.ValueType{ .integer, .{ .kind = .nil_value }, .integer };
    const direct_fields = [_]ir.TableConstructorField{
        .{ .list = source_parameter },
        .{ .keyed = .{ .key = external_key, .value = empty_table } },
    };
    const local_fields = [_]ir.TableConstructorField{
        .{ .list = direct_table },
        .{ .keyed = .{ .key = external_key, .value = source_parameter } },
    };
    const base_values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = external_key, .function = function_id, .type = .string, .origin = .{ .parameter = 1 } },
        .{ .id = source_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_id, .index = 0 } } },
        .{ .id = empty_table, .function = function_id, .type = .{ .kind = .table }, .origin = .{ .instruction_result = .{ .instruction = empty_id, .index = 0 } } },
        .{ .id = direct_table, .function = function_id, .type = .{ .kind = .table }, .origin = .{ .instruction_result = .{ .instruction = direct_id, .index = 0 } } },
        .{ .id = local_table, .function = function_id, .type = .{ .kind = .table }, .origin = .{ .instruction_result = .{ .instruction = local_id, .index = 0 } } },
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
    };
    const base_instructions = [_]ir.Instruction{
        .{
            .id = empty_id,
            .block = source_id,
            .operation = .{ .make_table = {} },
            .results = &.{empty_table},
            .effects = .table_constructor,
            .evidence = &.{evidence_id},
        },
        .{
            .id = direct_id,
            .block = source_id,
            .operation = .{ .make_table_literal = .{ .fields = &direct_fields, .tail_pack = vararg_pack } },
            .results = &.{direct_table},
            .effects = .table_constructor,
            .evidence = &.{evidence_id},
        },
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
            .id = local_id,
            .block = source_id,
            .operation = .{ .make_table_literal = .{ .fields = &local_fields, .tail_pack = producer_pack } },
            .results = &.{local_table},
            .effects = .table_constructor,
            .evidence = &.{evidence_id},
        },
    };
    const source: ir.Block = .{
        .id = source_id,
        .function = function_id,
        .parameters = &.{source_parameter},
        .instructions = &.{ empty_id, direct_id, producer_id, local_id },
        .terminator = .{ .return_values = &.{local_table} },
        .evidence = &.{evidence_id},
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ callee, external_key },
        .blocks = &.{source_id},
        .entry_block = source_id,
        .is_variadic = true,
        .vararg_pack = vararg_pack,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .structural_derivation,
        .locator = "fixture:table-constructor-node-split",
    }};
    var source_program: ir.Program = .{
        .program_id = "table-constructor-node-split",
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
    changed_values[empty_table.index()].type = .integer;
    source_program.values = &changed_values;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.values = &base_values;
    var changed_instructions = base_instructions;
    changed_instructions[empty_id.index()].effects = .pure;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    const future_fields = [_]ir.TableConstructorField{.{ .list = local_table }};
    changed_instructions = base_instructions;
    changed_instructions[direct_id.index()].operation.make_table_literal.fields = &future_fields;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    changed_instructions = base_instructions;
    changed_instructions[direct_id.index()].operation.make_table_literal.tail_pack = producer_pack;
    source_program.instructions = &changed_instructions;
    try std.testing.expect(!node_split.instructionsAreCloneable(&source_program, source));

    source_program.instructions = &base_instructions;
    var reordered = source;
    reordered.instructions = &.{ empty_id, direct_id, local_id, producer_id };
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
    try std.testing.expectEqual(@as(usize, 4), cloned.cloned_instructions);

    const clone_empty = ir.InstructionId.fromIndex(4);
    const clone_direct = ir.InstructionId.fromIndex(5);
    const clone_producer = ir.InstructionId.fromIndex(6);
    const clone_local = ir.InstructionId.fromIndex(7);
    const clone_parameter = ir.ValueId.fromIndex(6);
    const clone_empty_table = ir.ValueId.fromIndex(7);
    const clone_direct_table = ir.ValueId.fromIndex(8);
    const clone_local_table = ir.ValueId.fromIndex(9);
    const clone_producer_pack = ir.ValuePackId.fromIndex(2);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_empty_table}, instructions.items[clone_empty.index()].results);
    const cloned_direct = instructions.items[clone_direct.index()].operation.make_table_literal;
    try std.testing.expectEqual(clone_parameter, cloned_direct.fields[0].list);
    try std.testing.expectEqual(external_key, cloned_direct.fields[1].keyed.key);
    try std.testing.expectEqual(clone_empty_table, cloned_direct.fields[1].keyed.value);
    try std.testing.expectEqual(vararg_pack, cloned_direct.tail_pack.?);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_direct_table}, instructions.items[clone_direct.index()].results);
    try std.testing.expectEqual(clone_producer_pack, instructions.items[clone_producer.index()].pack_result.?);
    const cloned_local = instructions.items[clone_local.index()].operation.make_table_literal;
    try std.testing.expectEqual(clone_direct_table, cloned_local.fields[0].list);
    try std.testing.expectEqual(external_key, cloned_local.fields[1].keyed.key);
    try std.testing.expectEqual(clone_parameter, cloned_local.fields[1].keyed.value);
    try std.testing.expectEqual(clone_producer_pack, cloned_local.tail_pack.?);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_local_table}, cloned.block.terminator.return_values);

    const blocks = [_]ir.Block{ source, cloned.block };
    var program = source_program;
    program.blocks = &blocks;
    program.instructions = instructions.items;
    program.values = values.items;
    program.value_packs = packs.items;
    try std.testing.expectEqual(
        solver_equivalence.DynamicRelation.distinct,
        solver_equivalence.dynamicDescriptorRelation(
            solver_equivalence.dynamicValueDescriptor(&program, empty_table).?,
            solver_equivalence.dynamicValueDescriptor(&program, clone_empty_table).?,
        ),
    );
    try std.testing.expectEqual(
        solver_equivalence.DynamicRelation.distinct,
        solver_equivalence.dynamicDescriptorRelation(
            solver_equivalence.dynamicValueDescriptor(&program, direct_table).?,
            solver_equivalence.dynamicValueDescriptor(&program, clone_direct_table).?,
        ),
    );
    try std.testing.expectEqual(
        solver_equivalence.DynamicRelation.distinct,
        solver_equivalence.dynamicDescriptorRelation(
            solver_equivalence.dynamicValueDescriptor(&program, local_table).?,
            solver_equivalence.dynamicValueDescriptor(&program, clone_local_table).?,
        ),
    );
    const incoming: ir.Edge = .{ .target = source_id, .arguments = &.{source_parameter} };
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) != null);

    const saved_direct = instructions.items[clone_direct.index()];
    instructions.items[clone_direct.index()].operation.make_table_literal.fields = &direct_fields;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_direct.index()] = saved_direct;

    const swapped_fields = [_]ir.TableConstructorField{
        .{ .keyed = .{ .key = external_key, .value = clone_empty_table } },
        .{ .list = clone_parameter },
    };
    instructions.items[clone_direct.index()].operation.make_table_literal.fields = &swapped_fields;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_direct.index()] = saved_direct;

    instructions.items[clone_direct.index()].operation.make_table_literal.tail_pack = null;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_direct.index()] = saved_direct;

    const saved_local = instructions.items[clone_local.index()];
    instructions.items[clone_local.index()].operation.make_table_literal.tail_pack = producer_pack;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    instructions.items[clone_local.index()] = saved_local;

    values.items[clone_local_table.index()].type = .integer;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
    values.items[clone_local_table.index()] = base_values[local_table.index()];
    values.items[clone_local_table.index()].id = clone_local_table;
    values.items[clone_local_table.index()].origin = .{ .instruction_result = .{ .instruction = clone_local, .index = 0 } };

    instructions.items[clone_local.index()].effects = .pure;
    try std.testing.expect(try node_split.replayAlloc(allocator, &program, incoming, clone_id) == null);
}
