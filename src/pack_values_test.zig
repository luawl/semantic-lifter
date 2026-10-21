const std = @import("std");
const ir = @import("ir.zig");
const validation = @import("validate.zig");
const emitter = @import("emit_luau.zig");
const pack_plan = @import("pack_plan.zig");
const dead_code = @import("dead_code.zig");
const place_write_fusion = @import("place_write_fusion.zig");
const place_read_fusion = @import("place_read_fusion.zig");
const value_fusion = @import("value_fusion.zig");

const fixture = struct {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const integer_id = ir.ValueId.fromIndex(0);
    const string_id = ir.ValueId.fromIndex(1);
    const adjusted_integer = ir.ValueId.fromIndex(2);
    const adjusted_string = ir.ValueId.fromIndex(3);
    const adjusted_nil = ir.ValueId.fromIndex(4);
    const integer_instruction = ir.InstructionId.fromIndex(0);
    const string_instruction = ir.InstructionId.fromIndex(1);
    const pack_instruction = ir.InstructionId.fromIndex(2);
    const adjust_instruction = ir.InstructionId.fromIndex(3);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);

    const prefix = [_]ir.ValueType{ .integer, .string };
    const values = [_]ir.Value{
        .{ .id = integer_id, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = integer_instruction, .index = 0 } } },
        .{ .id = string_id, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = string_instruction, .index = 0 } } },
        .{ .id = adjusted_integer, .function = function_id, .type = .integer, .name_hint = "first", .origin = .{ .instruction_result = .{ .instruction = adjust_instruction, .index = 0 } } },
        .{ .id = adjusted_string, .function = function_id, .type = .string, .name_hint = "second", .origin = .{ .instruction_result = .{ .instruction = adjust_instruction, .index = 1 } } },
        .{ .id = adjusted_nil, .function = function_id, .type = .{ .kind = .nil_value }, .name_hint = "third", .origin = .{ .instruction_result = .{ .instruction = adjust_instruction, .index = 2 } } },
    };
    const packs = [_]ir.ValuePack{.{
        .id = pack_id,
        .function = function_id,
        .origin = .{ .instruction_result = pack_instruction },
        .shape = .{ .prefix = &prefix, .tail = .closed },
        .evidence = &.{proof},
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = integer_instruction, .block = block_id, .operation = .{ .constant = .{ .integer = "7" } }, .results = &.{integer_id}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = string_instruction, .block = block_id, .operation = .{ .constant = .{ .string = "x" } }, .results = &.{string_id}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = pack_instruction, .block = block_id, .operation = .{ .pack_values = &.{ integer_id, string_id } }, .results = &.{}, .pack_result = pack_id, .effects = .pure, .evidence = &.{proof} },
        .{ .id = adjust_instruction, .block = block_id, .operation = .{ .adjust_pack = pack_id }, .results = &.{ adjusted_integer, adjusted_string, adjusted_nil }, .effects = .pure, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ integer_instruction, string_instruction, pack_instruction, adjust_instruction },
        .terminator = .{ .return_values = &.{ adjusted_integer, adjusted_string, adjusted_nil } },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:pack-values" }};
    const program: ir.Program = .{
        .program_id = "pack-values",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
        .evidence = &evidence,
    };
};

fn expectDiagnostic(program: *const ir.Program, profile: ir.AdmissionProfile, code: @import("diagnostics.zig").Code) !void {
    var report = try validation.validate(std.testing.allocator, program, profile);
    defer report.deinit();
    try std.testing.expect(report.contains(code));
}

fn expectClean(program: *const ir.Program, profile: ir.AdmissionProfile) !void {
    var report = try validation.validate(std.testing.allocator, program, profile);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "pack values admission binds shape effects provenance and dominance" {
    try expectClean(&fixture.program, .core);
    try expectClean(&fixture.program, .readable_luau);

    const wrong_prefix = [_]ir.ValueType{ .string, .string };
    var packs = fixture.packs;
    packs[0].shape.prefix = &wrong_prefix;
    var program = fixture.program;
    program.value_packs = &packs;
    try expectDiagnostic(&program, .core, .invalid_value_pack_shape);

    var instructions = fixture.instructions;
    instructions[fixture.pack_instruction.index()].effects = .dynamic_call;
    program = fixture.program;
    program.instructions = &instructions;
    try expectDiagnostic(&program, .core, .invalid_pack_values_effects);

    packs = fixture.packs;
    packs[0].evidence = &.{};
    program = fixture.program;
    program.value_packs = &packs;
    try expectDiagnostic(&program, .core, .pack_values_evidence_mismatch);

    instructions = fixture.instructions;
    instructions[fixture.pack_instruction.index()].operation = .{ .pack_values = &.{} };
    packs = fixture.packs;
    packs[0].shape = .{ .prefix = &.{}, .tail = .closed };
    program = fixture.program;
    program.instructions = &instructions;
    program.value_packs = &packs;
    try expectDiagnostic(&program, .core, .empty_pack_values);

    var blocks = fixture.blocks;
    blocks[0].instructions = &.{ fixture.pack_instruction, fixture.integer_instruction, fixture.string_instruction, fixture.adjust_instruction };
    program = fixture.program;
    program.blocks = &blocks;
    try expectDiagnostic(&program, .core, .value_used_before_definition);

    blocks = fixture.blocks;
    blocks[0].terminator = .{ .return_expanded = .{ .values = &.{fixture.adjusted_integer}, .pack = fixture.pack_id } };
    program = fixture.program;
    program.blocks = &blocks;
    try expectClean(&program, .core);
    try expectClean(&program, .readable_luau);
    var fanout_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer fanout_plan.deinit();
    try std.testing.expect(fanout_plan.role(fixture.pack_instruction) == .materialized_pack_values_producer);
    try std.testing.expectEqual(
        pack_plan.InstructionRole{ .fused_pack_values_adjustment = fixture.pack_instruction },
        fanout_plan.role(fixture.adjust_instruction),
    );
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .fused_pack_values_return = fixture.pack_instruction },
        fanout_plan.terminatorRole(fixture.block_id),
    );
    const fanout_source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(fanout_source);
    try std.testing.expect(std.mem.indexOf(u8, fanout_source, "return first, 7, \"x\"") != null);
}

test "zero-width closed pack adjustment renders no statement" {
    var instructions = fixture.instructions;
    instructions[fixture.adjust_instruction.index()].results = &.{};
    var blocks = fixture.blocks;
    blocks[fixture.block_id.index()].terminator = .{ .return_values = &.{} };
    var program = fixture.program;
    program.instructions = &instructions;
    program.blocks = &blocks;
    program.values = fixture.values[0..2];

    try expectClean(&program, .core);
    try expectClean(&program, .readable_luau);
    var plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expect(plan.role(fixture.pack_instruction) == .materialized_pack_values_producer);
    try std.testing.expectEqual(
        pack_plan.InstructionRole{ .fused_pack_values_adjustment = fixture.pack_instruction },
        plan.role(fixture.adjust_instruction),
    );
    try std.testing.expect(plan.packValuesProjection(&program, fixture.pack_instruction) == null);

    const discarded_source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(discarded_source);
    try std.testing.expectEqualStrings("", discarded_source);

    blocks[fixture.block_id.index()].terminator = .{ .return_pack = fixture.pack_id };
    program.blocks = &blocks;
    try expectClean(&program, .readable_luau);
    var fanout_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer fanout_plan.deinit();
    try std.testing.expect(fanout_plan.role(fixture.pack_instruction) == .materialized_pack_values_producer);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .fused_pack_values_return = fixture.pack_instruction },
        fanout_plan.terminatorRole(fixture.block_id),
    );
    const fanout_source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(fanout_source);
    try std.testing.expect(std.mem.indexOf(u8, fanout_source, "return 7, \"x\"") != null);
}

test "pack values emit through adjustment return table and invocation consumers" {
    const adjusted_source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &fixture.program);
    defer std.testing.allocator.free(adjusted_source);
    try std.testing.expect(std.mem.indexOf(u8, adjusted_source, " = 7, \"x\"") != null);

    var return_instructions = fixture.instructions;
    return_instructions[fixture.adjust_instruction.index()] = .{
        .id = fixture.adjust_instruction,
        .block = fixture.block_id,
        .operation = .{ .environment_get = .{ .target = .ambient, .name = "pack_return_gap" } },
        .results = &.{fixture.adjusted_integer},
        .effects = .semantic_environment_read,
        .evidence = &.{fixture.proof},
    };
    var return_blocks = fixture.blocks;
    return_blocks[0].instructions = &.{ fixture.integer_instruction, fixture.string_instruction, fixture.pack_instruction, fixture.adjust_instruction };
    return_blocks[0].terminator = .{ .return_pack = fixture.pack_id };
    var return_program = fixture.program;
    return_program.blocks = &return_blocks;
    return_program.instructions = &return_instructions;
    return_program.values = fixture.values[0..3];
    try expectClean(&return_program, .readable_luau);
    const return_source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &return_program);
    defer std.testing.allocator.free(return_source);
    try std.testing.expect(std.mem.indexOf(u8, return_source, "return 7, \"x\"") != null);

    var table_values = [_]ir.Value{
        fixture.values[0],
        fixture.values[1],
        .{ .id = fixture.adjusted_integer, .function = fixture.function_id, .type = .{ .kind = .table }, .name_hint = "packed", .origin = .{ .instruction_result = .{ .instruction = fixture.adjust_instruction, .index = 0 } } },
    };
    var table_instructions = fixture.instructions;
    table_instructions[fixture.adjust_instruction.index()] = .{
        .id = fixture.adjust_instruction,
        .block = fixture.block_id,
        .operation = .{ .make_table_literal = .{ .fields = &.{}, .tail_pack = fixture.pack_id } },
        .results = &.{fixture.adjusted_integer},
        .effects = .table_constructor,
        .evidence = &.{fixture.proof},
    };
    var table_blocks = fixture.blocks;
    table_blocks[0].terminator = .{ .return_values = &.{fixture.adjusted_integer} };
    var table_program = fixture.program;
    table_program.values = &table_values;
    table_program.instructions = &table_instructions;
    table_program.blocks = &table_blocks;
    try expectClean(&table_program, .readable_luau);
    const table_source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &table_program);
    defer std.testing.allocator.free(table_source);
    try std.testing.expect(std.mem.indexOf(u8, table_source, "7, \"x\"") != null);

    const callee = ir.ValueId.fromIndex(2);
    const get_callee = ir.InstructionId.fromIndex(2);
    const make_pack = ir.InstructionId.fromIndex(3);
    const invoke = ir.InstructionId.fromIndex(4);
    const invocation_values = [_]ir.Value{
        fixture.values[0],
        fixture.values[1],
        .{ .id = callee, .function = fixture.function_id, .type = .dynamic, .name_hint = "consume", .origin = .{ .instruction_result = .{ .instruction = get_callee, .index = 0 } } },
    };
    const invocation_pack = [_]ir.ValuePack{.{
        .id = fixture.pack_id,
        .function = fixture.function_id,
        .origin = .{ .instruction_result = make_pack },
        .shape = .{ .prefix = &fixture.prefix, .tail = .closed },
        .evidence = &.{fixture.proof},
    }};
    const invocation_instructions = [_]ir.Instruction{
        fixture.instructions[0],
        fixture.instructions[1],
        .{ .id = get_callee, .block = fixture.block_id, .operation = .{ .environment_get = .{ .target = .ambient, .name = "consume" } }, .results = &.{callee}, .effects = .semantic_table_read, .evidence = &.{fixture.proof} },
        .{ .id = make_pack, .block = fixture.block_id, .operation = .{ .pack_values = &.{ fixture.integer_id, fixture.string_id } }, .results = &.{}, .pack_result = fixture.pack_id, .effects = .pure, .evidence = &.{fixture.proof} },
        .{ .id = invoke, .block = fixture.block_id, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .argument_pack = fixture.pack_id, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call, .evidence = &.{fixture.proof} },
    };
    const invocation_blocks = [_]ir.Block{.{
        .id = fixture.block_id,
        .function = fixture.function_id,
        .instructions = &.{ fixture.integer_instruction, fixture.string_instruction, get_callee, make_pack, invoke },
        .terminator = .{ .return_values = &.{} },
        .evidence = &.{fixture.proof},
    }};
    var invocation_program = fixture.program;
    invocation_program.values = &invocation_values;
    invocation_program.value_packs = &invocation_pack;
    invocation_program.instructions = &invocation_instructions;
    invocation_program.blocks = &invocation_blocks;
    try expectClean(&invocation_program, .readable_luau);
    const invocation_source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &invocation_program);
    defer std.testing.allocator.free(invocation_source);
    try std.testing.expect(std.mem.indexOf(u8, invocation_source, "consume(7, \"x\")") != null);

    const packed_table = ir.ValueId.fromIndex(3);
    const make_table = ir.InstructionId.fromIndex(5);
    const mixed_values = invocation_values ++ [_]ir.Value{.{
        .id = packed_table,
        .function = fixture.function_id,
        .type = .{ .kind = .table },
        .name_hint = "packed",
        .origin = .{ .instruction_result = .{ .instruction = make_table, .index = 0 } },
    }};
    const mixed_instructions = invocation_instructions ++ [_]ir.Instruction{.{
        .id = make_table,
        .block = fixture.block_id,
        .operation = .{ .make_table_literal = .{ .fields = &.{}, .tail_pack = fixture.pack_id } },
        .results = &.{packed_table},
        .effects = .table_constructor,
        .evidence = &.{fixture.proof},
    }};
    const mixed_blocks = [_]ir.Block{.{
        .id = fixture.block_id,
        .function = fixture.function_id,
        .instructions = &.{ fixture.integer_instruction, fixture.string_instruction, get_callee, make_pack, invoke, make_table },
        .terminator = .{ .return_values = &.{packed_table} },
        .evidence = &.{fixture.proof},
    }};
    var mixed_program = invocation_program;
    mixed_program.values = &mixed_values;
    mixed_program.instructions = &mixed_instructions;
    mixed_program.blocks = &mixed_blocks;
    try expectClean(&mixed_program, .readable_luau);
    var mixed_plan = try pack_plan.Plan.init(std.testing.allocator, &mixed_program);
    defer mixed_plan.deinit();
    try std.testing.expect(mixed_plan.role(make_pack) == .materialized_pack_values_producer);
    try std.testing.expect(mixed_plan.packValuesServesInstruction(make_pack, invoke));
    try std.testing.expect(mixed_plan.packValuesServesInstruction(make_pack, make_table));
    const mixed_source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &mixed_program);
    defer std.testing.allocator.free(mixed_source);
    try std.testing.expect(std.mem.indexOf(u8, mixed_source, "consume(7, \"x\")") != null);
    try std.testing.expect(std.mem.indexOf(u8, mixed_source, "return { 7, \"x\" }") != null);
    try std.testing.expect(std.mem.indexOf(u8, mixed_source, "table.pack") == null);
}

test "nonadjacent pack projection preserves effectful value ordering" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const get_callee = ir.InstructionId.fromIndex(0);
    const call_id = ir.InstructionId.fromIndex(1);
    const pack_instruction = ir.InstructionId.fromIndex(2);
    const gap_id = ir.InstructionId.fromIndex(3);
    const adjust_id = ir.InstructionId.fromIndex(4);
    const callee = ir.ValueId.fromIndex(0);
    const packed_value = ir.ValueId.fromIndex(1);
    const gap_value = ir.ValueId.fromIndex(2);
    const adjusted_value = ir.ValueId.fromIndex(3);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);

    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .name_hint = "produce", .origin = .{ .instruction_result = .{ .instruction = get_callee, .index = 0 } } },
        .{ .id = packed_value, .function = function_id, .name_hint = "packed_value", .origin = .{ .instruction_result = .{ .instruction = call_id, .index = 0 } } },
        .{ .id = gap_value, .function = function_id, .name_hint = "gap_value", .origin = .{ .instruction_result = .{ .instruction = gap_id, .index = 0 } } },
        .{ .id = adjusted_value, .function = function_id, .name_hint = "adjusted_value", .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 0 } } },
    };
    const prefix = [_]ir.ValueType{.dynamic};
    const packs = [_]ir.ValuePack{.{
        .id = pack_id,
        .function = function_id,
        .origin = .{ .instruction_result = pack_instruction },
        .shape = .{ .prefix = &prefix, .tail = .closed },
        .evidence = &.{proof},
    }};
    var instructions = [_]ir.Instruction{
        .{ .id = get_callee, .block = block_id, .operation = .{ .environment_get = .{ .target = .ambient, .name = "produce" } }, .results = &.{callee}, .effects = .semantic_environment_read, .evidence = &.{proof} },
        .{ .id = call_id, .block = block_id, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{packed_value}, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = pack_instruction, .block = block_id, .operation = .{ .pack_values = &.{packed_value} }, .results = &.{}, .pack_result = pack_id, .effects = .pure, .evidence = &.{proof} },
        .{ .id = gap_id, .block = block_id, .operation = .{ .environment_get = .{ .target = .ambient, .name = "after_pack" } }, .results = &.{gap_value}, .effects = .semantic_environment_read, .evidence = &.{proof} },
        .{ .id = adjust_id, .block = block_id, .operation = .{ .adjust_pack = pack_id }, .results = &.{adjusted_value}, .effects = .pure, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ get_callee, call_id, pack_instruction, gap_id, adjust_id },
        .terminator = .{ .return_values = &.{adjusted_value} },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &.{block_id}, .entry_block = block_id, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:nonadjacent-pack-order" }};
    var program: ir.Program = .{
        .program_id = "nonadjacent-pack-order",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
        .evidence = &evidence,
    };

    try expectClean(&program, .readable_luau);
    var planned_packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer planned_packs.deinit();
    const projection = planned_packs.packValuesProjection(&program, pack_instruction).?;
    try std.testing.expectEqual(pack_plan.ProjectionConsumer{ .instruction = adjust_id }, projection.consumer);
    try std.testing.expectEqualSlices(ir.InstructionId, &.{gap_id}, projection.gaps);
    var dead = try dead_code.Plan.init(std.testing.allocator, &program, &planned_packs);
    defer dead.deinit();
    var writes = try place_write_fusion.Plan.init(std.testing.allocator, &program, &planned_packs, &dead);
    defer writes.deinit();
    var reads = try place_read_fusion.Plan.init(std.testing.allocator, &program, &planned_packs, &dead);
    defer reads.deinit();
    var fused_values = try value_fusion.Plan.init(std.testing.allocator, &program, &planned_packs, &dead, &writes, &reads);
    defer fused_values.deinit();
    try std.testing.expect(fused_values.consumer(call_id) == null);

    const source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    const call_position = std.mem.indexOf(u8, source, "produce()") orelse return error.TestUnexpectedResult;
    const gap_position = std.mem.indexOf(u8, source, "after_pack") orelse return error.TestUnexpectedResult;
    try std.testing.expect(call_position < gap_position);

    instructions[gap_id.index()].operation = .{ .constant = .{ .integer = "0" } };
    instructions[gap_id.index()].effects = .pure;
    program.instructions = &instructions;
    var pure_packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer pure_packs.deinit();
    var pure_dead = try dead_code.Plan.init(std.testing.allocator, &program, &pure_packs);
    defer pure_dead.deinit();
    var pure_writes = try place_write_fusion.Plan.init(std.testing.allocator, &program, &pure_packs, &pure_dead);
    defer pure_writes.deinit();
    var pure_reads = try place_read_fusion.Plan.init(std.testing.allocator, &program, &pure_packs, &pure_dead);
    defer pure_reads.deinit();
    var pure_fused_values = try value_fusion.Plan.init(std.testing.allocator, &program, &pure_packs, &pure_dead, &pure_writes, &pure_reads);
    defer pure_fused_values.deinit();
    try std.testing.expectEqual(value_fusion.Consumer{ .instruction = pack_instruction }, pure_fused_values.consumer(call_id).?);

    instructions[gap_id.index()].operation = .{ .environment_get = .{ .target = .ambient, .name = "after_pack" } };
    instructions[gap_id.index()].effects = .semantic_environment_read;
    instructions[adjust_id.index()].results = &.{};
    var discard_blocks = blocks;
    discard_blocks[block_id.index()].terminator = .{ .return_values = &.{} };
    program.instructions = &instructions;
    program.blocks = &discard_blocks;
    program.values = values[0..3];
    try expectClean(&program, .readable_luau);
    var discard_packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer discard_packs.deinit();
    try std.testing.expect(discard_packs.role(pack_instruction) == .materialized_pack_values_producer);
    try std.testing.expect(discard_packs.packValuesProjection(&program, pack_instruction) == null);
    var discard_dead = try dead_code.Plan.init(std.testing.allocator, &program, &discard_packs);
    defer discard_dead.deinit();
    var discard_writes = try place_write_fusion.Plan.init(std.testing.allocator, &program, &discard_packs, &discard_dead);
    defer discard_writes.deinit();
    var discard_reads = try place_read_fusion.Plan.init(std.testing.allocator, &program, &discard_packs, &discard_dead);
    defer discard_reads.deinit();
    var discard_fused_values = try value_fusion.Plan.init(
        std.testing.allocator,
        &program,
        &discard_packs,
        &discard_dead,
        &discard_writes,
        &discard_reads,
    );
    defer discard_fused_values.deinit();
    try std.testing.expect(discard_fused_values.consumer(call_id) == null);
    const discarded_source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(discarded_source);
    const discarded_call = std.mem.indexOf(u8, discarded_source, "produce()") orelse return error.TestUnexpectedResult;
    const discarded_gap = std.mem.indexOf(u8, discarded_source, "after_pack") orelse return error.TestUnexpectedResult;
    try std.testing.expect(discarded_call < discarded_gap);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, discarded_source, "produce()"));
    try std.testing.expect(std.mem.indexOf(u8, discarded_source, "adjusted_value") == null);
}

test "nonadjacent pack projection keeps mutable place reads before writes" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const replacement_instruction = ir.InstructionId.fromIndex(0);
    const read_id = ir.InstructionId.fromIndex(1);
    const pack_instruction = ir.InstructionId.fromIndex(2);
    const write_id = ir.InstructionId.fromIndex(3);
    const adjust_id = ir.InstructionId.fromIndex(4);
    const replacement = ir.ValueId.fromIndex(0);
    const snapshot = ir.ValueId.fromIndex(1);
    const adjusted = ir.ValueId.fromIndex(2);
    const place_id = ir.PlaceId.fromIndex(0);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = replacement, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = replacement_instruction, .index = 0 } } },
        .{ .id = snapshot, .function = function_id, .type = .integer, .name_hint = "snapshot", .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } } },
        .{ .id = adjusted, .function = function_id, .type = .integer, .name_hint = "adjusted", .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 0 } } },
    };
    const places = [_]ir.Place{.{ .id = place_id, .function = function_id, .type = .integer, .origin = .{ .local = 0 } }};
    const prefix = [_]ir.ValueType{.integer};
    const packs = [_]ir.ValuePack{.{
        .id = pack_id,
        .function = function_id,
        .origin = .{ .instruction_result = pack_instruction },
        .shape = .{ .prefix = &prefix, .tail = .closed },
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = replacement_instruction, .block = block_id, .operation = .{ .constant = .{ .integer = "9" } }, .results = &.{replacement}, .effects = .pure },
        .{ .id = read_id, .block = block_id, .operation = .{ .place_read = place_id }, .results = &.{snapshot}, .effects = .place_read },
        .{ .id = pack_instruction, .block = block_id, .operation = .{ .pack_values = &.{snapshot} }, .results = &.{}, .pack_result = pack_id, .effects = .pure },
        .{ .id = write_id, .block = block_id, .operation = .{ .place_write = .{ .place = place_id, .value = replacement } }, .results = &.{}, .effects = .place_write },
        .{ .id = adjust_id, .block = block_id, .operation = .{ .adjust_pack = pack_id }, .results = &.{adjusted}, .effects = .pure },
    };
    var blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ replacement_instruction, read_id, pack_instruction, write_id, adjust_id },
        .terminator = .{ .return_values = &.{adjusted} },
    }};
    const functions = [_]ir.Function{.{ .id = function_id, .local_places = &.{place_id}, .blocks = &.{block_id}, .entry_block = block_id }};
    var program: ir.Program = .{
        .program_id = "nonadjacent-pack-place-read",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
        .places = &places,
    };

    var planned_packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer planned_packs.deinit();
    const projection = planned_packs.packValuesProjection(&program, pack_instruction).?;
    try std.testing.expectEqualSlices(ir.InstructionId, &.{write_id}, projection.gaps);
    var dead = try dead_code.Plan.init(std.testing.allocator, &program, &planned_packs);
    defer dead.deinit();
    var reads = try place_read_fusion.Plan.init(std.testing.allocator, &program, &planned_packs, &dead);
    defer reads.deinit();
    try std.testing.expect(reads.consumer(read_id) == null);

    blocks[0].instructions = &.{ replacement_instruction, read_id, pack_instruction, adjust_id, write_id };
    program.blocks = &blocks;
    var adjacent_packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer adjacent_packs.deinit();
    var adjacent_dead = try dead_code.Plan.init(std.testing.allocator, &program, &adjacent_packs);
    defer adjacent_dead.deinit();
    var adjacent_reads = try place_read_fusion.Plan.init(std.testing.allocator, &program, &adjacent_packs, &adjacent_dead);
    defer adjacent_reads.deinit();
    try std.testing.expectEqual(place_read_fusion.Consumer{ .instruction = pack_instruction }, adjacent_reads.consumer(read_id).?);
}

test "cross-block closed packs materialize operands and reject producer reentry" {
    const function_id = ir.FunctionId.fromIndex(0);
    const producer_block = ir.BlockId.fromIndex(0);
    const consumer_block = ir.BlockId.fromIndex(1);
    const get_probe = ir.InstructionId.fromIndex(0);
    const pack_instruction = ir.InstructionId.fromIndex(1);
    const mutate_probe = ir.InstructionId.fromIndex(2);
    const adjust_pack = ir.InstructionId.fromIndex(3);
    const mutate = ir.ValueId.fromIndex(0);
    const probe = ir.ValueId.fromIndex(1);
    const adjusted = ir.ValueId.fromIndex(2);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);

    const values = [_]ir.Value{
        .{ .id = mutate, .function = function_id, .type = .function, .name_hint = "mutate_probe", .origin = .{ .parameter = 0 } },
        .{ .id = probe, .function = function_id, .type = .function, .name_hint = "snapshotted_probe", .origin = .{ .instruction_result = .{ .instruction = get_probe, .index = 0 } } },
        .{ .id = adjusted, .function = function_id, .type = .function, .name_hint = "adjusted_probe", .origin = .{ .instruction_result = .{ .instruction = adjust_pack, .index = 0 } } },
    };
    const prefix = [_]ir.ValueType{.function};
    const packs = [_]ir.ValuePack{.{
        .id = pack_id,
        .function = function_id,
        .origin = .{ .instruction_result = pack_instruction },
        .shape = .{ .prefix = &prefix, .tail = .closed },
        .evidence = &.{proof},
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = get_probe, .block = producer_block, .operation = .{ .environment_get = .{ .target = .ambient, .name = "cross_block_probe" } }, .results = &.{probe}, .effects = .semantic_environment_read, .evidence = &.{proof} },
        .{ .id = pack_instruction, .block = producer_block, .operation = .{ .pack_values = &.{probe} }, .results = &.{}, .pack_result = pack_id, .effects = .pure, .evidence = &.{proof} },
        .{ .id = mutate_probe, .block = producer_block, .operation = .{ .call = .{ .callee = mutate, .arguments = &.{}, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = adjust_pack, .block = consumer_block, .operation = .{ .adjust_pack = pack_id }, .results = &.{adjusted}, .effects = .pure, .evidence = &.{proof} },
    };
    var blocks = [_]ir.Block{
        .{ .id = producer_block, .function = function_id, .instructions = &.{ get_probe, pack_instruction, mutate_probe }, .terminator = .{ .jump = .{ .target = consumer_block } }, .evidence = &.{proof} },
        .{ .id = consumer_block, .function = function_id, .instructions = &.{adjust_pack}, .terminator = .{ .return_values = &.{adjusted} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .parameters = &.{mutate}, .blocks = &.{ producer_block, consumer_block }, .entry_block = producer_block, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:cross-block-pack-values" }};
    var program: ir.Program = .{
        .program_id = "cross-block-pack-values",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
        .evidence = &evidence,
    };

    try expectClean(&program, .readable_luau);
    var adjustment_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer adjustment_plan.deinit();
    try std.testing.expectEqual(pack_plan.InstructionRole{ .fused_pack_values_producer = adjust_pack }, adjustment_plan.role(pack_instruction));
    try std.testing.expect(adjustment_plan.packValuesProjection(&program, pack_instruction) == null);

    const adjustment_source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(adjustment_source);
    const read_position = std.mem.indexOf(u8, adjustment_source, "local snapshotted_probe = cross_block_probe") orelse return error.TestUnexpectedResult;
    const mutation_position = std.mem.indexOf(u8, adjustment_source, "mutate_probe()") orelse return error.TestUnexpectedResult;
    try std.testing.expect(read_position < mutation_position);
    try std.testing.expect(std.mem.indexOf(u8, adjustment_source, "local adjusted_probe = snapshotted_probe") != null);

    const dispatcher_block = ir.BlockId.fromIndex(2);
    const condition = ir.ValueId.fromIndex(3);
    const non_dominating_values = values ++ [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .name_hint = "condition",
        .origin = .{ .parameter = 1 },
    }};
    const non_dominating_blocks = [_]ir.Block{
        blocks[producer_block.index()],
        blocks[consumer_block.index()],
        .{
            .id = dispatcher_block,
            .function = function_id,
            .instructions = &.{},
            .terminator = .{ .branch = .{
                .condition = condition,
                .then_edge = .{ .target = producer_block },
                .else_edge = .{ .target = consumer_block },
            } },
            .evidence = &.{proof},
        },
    };
    const non_dominating_functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ mutate, condition },
        .blocks = &.{ dispatcher_block, producer_block, consumer_block },
        .entry_block = dispatcher_block,
        .evidence = &.{proof},
    }};
    var non_dominating_program = program;
    non_dominating_program.functions = &non_dominating_functions;
    non_dominating_program.blocks = &non_dominating_blocks;
    non_dominating_program.values = &non_dominating_values;
    try expectDiagnostic(&non_dominating_program, .core, .non_dominating_value_pack_use);
    var non_dominating_plan = try pack_plan.Plan.init(std.testing.allocator, &non_dominating_program);
    defer non_dominating_plan.deinit();
    try std.testing.expect(non_dominating_plan.role(pack_instruction) == .ordinary);

    blocks[consumer_block.index()].terminator = .{ .jump = .{ .target = producer_block } };
    program.blocks = &blocks;
    var cyclic_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer cyclic_plan.deinit();
    try std.testing.expect(cyclic_plan.role(pack_instruction) == .ordinary);

    blocks[consumer_block.index()].instructions = &.{};
    blocks[consumer_block.index()].terminator = .{ .return_pack = pack_id };
    program.blocks = &blocks;
    program.instructions = instructions[0..3];
    program.values = values[0..2];
    try expectClean(&program, .readable_luau);
    var return_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer return_plan.deinit();
    try std.testing.expectEqual(pack_plan.TerminatorRole{ .fused_pack_values_return = pack_instruction }, return_plan.terminatorRole(consumer_block));
    try std.testing.expect(return_plan.packValuesProjection(&program, pack_instruction) == null);

    const return_source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(return_source);
    try std.testing.expect(std.mem.indexOf(u8, return_source, "return snapshotted_probe") != null);
}

test "fused last pack_values operand truncates to the modeled arity" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const call_id = ir.InstructionId.fromIndex(0);
    const pack_instruction = ir.InstructionId.fromIndex(1);
    const callee = ir.ValueId.fromIndex(0);
    const result = ir.ValueId.fromIndex(1);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);

    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .name_hint = "f", .origin = .{ .parameter = 0 } },
        .{ .id = result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = call_id, .index = 0 } } },
    };
    const prefix = [_]ir.ValueType{.dynamic};
    const packs = [_]ir.ValuePack{.{
        .id = pack_id,
        .function = function_id,
        .origin = .{ .instruction_result = pack_instruction },
        .shape = .{ .prefix = &prefix, .tail = .closed },
        .evidence = &.{proof},
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = call_id, .block = block_id, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{result}, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = pack_instruction, .block = block_id, .operation = .{ .pack_values = &.{result} }, .results = &.{}, .pack_result = pack_id, .effects = .pure, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ call_id, pack_instruction },
        .terminator = .{ .return_pack = pack_id },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{ .id = function_id, .parameters = &.{callee}, .blocks = &.{block_id}, .entry_block = block_id, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:fused-pack-tail-return" }};
    const program: ir.Program = .{
        .program_id = "fused-pack-tail-return",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
        .evidence = &evidence,
    };

    try expectClean(&program, .readable_luau);
    var plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .fused_pack_values_return = pack_instruction },
        plan.terminatorRole(block_id),
    );

    const source = try emitter.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "return (f())") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "return f()") == null);
}
