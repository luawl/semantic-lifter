const std = @import("std");
const lifter = @import("semantic_lifter");
const ir = lifter.ir;
const validation = lifter.validate;
const emitStandardLuauAlloc = lifter.emit_luau.emitStandardLuauAlloc;

const operator_matrix_function = ir.FunctionId.fromIndex(0);
const operator_matrix_block = ir.BlockId.fromIndex(0);
const operator_matrix_instruction = ir.InstructionId.fromIndex(0);
const operator_matrix_left = ir.ValueId.fromIndex(0);
const operator_matrix_right = ir.ValueId.fromIndex(1);
const operator_matrix_result = ir.ValueId.fromIndex(2);
const operator_matrix_evidence = ir.EvidenceId.fromIndex(0);
const operator_u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32, .signed = false };

const UnaryOperatorRow = struct {
    operator: ir.UnaryOperator,
    operand_type: ir.ValueType,
    result_type: ir.ValueType,
    expected_expression: []const u8,
    expected_capability: ?[]const u8 = null,
    primitive_only: bool = false,
};

const BinaryOperatorRow = struct {
    operator: ir.BinaryOperator,
    left_type: ir.ValueType,
    right_type: ir.ValueType,
    result_type: ir.ValueType,
    expected_expression: []const u8,
    expected_capability: ?[]const u8 = null,
    primitive_only: bool = false,
};

const OperatorExpectation = enum {
    clean,
    understated_effects,
    result_type_mismatch,
    unproved_primitive_domain,
    unsupported_bit_operation,
    missing_shift_behavior,
    unexpected_shift_behavior,
    unknown_effects,
};

const RejectedOperatorRow = struct {
    operation: ir.Operation,
    left_type: ir.ValueType,
    right_type: ir.ValueType = .dynamic,
    result_type: ir.ValueType,
    effects: ir.EffectSummary = .pure,
    expectation: OperatorExpectation,
};

fn unaryOperatorRow(operator: ir.UnaryOperator, operand_type: ir.ValueType, result_type: ir.ValueType, expected_expression: []const u8) UnaryOperatorRow {
    return .{ .operator = operator, .operand_type = operand_type, .result_type = result_type, .expected_expression = expected_expression };
}

fn bitUnaryOperatorRow(operator: ir.UnaryOperator, expected_expression: []const u8, expected_capability: []const u8) UnaryOperatorRow {
    return .{
        .operator = operator,
        .operand_type = operator_u32_type,
        .result_type = operator_u32_type,
        .expected_expression = expected_expression,
        .expected_capability = expected_capability,
        .primitive_only = true,
    };
}

fn binaryOperatorRow(operator: ir.BinaryOperator, operand_type: ir.ValueType, result_type: ir.ValueType, expected_expression: []const u8) BinaryOperatorRow {
    return .{
        .operator = operator,
        .left_type = operand_type,
        .right_type = operand_type,
        .result_type = result_type,
        .expected_expression = expected_expression,
    };
}

fn bitBinaryOperatorRow(operator: ir.BinaryOperator, expected_expression: []const u8, expected_capability: []const u8) BinaryOperatorRow {
    return .{
        .operator = operator,
        .left_type = operator_u32_type,
        .right_type = operator_u32_type,
        .result_type = operator_u32_type,
        .expected_expression = expected_expression,
        .expected_capability = expected_capability,
        .primitive_only = true,
    };
}

fn unaryOperation(operator: ir.UnaryOperator, mode: ir.OperatorMode) ir.Operation {
    return .{ .unary = .{ .operator = operator, .operand = operator_matrix_left, .mode = mode } };
}

fn binaryOperation(operator: ir.BinaryOperator, mode: ir.OperatorMode, shift_behavior: ?ir.ShiftBehavior) ir.Operation {
    return .{ .binary = .{
        .operator = operator,
        .left = operator_matrix_left,
        .right = operator_matrix_right,
        .mode = mode,
        .shift_behavior = shift_behavior,
    } };
}

fn expectReadableOperatorRow(
    operation: ir.Operation,
    left_type: ir.ValueType,
    right_type: ir.ValueType,
    result_type: ir.ValueType,
    effects: ir.EffectSummary,
    expected_expression: []const u8,
    expected_capability: ?[]const u8,
    expectation: OperatorExpectation,
) !void {
    const values = [_]ir.Value{
        .{ .id = operator_matrix_left, .function = operator_matrix_function, .type = left_type, .name_hint = "left", .origin = .{ .parameter = 0 } },
        .{ .id = operator_matrix_right, .function = operator_matrix_function, .type = right_type, .name_hint = "right", .origin = .{ .parameter = 1 } },
        .{ .id = operator_matrix_result, .function = operator_matrix_function, .type = result_type, .name_hint = "result", .origin = .{ .instruction_result = .{ .instruction = operator_matrix_instruction, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = operator_matrix_instruction,
        .block = operator_matrix_block,
        .operation = operation,
        .results = &.{operator_matrix_result},
        .effects = effects,
        .evidence = &.{operator_matrix_evidence},
    }};
    const blocks = [_]ir.Block{.{
        .id = operator_matrix_block,
        .function = operator_matrix_function,
        .instructions = &.{operator_matrix_instruction},
        .terminator = .{ .return_values = &.{operator_matrix_result} },
        .evidence = &.{operator_matrix_evidence},
    }};
    const functions = [_]ir.Function{.{
        .id = operator_matrix_function,
        .parameters = &.{ operator_matrix_left, operator_matrix_right },
        .blocks = &.{operator_matrix_block},
        .entry_block = operator_matrix_block,
        .evidence = &.{operator_matrix_evidence},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = operator_matrix_evidence,
        .kind = .dynamic_fixture,
        .locator = "fixture:readable-runtime-operator-matrix",
    }};
    const program: ir.Program = .{
        .program_id = "readable-runtime-operator-matrix",
        .entry_function = operator_matrix_function,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    var report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer report.deinit();
    if (expectation != .clean) {
        try std.testing.expectEqual(@as(usize, 1), report.diagnostics.items.len);
        switch (expectation) {
            .clean => unreachable,
            .understated_effects => try std.testing.expect(report.contains(.understated_operator_effects)),
            .result_type_mismatch => try std.testing.expect(report.contains(.operation_result_type_mismatch)),
            .unproved_primitive_domain => try std.testing.expect(report.contains(.unproved_primitive_operator_domain)),
            .unsupported_bit_operation => try std.testing.expect(report.contains(.unsupported_readable_bit_operation)),
            .missing_shift_behavior => try std.testing.expect(report.contains(.missing_shift_behavior)),
            .unexpected_shift_behavior => try std.testing.expect(report.contains(.unexpected_shift_behavior)),
            .unknown_effects => try std.testing.expect(report.contains(.unknown_effects)),
        }
        return;
    }
    try std.testing.expect(report.isClean());

    const first = try emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(first);
    const second = try emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(second);
    try std.testing.expectEqualStrings(first, second);
    try std.testing.expect(std.mem.indexOf(u8, first, expected_expression) != null);
    if (expected_capability) |capability| {
        try std.testing.expect(std.mem.indexOf(u8, first, capability) != null);
    }
}

test "closure ownership and binding failures are typed" {
    const fixture = lifter.fixtures.immutable_closure_module;

    {
        var functions = fixture.functions;
        functions[fixture.f_adder.index()].lexical_parent = fixture.f_entry;
        var program = fixture.program;
        program.functions = &functions;
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(report.contains(.closure_lexical_parent_mismatch));
    }

    {
        var instructions = fixture.instructions;
        instructions[fixture.i_make_adder.index()].operation = .{ .make_closure = .{
            .function = fixture.f_adder,
            .bindings = &.{},
        } };
        var program = fixture.program;
        program.instructions = &instructions;
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(report.contains(.closure_binding_arity_mismatch));
    }

    {
        var instructions = fixture.instructions;
        instructions[fixture.i_make_adder.index()].operation = .{ .make_closure = .{
            .function = fixture.f_adder,
            .bindings = &.{.{ .place = ir.PlaceId.fromIndex(0) }},
        } };
        var program = fixture.program;
        program.instructions = &instructions;
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(report.contains(.closure_binding_kind_mismatch));
        try std.testing.expect(report.contains(.invalid_place_operand));
    }

    {
        var instructions = fixture.instructions;
        instructions[fixture.i_export.index()].operation = .{ .function_ref = fixture.f_adder };
        var program = fixture.program;
        program.instructions = &instructions;
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(report.contains(.invalid_function_reference));
    }

    {
        var functions = fixture.functions;
        functions[fixture.f_factory.index()].lexical_parent = fixture.f_adder;
        var program = fixture.program;
        program.functions = &functions;
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(report.contains(.cyclic_function_lexical_parent));
    }
}

test "place operations require exact memory effects" {
    const fixture = lifter.fixtures.shared_place_closure_module;

    var read_instructions = fixture.instructions;
    read_instructions[fixture.i_read.index()].effects = .pure;
    var read_program = fixture.program;
    read_program.instructions = &read_instructions;
    var read_report = try validation.validate(std.testing.allocator, &read_program, .core);
    defer read_report.deinit();
    try std.testing.expect(read_report.contains(.invalid_place_read_effects));

    var write_instructions = fixture.instructions;
    write_instructions[fixture.i_write.index()].effects = .pure;
    var write_program = fixture.program;
    write_program.instructions = &write_instructions;
    var write_report = try validation.validate(std.testing.allocator, &write_program, .core);
    defer write_report.deinit();
    try std.testing.expect(write_report.contains(.invalid_place_write_effects));
}

test "known table access effects cannot be understated" {
    const fixture = lifter.fixtures.arithmetic_module;

    try std.testing.expect(ir.EffectSummary.semantic_table_read.writes_memory);
    try std.testing.expect(ir.EffectSummary.semantic_environment_read.writes_memory);

    var semantic_instructions = fixture.instructions;
    semantic_instructions[fixture.i_sum.index()].operation = .{ .table_get = .{
        .table = fixture.v_left,
        .key = fixture.v_right,
        .mode = .semantic,
    } };
    semantic_instructions[fixture.i_sum.index()].effects = .pure;
    var semantic_program = fixture.program;
    semantic_program.instructions = &semantic_instructions;
    var semantic_report = try validation.validate(std.testing.allocator, &semantic_program, .core);
    defer semantic_report.deinit();
    try std.testing.expect(semantic_report.contains(.understated_table_get_effects));

    var callback_instructions = fixture.instructions;
    callback_instructions[fixture.i_sum.index()].operation = .{ .table_get = .{
        .table = fixture.v_left,
        .key = fixture.v_right,
        .mode = .semantic,
    } };
    callback_instructions[fixture.i_sum.index()].effects = .{
        .precision = .conservative,
        .reads_memory = true,
        .may_throw = true,
        .may_yield = true,
        .invokes_unknown_code = true,
    };
    var callback_program = fixture.program;
    callback_program.instructions = &callback_instructions;
    var callback_report = try validation.validate(std.testing.allocator, &callback_program, .core);
    defer callback_report.deinit();
    try std.testing.expect(callback_report.contains(.understated_table_get_effects));

    var raw_instructions = fixture.instructions;
    raw_instructions[fixture.i_sum.index()].operation = .{ .table_get = .{
        .table = fixture.v_left,
        .key = fixture.v_right,
        .mode = .raw,
    } };
    raw_instructions[fixture.i_sum.index()].effects = .raw_table_read;
    var raw_program = fixture.program;
    raw_program.instructions = &raw_instructions;
    var raw_report = try validation.validate(std.testing.allocator, &raw_program, .core);
    defer raw_report.deinit();
    try std.testing.expect(!raw_report.contains(.understated_table_get_effects));

    var set_instructions = fixture.instructions;
    set_instructions[fixture.i_factor.index()].operation = .{ .table_set = .{
        .table = fixture.v_left,
        .key = fixture.v_right,
        .value = fixture.v_sum,
        .mode = .raw,
    } };
    set_instructions[fixture.i_factor.index()].effects = .pure;
    var set_program = fixture.program;
    set_program.instructions = &set_instructions;
    var set_report = try validation.validate(std.testing.allocator, &set_program, .core);
    defer set_report.deinit();
    try std.testing.expect(set_report.contains(.understated_table_set_effects));
}

test "pack shapes constrain producers and fixed adjustments" {
    const fixture = lifter.fixtures.open_pack_adjust_module;
    const boolean_prefix = [_]ir.ValueType{.boolean};
    var packs = fixture.value_packs;
    packs[0].shape = .{ .prefix = &boolean_prefix, .tail = .open };
    var values = fixture.values;
    values[fixture.v_first.index()].type = .integer;
    var program = fixture.program;
    program.value_packs = &packs;
    program.values = &values;

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(!report.contains(.invalid_value_pack_shape));
    try std.testing.expect(report.contains(.pack_adjustment_type_mismatch));

    const integer_prefix = [_]ir.ValueType{.integer};
    packs[0].shape = .{ .prefix = &integer_prefix, .tail = .closed };
    var closed_report = try validation.validate(std.testing.allocator, &program, .core);
    defer closed_report.deinit();
    try std.testing.expect(!closed_report.contains(.invalid_value_pack_shape));
    try std.testing.expect(!closed_report.contains(.pack_adjustment_type_mismatch));
}

test "pack adjustment types reject narrowing unknown values" {
    const fixture = lifter.fixtures.open_pack_adjust_module;
    const dynamic_prefix = [_]ir.ValueType{.dynamic};
    var packs = fixture.value_packs;
    packs[0].shape = .{ .prefix = &dynamic_prefix, .tail = .open };
    var values = fixture.values;
    values[fixture.v_first.index()].type = .integer;
    var program = fixture.program;
    program.value_packs = &packs;
    program.values = &values;

    var narrowing_report = try validation.validate(std.testing.allocator, &program, .core);
    defer narrowing_report.deinit();
    try std.testing.expect(narrowing_report.contains(.pack_adjustment_type_mismatch));

    const integer_prefix = [_]ir.ValueType{.integer};
    packs[0].shape = .{ .prefix = &integer_prefix, .tail = .open };
    values[fixture.v_first.index()].type = .number;
    var widening_report = try validation.validate(std.testing.allocator, &program, .core);
    defer widening_report.deinit();
    try std.testing.expect(!widening_report.contains(.pack_adjustment_type_mismatch));
}

test "protected and coroutine boundaries require typed status and effects" {
    const open_fixture = lifter.fixtures.open_pack_adjust_module;
    var instructions = open_fixture.instructions;
    instructions[open_fixture.i_call.index()].operation = .{ .protected_call = .{
        .callee = open_fixture.v_callee,
        .arguments = &.{},
        .result_arity = .{ .variadic = {} },
    } };
    instructions[open_fixture.i_call.index()].effects = .protected_invocation;
    var program = open_fixture.program;
    program.instructions = &instructions;

    var missing_prefix_report = try validation.validate(std.testing.allocator, &program, .core);
    defer missing_prefix_report.deinit();
    try std.testing.expect(missing_prefix_report.contains(.invalid_value_pack_shape));

    const boolean_prefix = [_]ir.ValueType{.boolean};
    var packs = open_fixture.value_packs;
    packs[0].shape = .{ .prefix = &boolean_prefix, .tail = .open };
    program.value_packs = &packs;
    var valid_prefix_report = try validation.validate(std.testing.allocator, &program, .core);
    defer valid_prefix_report.deinit();
    try std.testing.expect(!valid_prefix_report.contains(.invalid_value_pack_shape));

    instructions[open_fixture.i_call.index()].effects = .pure;
    var effects_report = try validation.validate(std.testing.allocator, &program, .core);
    defer effects_report.deinit();
    try std.testing.expect(effects_report.contains(.invalid_protected_call_effects));

    const arithmetic = lifter.fixtures.arithmetic_module;
    var coroutine_instructions = arithmetic.instructions;
    coroutine_instructions[arithmetic.i_sum.index()].operation = .{ .coroutine_create = .{ .callee = arithmetic.v_left } };
    coroutine_instructions[arithmetic.i_sum.index()].effects = .coroutine_create;
    var coroutine_program = arithmetic.program;
    coroutine_program.instructions = &coroutine_instructions;
    var coroutine_report = try validation.validate(std.testing.allocator, &coroutine_program, .core);
    defer coroutine_report.deinit();
    try std.testing.expect(coroutine_report.contains(.invalid_coroutine_value_type));
}

test "captured protected-call capabilities permit reachable runtime global mutation" {
    const fixture = lifter.fixtures.open_pack_adjust_module;
    const store_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const boolean_prefix = [_]ir.ValueType{.boolean};
    var packs = fixture.value_packs;
    packs[fixture.p_results.index()].shape = .{ .prefix = &boolean_prefix, .tail = .open };
    var instructions = fixture.instructions ++ [_]ir.Instruction{.{
        .id = store_id,
        .block = fixture.b_entry,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "unrelated",
            .value = fixture.v_callee,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
        .evidence = &.{fixture.proof},
    }};
    instructions[fixture.i_call.index()].operation = .{ .protected_call = .{
        .callee = fixture.v_callee,
        .arguments = &.{},
        .result_arity = .{ .variadic = {} },
    } };
    instructions[fixture.i_call.index()].effects = .protected_invocation;
    const block_instructions = [_]ir.InstructionId{ fixture.i_get, fixture.i_call, store_id, fixture.i_adjust };
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].instructions = &block_instructions;
    var program = fixture.program;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.value_packs = &packs;

    var unrelated_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer unrelated_report.deinit();
    try std.testing.expect(unrelated_report.isClean());

    instructions[store_id.index()].operation.environment_set.name = "pcall";
    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());

    var pcall_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer pcall_report.deinit();
    try std.testing.expect(pcall_report.isClean());

    instructions[fixture.i_call.index()].operation.protected_call.error_handler = fixture.v_callee;
    var unrelated_to_xpcall_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer unrelated_to_xpcall_report.deinit();
    try std.testing.expect(unrelated_to_xpcall_report.isClean());

    instructions[store_id.index()].operation.environment_set.name = "xpcall";
    var xpcall_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer xpcall_report.deinit();
    try std.testing.expect(xpcall_report.isClean());
}

fn canonicalType(kind: ir.TypeKind) ir.ValueType {
    return switch (kind) {
        .integer => .integer,
        .number => .number,
        else => .{ .kind = kind },
    };
}

fn expectTypedThrowAdmission(
    message_kind: ir.TypeKind,
    dynamic_level_kind: ?ir.TypeKind,
    static_level: u32,
    reachable: bool,
    blocked: bool,
) !void {
    const proof = ir.EvidenceId.fromIndex(0);
    const f_entry = ir.FunctionId.fromIndex(0);
    const f_thrower = ir.FunctionId.fromIndex(1);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_body = ir.BlockId.fromIndex(1);
    const b_dead = ir.BlockId.fromIndex(2);
    const i_export = ir.InstructionId.fromIndex(0);
    const v_export = ir.ValueId.fromIndex(0);
    const v_message = ir.ValueId.fromIndex(1);
    const v_level = ir.ValueId.fromIndex(2);

    const values = [_]ir.Value{
        .{ .id = v_export, .function = f_entry, .type = .function, .origin = .{ .instruction_result = .{ .instruction = i_export, .index = 0 } } },
        .{ .id = v_message, .function = f_thrower, .type = canonicalType(message_kind), .origin = .{ .parameter = 0 }, .name_hint = "error_object" },
        .{ .id = v_level, .function = f_thrower, .type = canonicalType(dynamic_level_kind orelse .dynamic), .origin = .{ .parameter = 1 }, .name_hint = "error_level" },
    };
    const instructions = [_]ir.Instruction{.{
        .id = i_export,
        .block = b_entry,
        .operation = .{ .function_ref = f_thrower },
        .results = &.{v_export},
        .effects = .pure,
        .evidence = &.{proof},
    }};
    const throw_terminator: ir.Terminator = .{ .throw_error = .{
        .value = v_message,
        .level = static_level,
        .dynamic_level = if (dynamic_level_kind != null) v_level else null,
    } };
    const return_terminator: ir.Terminator = .{ .return_values = &.{v_message} };
    const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f_entry, .instructions = &.{i_export}, .terminator = .{ .return_values = &.{v_export} }, .evidence = &.{proof} },
        .{ .id = b_body, .function = f_thrower, .terminator = if (reachable) throw_terminator else return_terminator, .evidence = &.{proof} },
        .{ .id = b_dead, .function = f_thrower, .terminator = if (reachable) return_terminator else throw_terminator, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{
        .{ .id = f_entry, .blocks = &.{b_entry}, .entry_block = b_entry, .evidence = &.{proof} },
        .{ .id = f_thrower, .parameters = &.{ v_message, v_level }, .blocks = &.{ b_body, b_dead }, .entry_block = b_body, .evidence = &.{proof} },
    };
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:typed-throw-admission" }};
    const program: ir.Program = .{
        .program_id = "typed-throw-admission",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    if (dynamic_level_kind != null and static_level != 0) {
        try std.testing.expect(core_report.contains(.conflicting_error_levels));
        return;
    }
    try std.testing.expect(core_report.isClean());

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    if (blocked) {
        try std.testing.expectEqual(@as(usize, 1), readable_report.diagnostics.items.len);
        try std.testing.expect(readable_report.contains(.unsupported_readable_error_location));
        try std.testing.expectEqual(@as(?u32, @intCast(b_body.index())), readable_report.diagnostics.items[0].entity_index);
        try std.testing.expectError(error.InvalidIr, emitStandardLuauAlloc(std.testing.allocator, &program));
    } else {
        try std.testing.expect(readable_report.isClean());
        const source = try emitStandardLuauAlloc(std.testing.allocator, &program);
        defer std.testing.allocator.free(source);
        if (dynamic_level_kind != null and reachable) {
            try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_error(error_object, error_level)") != null);
        }
    }
}

test "typed throws are readable terminators" {
    const fixture = lifter.fixtures.absolute_value_module;
    var blocks = fixture.blocks;
    blocks[fixture.b_join.index()].terminator = .{ .throw_error = .{
        .value = fixture.v_absolute,
        .level = 0,
    } };
    var program = fixture.program;
    program.blocks = &blocks;
    var report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer report.deinit();
    try std.testing.expect(!report.contains(.unsupported_readable_terminator));

    const store_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const instructions = fixture.instructions ++ [_]ir.Instruction{.{
        .id = store_id,
        .block = fixture.b_join,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "error",
            .value = fixture.v_absolute,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
        .evidence = &.{fixture.proof},
    }};
    const join_instructions = [_]ir.InstructionId{store_id};
    blocks[fixture.b_join.index()].instructions = &join_instructions;
    program.instructions = &instructions;

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var mutable_error_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer mutable_error_report.deinit();
    try std.testing.expect(mutable_error_report.isClean());

    const rows = [_]struct {
        kind: ir.TypeKind,
        positive_level_blocked: bool,
    }{
        .{ .kind = .dynamic, .positive_level_blocked = true },
        .{ .kind = .nil_value, .positive_level_blocked = false },
        .{ .kind = .boolean, .positive_level_blocked = false },
        .{ .kind = .integer, .positive_level_blocked = true },
        .{ .kind = .number, .positive_level_blocked = true },
        .{ .kind = .string, .positive_level_blocked = true },
        .{ .kind = .table, .positive_level_blocked = false },
        .{ .kind = .function, .positive_level_blocked = false },
        .{ .kind = .thread, .positive_level_blocked = false },
        .{ .kind = .userdata, .positive_level_blocked = false },
        .{ .kind = .tuple, .positive_level_blocked = true },
    };
    try std.testing.expectEqual(std.meta.fields(ir.TypeKind).len, rows.len);
    for (rows) |row| {
        try expectTypedThrowAdmission(row.kind, null, 0, true, false);
        try expectTypedThrowAdmission(row.kind, null, 1, true, row.positive_level_blocked);
        try expectTypedThrowAdmission(row.kind, .integer, 0, true, row.positive_level_blocked);
        try expectTypedThrowAdmission(row.kind, .number, 0, true, row.positive_level_blocked);
    }

    const level_rows = [_]struct {
        kind: ir.TypeKind,
        blocked: bool,
    }{
        .{ .kind = .dynamic, .blocked = true },
        .{ .kind = .nil_value, .blocked = true },
        .{ .kind = .boolean, .blocked = true },
        .{ .kind = .integer, .blocked = false },
        .{ .kind = .number, .blocked = false },
        .{ .kind = .string, .blocked = true },
        .{ .kind = .table, .blocked = true },
        .{ .kind = .function, .blocked = true },
        .{ .kind = .thread, .blocked = true },
        .{ .kind = .userdata, .blocked = true },
        .{ .kind = .tuple, .blocked = true },
    };
    try std.testing.expectEqual(std.meta.fields(ir.TypeKind).len, level_rows.len);
    for (level_rows) |row| {
        try expectTypedThrowAdmission(.table, row.kind, 0, true, row.blocked);
    }

    try expectTypedThrowAdmission(.dynamic, null, 1, false, false);
    try expectTypedThrowAdmission(.string, .integer, 0, false, false);
    try expectTypedThrowAdmission(.table, .string, 0, false, false);
    try expectTypedThrowAdmission(.table, .integer, 1, true, false);
}

test "reduced call effects require a typed replayable claim" {
    const fixture = lifter.fixtures.open_pack_adjust_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_call.index()].effects = .pure;
    var program = fixture.program;
    program.instructions = &instructions;

    var unproved_report = try validation.validate(std.testing.allocator, &program, .core);
    defer unproved_report.deinit();
    try std.testing.expect(unproved_report.contains(.understated_call_effects));

    var terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    }};
    var certificates = [_]ir.SolverCertificate{.{
        .id = ir.CertificateId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .engine = .internal_facts,
        .resolution = .proved,
        .evidence = &.{fixture.proof},
    }};
    var claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .instruction = fixture.i_call },
        .predicate = ir.SolverTermId.fromIndex(0),
        .status = .proved,
        .required_for_emission = true,
        .evidence = &.{fixture.proof},
        .certificate = ir.CertificateId.fromIndex(0),
    }};
    const instruction_claims = [_]ir.ClaimId{ir.ClaimId.fromIndex(0)};
    instructions[fixture.i_call.index()].claims = &instruction_claims;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.certificates = &certificates;
    program.claims = &claims;

    var generic_report = try validation.validate(std.testing.allocator, &program, .core);
    defer generic_report.deinit();
    try std.testing.expect(generic_report.contains(.understated_call_effects));

    claims[0].purpose = .{ .effect_summary = .pure };
    var literal_report = try validation.validate(std.testing.allocator, &program, .core);
    defer literal_report.deinit();
    try std.testing.expect(literal_report.contains(.understated_call_effects));
    try std.testing.expect(literal_report.contains(.claim_predicate_purpose_mismatch));

    terms[0].operation = .{ .semantic_atom = .{ .instruction_effects = fixture.i_call } };
    var internal_report = try validation.validate(std.testing.allocator, &program, .core);
    defer internal_report.deinit();
    try std.testing.expect(internal_report.contains(.understated_call_effects));
    try std.testing.expect(internal_report.contains(.certificate_replay_mismatch));
    try std.testing.expect(!internal_report.contains(.claim_predicate_purpose_mismatch));

    certificates[0].engine = .imported;
    certificates[0].certificate_digest = "fixture:instruction-effects";
    var effect_report = try validation.validate(std.testing.allocator, &program, .core);
    defer effect_report.deinit();
    try std.testing.expect(!effect_report.contains(.understated_call_effects));
    try std.testing.expect(!effect_report.contains(.claim_effect_summary_mismatch));
    try std.testing.expect(!effect_report.contains(.claim_predicate_purpose_mismatch));

    claims[0].purpose = .{ .effect_summary = .dynamic_call };
    var mismatch_report = try validation.validate(std.testing.allocator, &program, .core);
    defer mismatch_report.deinit();
    try std.testing.expect(mismatch_report.contains(.understated_call_effects));
    try std.testing.expect(mismatch_report.contains(.claim_effect_summary_mismatch));
}

test "primitive operator mode requires a static or certified domain" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_left.index()].type = .dynamic;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation.binary.mode = .semantic;
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;

    var semantic_report = try validation.validate(std.testing.allocator, &program, .core);
    defer semantic_report.deinit();
    try std.testing.expect(semantic_report.contains(.understated_operator_effects));

    instructions[fixture.i_sum.index()].operation.binary.mode = .primitive;
    var primitive_report = try validation.validate(std.testing.allocator, &program, .core);
    defer primitive_report.deinit();
    try std.testing.expect(primitive_report.contains(.unproved_primitive_operator_domain));

    var terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    }};
    var certificates = [_]ir.SolverCertificate{.{
        .id = ir.CertificateId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .engine = .internal_facts,
        .resolution = .proved,
        .evidence = &.{fixture.proof},
    }};
    const claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .instruction = fixture.i_sum },
        .predicate = ir.SolverTermId.fromIndex(0),
        .purpose = .{ .primitive_operator_domain = .pure },
        .status = .proved,
        .required_for_emission = true,
        .evidence = &.{fixture.proof},
        .certificate = ir.CertificateId.fromIndex(0),
    }};
    const instruction_claims = [_]ir.ClaimId{ir.ClaimId.fromIndex(0)};
    instructions[fixture.i_sum.index()].claims = &instruction_claims;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.certificates = &certificates;
    program.claims = &claims;
    var literal_report = try validation.validate(std.testing.allocator, &program, .core);
    defer literal_report.deinit();
    try std.testing.expect(literal_report.contains(.unproved_primitive_operator_domain));
    try std.testing.expect(literal_report.contains(.claim_predicate_purpose_mismatch));

    terms[0].operation = .{ .semantic_atom = .{ .instruction_effects = fixture.i_sum } };
    var wrong_kind_report = try validation.validate(std.testing.allocator, &program, .core);
    defer wrong_kind_report.deinit();
    try std.testing.expect(wrong_kind_report.contains(.claim_predicate_purpose_mismatch));
    try std.testing.expect(wrong_kind_report.contains(.unproved_primitive_operator_domain));

    terms[0].operation = .{ .semantic_atom = .{ .primitive_operator_domain = fixture.i_result } };
    var wrong_subject_report = try validation.validate(std.testing.allocator, &program, .core);
    defer wrong_subject_report.deinit();
    try std.testing.expect(wrong_subject_report.contains(.claim_predicate_purpose_mismatch));
    try std.testing.expect(wrong_subject_report.contains(.unproved_primitive_operator_domain));

    terms[0].operation = .{ .semantic_atom = .{ .primitive_operator_domain = ir.InstructionId.fromIndex(99) } };
    var invalid_atom_report = try validation.validate(std.testing.allocator, &program, .core);
    defer invalid_atom_report.deinit();
    try std.testing.expect(invalid_atom_report.contains(.invalid_semantic_atom_reference));
    try std.testing.expect(invalid_atom_report.contains(.claim_predicate_purpose_mismatch));

    terms[0].operation = .{ .semantic_atom = .{ .primitive_operator_domain = fixture.i_sum } };
    var internal_report = try validation.validate(std.testing.allocator, &program, .core);
    defer internal_report.deinit();
    try std.testing.expect(internal_report.contains(.unproved_primitive_operator_domain));
    try std.testing.expect(internal_report.contains(.certificate_replay_mismatch));
    try std.testing.expect(!internal_report.contains(.claim_predicate_purpose_mismatch));

    certificates[0].engine = .imported;
    certificates[0].certificate_digest = "fixture:primitive-operator-domain";
    var certified_report = try validation.validate(std.testing.allocator, &program, .core);
    defer certified_report.deinit();
    try std.testing.expect(!certified_report.contains(.unproved_primitive_operator_domain));
    try std.testing.expect(!certified_report.contains(.claim_predicate_purpose_mismatch));
}

test "instructions retain multiple independently typed claims" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_left.index()].type = .dynamic;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation.binary.mode = .primitive;

    const terms = [_]ir.SolverTerm{
        .{
            .id = ir.SolverTermId.fromIndex(0),
            .sort = .{ .kind = .boolean },
            .operation = .{ .semantic_atom = .{ .no_metamethod_dispatch = fixture.i_sum } },
        },
        .{
            .id = ir.SolverTermId.fromIndex(1),
            .sort = .{ .kind = .boolean },
            .operation = .{ .semantic_atom = .{ .primitive_operator_domain = fixture.i_sum } },
        },
    };
    const queries = [_]ir.SolverQuery{
        .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(0) },
        .{ .id = ir.QueryId.fromIndex(1), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(1) },
    };
    const certificates = [_]ir.SolverCertificate{
        .{
            .id = ir.CertificateId.fromIndex(0),
            .query = ir.QueryId.fromIndex(0),
            .engine = .imported,
            .resolution = .proved,
            .evidence = &.{fixture.proof},
            .certificate_digest = "fixture:no-metamethod-dispatch",
        },
        .{
            .id = ir.CertificateId.fromIndex(1),
            .query = ir.QueryId.fromIndex(1),
            .engine = .imported,
            .resolution = .proved,
            .evidence = &.{fixture.proof},
            .certificate_digest = "fixture:primitive-operator-domain",
        },
    };
    const claims = [_]ir.Claim{
        .{
            .id = ir.ClaimId.fromIndex(0),
            .subject = .{ .instruction = fixture.i_sum },
            .predicate = ir.SolverTermId.fromIndex(0),
            .purpose = .{ .no_metamethod_dispatch = .pure },
            .status = .proved,
            .evidence = &.{fixture.proof},
            .certificate = ir.CertificateId.fromIndex(0),
        },
        .{
            .id = ir.ClaimId.fromIndex(1),
            .subject = .{ .instruction = fixture.i_sum },
            .predicate = ir.SolverTermId.fromIndex(1),
            .purpose = .{ .primitive_operator_domain = .pure },
            .status = .proved,
            .required_for_emission = true,
            .evidence = &.{fixture.proof},
            .certificate = ir.CertificateId.fromIndex(1),
        },
    };
    const instruction_claims = [_]ir.ClaimId{ ir.ClaimId.fromIndex(0), ir.ClaimId.fromIndex(1) };
    instructions[fixture.i_sum.index()].claims = &instruction_claims;
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.certificates = &certificates;
    program.claims = &claims;

    var valid_report = try validation.validate(std.testing.allocator, &program, .core);
    defer valid_report.deinit();
    try std.testing.expect(!valid_report.contains(.unproved_primitive_operator_domain));
    try std.testing.expect(!valid_report.contains(.duplicate_instruction_claim));
    try std.testing.expect(!valid_report.contains(.instruction_claim_subject_mismatch));
    try std.testing.expect(!valid_report.contains(.unlisted_instruction_claim));

    const duplicate_claims = [_]ir.ClaimId{ ir.ClaimId.fromIndex(0), ir.ClaimId.fromIndex(0), ir.ClaimId.fromIndex(1) };
    instructions[fixture.i_sum.index()].claims = &duplicate_claims;
    var duplicate_report = try validation.validate(std.testing.allocator, &program, .core);
    defer duplicate_report.deinit();
    try std.testing.expect(duplicate_report.contains(.duplicate_instruction_claim));

    const first_claim_only = [_]ir.ClaimId{ir.ClaimId.fromIndex(0)};
    const misplaced_claim = [_]ir.ClaimId{ir.ClaimId.fromIndex(1)};
    instructions[fixture.i_sum.index()].claims = &first_claim_only;
    instructions[fixture.i_result.index()].claims = &misplaced_claim;
    var ownership_report = try validation.validate(std.testing.allocator, &program, .core);
    defer ownership_report.deinit();
    try std.testing.expect(ownership_report.contains(.instruction_claim_subject_mismatch));
    try std.testing.expect(ownership_report.contains(.unlisted_instruction_claim));
}

test "no-metamethod proofs reduce only dispatch-related effect minima" {
    const fixture = lifter.fixtures.arithmetic_module;

    {
        var values = fixture.values;
        values[fixture.v_left.index()].type = .dynamic;
        var instructions = fixture.instructions;
        instructions[fixture.i_sum.index()].effects = .{ .precision = .exact, .may_throw = true };
        var program = fixture.program;
        program.values = &values;
        program.instructions = &instructions;

        var unproved_report = try validation.validate(std.testing.allocator, &program, .core);
        defer unproved_report.deinit();
        try std.testing.expect(unproved_report.contains(.understated_operator_effects));

        const terms = [_]ir.SolverTerm{.{
            .id = ir.SolverTermId.fromIndex(0),
            .sort = .{ .kind = .boolean },
            .operation = .{ .semantic_atom = .{ .no_metamethod_dispatch = fixture.i_sum } },
        }};
        const queries = [_]ir.SolverQuery{.{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .goal = ir.SolverTermId.fromIndex(0),
        }};
        const certificates = [_]ir.SolverCertificate{.{
            .id = ir.CertificateId.fromIndex(0),
            .query = ir.QueryId.fromIndex(0),
            .engine = .imported,
            .resolution = .proved,
            .evidence = &.{fixture.proof},
            .certificate_digest = "fixture:no-operator-dispatch",
        }};
        var claims = [_]ir.Claim{.{
            .id = ir.ClaimId.fromIndex(0),
            .subject = .{ .instruction = fixture.i_sum },
            .predicate = ir.SolverTermId.fromIndex(0),
            .purpose = .{ .no_metamethod_dispatch = instructions[fixture.i_sum.index()].effects },
            .status = .proved,
            .evidence = &.{fixture.proof},
            .certificate = ir.CertificateId.fromIndex(0),
        }};
        const instruction_claims = [_]ir.ClaimId{ir.ClaimId.fromIndex(0)};
        instructions[fixture.i_sum.index()].claims = &instruction_claims;
        program.solver_terms = &terms;
        program.queries = &queries;
        program.certificates = &certificates;
        program.claims = &claims;

        var proved_report = try validation.validate(std.testing.allocator, &program, .core);
        defer proved_report.deinit();
        try std.testing.expect(!proved_report.contains(.understated_operator_effects));

        instructions[fixture.i_sum.index()].effects = .pure;
        claims[0].purpose = .{ .no_metamethod_dispatch = .pure };
        var still_throwing_report = try validation.validate(std.testing.allocator, &program, .core);
        defer still_throwing_report.deinit();
        try std.testing.expect(still_throwing_report.contains(.understated_operator_effects));
    }

    {
        var instructions = fixture.instructions;
        instructions[fixture.i_sum.index()].operation = .{ .table_get = .{
            .table = fixture.v_left,
            .key = fixture.v_right,
            .mode = .semantic,
        } };
        instructions[fixture.i_sum.index()].effects = .raw_table_read;
        var program = fixture.program;
        program.instructions = &instructions;

        var unproved_report = try validation.validate(std.testing.allocator, &program, .core);
        defer unproved_report.deinit();
        try std.testing.expect(unproved_report.contains(.understated_table_get_effects));

        const terms = [_]ir.SolverTerm{.{
            .id = ir.SolverTermId.fromIndex(0),
            .sort = .{ .kind = .boolean },
            .operation = .{ .semantic_atom = .{ .no_metamethod_dispatch = fixture.i_sum } },
        }};
        const queries = [_]ir.SolverQuery{.{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .goal = ir.SolverTermId.fromIndex(0),
        }};
        const certificates = [_]ir.SolverCertificate{.{
            .id = ir.CertificateId.fromIndex(0),
            .query = ir.QueryId.fromIndex(0),
            .engine = .imported,
            .resolution = .proved,
            .evidence = &.{fixture.proof},
            .certificate_digest = "fixture:no-table-dispatch",
        }};
        const claims = [_]ir.Claim{.{
            .id = ir.ClaimId.fromIndex(0),
            .subject = .{ .instruction = fixture.i_sum },
            .predicate = ir.SolverTermId.fromIndex(0),
            .purpose = .{ .no_metamethod_dispatch = .raw_table_read },
            .status = .proved,
            .evidence = &.{fixture.proof},
            .certificate = ir.CertificateId.fromIndex(0),
        }};
        const instruction_claims = [_]ir.ClaimId{ir.ClaimId.fromIndex(0)};
        instructions[fixture.i_sum.index()].claims = &instruction_claims;
        program.solver_terms = &terms;
        program.queries = &queries;
        program.certificates = &certificates;
        program.claims = &claims;

        var proved_report = try validation.validate(std.testing.allocator, &program, .core);
        defer proved_report.deinit();
        try std.testing.expect(!proved_report.contains(.understated_table_get_effects));
    }
}

test "native namecall requires dynamic effects and a source-representable method" {
    const fixture = lifter.fixtures.arithmetic_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation = .{ .namecall = .{
        .receiver = fixture.v_left,
        .method = "run",
        .arguments = &.{fixture.v_right},
        .result_arity = .{ .fixed = 1 },
    } };
    instructions[fixture.i_sum.index()].effects = .pure;
    var program = fixture.program;
    program.instructions = &instructions;

    var effect_report = try validation.validate(std.testing.allocator, &program, .core);
    defer effect_report.deinit();
    try std.testing.expect(effect_report.contains(.invalid_namecall_effects));

    instructions[fixture.i_sum.index()].effects = .namecall;
    instructions[fixture.i_sum.index()].operation.namecall.method = "not a method";
    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.contains(.unsupported_readable_namecall));
}

test "readable admission and emission are total for runtime unary operators" {
    const rows = [_]UnaryOperatorRow{
        unaryOperatorRow(.logical_not, .boolean, .boolean, "return not left"),
        unaryOperatorRow(.negate, .number, .number, "return -left"),
        unaryOperatorRow(.length, .string, .integer, "return #left"),
        bitUnaryOperatorRow(.bit_not, "return __lifter_bit32_bnot(left)", "bit32.bnot"),
    };
    try std.testing.expectEqual(std.meta.fields(ir.UnaryOperator).len, rows.len);

    const modes = [_]ir.OperatorMode{ .semantic, .primitive };
    for (rows) |row| {
        const first_mode: usize = if (row.primitive_only) 1 else 0;
        for (modes[first_mode..]) |mode| {
            try expectReadableOperatorRow(
                unaryOperation(row.operator, mode),
                row.operand_type,
                .dynamic,
                row.result_type,
                .pure,
                row.expected_expression,
                row.expected_capability,
                .clean,
            );
        }
    }
}

test "readable admission and emission are total for runtime binary operators" {
    const rows = [_]BinaryOperatorRow{
        binaryOperatorRow(.add, .number, .number, "return left + right"),
        binaryOperatorRow(.subtract, .number, .number, "return left - right"),
        binaryOperatorRow(.multiply, .number, .number, "return left * right"),
        binaryOperatorRow(.divide, .number, .number, "return left / right"),
        binaryOperatorRow(.floor_divide, .number, .number, "return left // right"),
        binaryOperatorRow(.modulo, .number, .number, "return left % right"),
        binaryOperatorRow(.power, .number, .number, "return left ^ right"),
        binaryOperatorRow(.concat, .string, .string, "return left .. right"),
        binaryOperatorRow(.equal, .string, .boolean, "return left == right"),
        binaryOperatorRow(.not_equal, .string, .boolean, "return left ~= right"),
        binaryOperatorRow(.less, .string, .boolean, "return left < right"),
        binaryOperatorRow(.less_equal, .string, .boolean, "return left <= right"),
        binaryOperatorRow(.greater, .string, .boolean, "return left > right"),
        binaryOperatorRow(.greater_equal, .string, .boolean, "return left >= right"),
        binaryOperatorRow(.logical_and, .boolean, .boolean, "return left and right"),
        binaryOperatorRow(.logical_or, .boolean, .boolean, "return left or right"),
        bitBinaryOperatorRow(.bit_and, "return __lifter_bit32_band(left, right)", "bit32.band"),
        bitBinaryOperatorRow(.bit_or, "return __lifter_bit32_bor(left, right)", "bit32.bor"),
        bitBinaryOperatorRow(.bit_xor, "return __lifter_bit32_bxor(left, right)", "bit32.bxor"),
        bitBinaryOperatorRow(.shift_left, "return __lifter_bit32_lshift(left, right)", "bit32.lshift"),
        bitBinaryOperatorRow(.shift_right, "return __lifter_bit32_rshift(left, right)", "bit32.rshift"),
    };
    try std.testing.expectEqual(std.meta.fields(ir.BinaryOperator).len, rows.len);

    const modes = [_]ir.OperatorMode{ .semantic, .primitive };
    const shift_behaviors = [_]ir.ShiftBehavior{ .luau_bit32, .zero_saturating };
    for (rows) |row| {
        const first_mode: usize = if (row.primitive_only) 1 else 0;
        for (modes[first_mode..]) |mode| {
            const is_shift = row.operator == .shift_left or row.operator == .shift_right;
            const behaviors: []const ir.ShiftBehavior = if (is_shift) &shift_behaviors else &.{};
            if (behaviors.len == 0) {
                try expectReadableOperatorRow(
                    binaryOperation(row.operator, mode, null),
                    row.left_type,
                    row.right_type,
                    row.result_type,
                    .pure,
                    row.expected_expression,
                    row.expected_capability,
                    .clean,
                );
                continue;
            }
            for (behaviors) |behavior| {
                const expected_expression = switch (behavior) {
                    .luau_bit32 => row.expected_expression,
                    .zero_saturating => switch (row.operator) {
                        .shift_left => "return (if right >= 32 then 0 else __lifter_bit32_lshift(left, right))",
                        .shift_right => "return (if right >= 32 then 0 else __lifter_bit32_rshift(left, right))",
                        else => unreachable,
                    },
                };
                try expectReadableOperatorRow(
                    binaryOperation(row.operator, mode, behavior),
                    row.left_type,
                    row.right_type,
                    row.result_type,
                    .pure,
                    expected_expression,
                    row.expected_capability,
                    .clean,
                );
            }
        }
    }
}

test "dynamic runtime operator dispatch is effect-complete before emission" {
    const operation = binaryOperation(.add, .semantic, null);
    try expectReadableOperatorRow(
        operation,
        .dynamic,
        .dynamic,
        .dynamic,
        .dynamic_call,
        "left + right",
        null,
        .clean,
    );
    try expectReadableOperatorRow(
        operation,
        .dynamic,
        .dynamic,
        .dynamic,
        .pure,
        "",
        null,
        .understated_effects,
    );

    const table_type: ir.ValueType = .{ .kind = .table };
    try expectReadableOperatorRow(
        operation,
        table_type,
        table_type,
        .dynamic,
        .dynamic_call,
        "left + right",
        null,
        .clean,
    );
}

test "malformed runtime operator rows stop at typed readable diagnostics" {
    const table_type: ir.ValueType = .{ .kind = .table };
    const rows = [_]RejectedOperatorRow{
        .{ .operation = unaryOperation(.negate, .semantic), .left_type = .number, .result_type = .string, .expectation = .result_type_mismatch },
        .{ .operation = binaryOperation(.concat, .semantic, null), .left_type = .string, .right_type = .string, .result_type = .number, .expectation = .result_type_mismatch },
        .{ .operation = unaryOperation(.negate, .primitive), .left_type = table_type, .result_type = .number, .expectation = .unproved_primitive_domain },
        .{ .operation = binaryOperation(.add, .primitive, null), .left_type = table_type, .right_type = table_type, .result_type = .number, .expectation = .unproved_primitive_domain },
        .{ .operation = unaryOperation(.bit_not, .primitive), .left_type = .integer, .result_type = .integer, .expectation = .unsupported_bit_operation },
        .{ .operation = binaryOperation(.bit_and, .semantic, null), .left_type = operator_u32_type, .right_type = operator_u32_type, .result_type = operator_u32_type, .expectation = .unsupported_bit_operation },
        .{ .operation = binaryOperation(.shift_left, .primitive, null), .left_type = operator_u32_type, .right_type = operator_u32_type, .result_type = operator_u32_type, .expectation = .missing_shift_behavior },
        .{ .operation = binaryOperation(.add, .semantic, .luau_bit32), .left_type = .number, .right_type = .number, .result_type = .number, .expectation = .unexpected_shift_behavior },
        .{ .operation = binaryOperation(.add, .semantic, null), .left_type = .number, .right_type = .number, .result_type = .number, .effects = .{}, .expectation = .unknown_effects },
    };
    for (rows) |row| {
        try expectReadableOperatorRow(
            row.operation,
            row.left_type,
            row.right_type,
            row.result_type,
            row.effects,
            "",
            null,
            row.expectation,
        );
    }
}
