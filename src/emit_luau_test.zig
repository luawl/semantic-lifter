const std = @import("std");
const lifter = @import("semantic_lifter");
const ir = lifter.ir;
const emitAlloc = lifter.emit_luau.emitStandardLuauAlloc;

test "dispatch option shares readable admission and preserves the default emitter" {
    const program = &lifter.fixtures.arithmetic_module.program;
    const original = try emitAlloc(std.testing.allocator, program);
    defer std.testing.allocator.free(original);
    const automatic = try lifter.emit_luau.emitAllocForTargetWithOptions(
        std.testing.allocator,
        program,
        .standard_luau,
        .{},
    );
    defer std.testing.allocator.free(automatic);
    try std.testing.expectEqualStrings(original, automatic);
    const dispatcher = try lifter.emit_luau.emitAllocForTargetWithOptions(
        std.testing.allocator,
        program,
        .standard_luau,
        .{ .force_dispatcher = true },
    );
    defer std.testing.allocator.free(dispatcher);
    try std.testing.expect(std.mem.indexOf(u8, dispatcher, "local __lifter_pc") != null);
    try std.testing.expect(std.mem.indexOf(u8, dispatcher, "while true do") != null);

    var invalid = program.*;
    invalid.blocks = &.{};
    try std.testing.expectError(error.InvalidIr, lifter.emit_luau.emitAllocForTargetWithOptions(
        std.testing.allocator,
        &invalid,
        .standard_luau,
        .{ .force_dispatcher = true },
    ));
}

/// One function that reads the host global `__make_closure` and returns it: a
/// neutral handoff that merely names that global.
const ambient_closure_read = struct {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const get_id = ir.InstructionId.fromIndex(0);
    const closure = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = closure, .function = function_id, .name_hint = "make_closure", .origin = .{ .instruction_result = .{ .instruction = get_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = get_id, .block = block_id, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .mode = .semantic, .name = "__make_closure" } }, .results = &.{closure}, .effects = .semantic_environment_read, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{.{ .id = block_id, .function = function_id, .instructions = &.{get_id}, .terminator = .{ .return_values = &.{closure} }, .evidence = &.{proof} }};
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &.{block_id}, .entry_block = block_id, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:ambient-closure-read" }};
    const program: ir.Program = .{
        .program_id = "ambient-closure-read",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };
};

test "neutral emission defines no helper for an ambient __make_closure read" {
    const source = try emitAlloc(std.testing.allocator, &ambient_closure_read.program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "__make_closure") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local function __make_closure") == null);
}

test "registered ambient helper is emitted once for its ambient read" {
    const helpers = [_]lifter.luau_runtime.AmbientHelper{.{
        .name = "__make_closure",
        .source = "local function __make_closure(target)\n  return target\nend\n\n",
    }};
    const source = try lifter.emit_luau.emitAllocForTargetWithOptions(
        std.testing.allocator,
        &ambient_closure_read.program,
        .standard_luau,
        .{ .ambient_helpers = &helpers },
    );
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, helpers[0].source) != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "local function __make_closure"));
}

test "generic semantic IR emits readable Luau without family knowledge" {
    const fixtures = lifter.fixtures;
    const source = try emitAlloc(std.testing.allocator, &fixtures.arithmetic_module.program);
    defer std.testing.allocator.free(source);
    try std.testing.expectEqualStrings(
        \\local fn_add_and_double
        \\fn_add_and_double = function(left, right)
        \\  return (left + right) * 2
        \\end
        \\
        \\return fn_add_and_double
        \\
    , source);
}

test "forced dispatcher lowers generic iteration protocol" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const iterator = ir.ValueId.fromIndex(0);
    const state = ir.ValueId.fromIndex(1);
    const control = ir.ValueId.fromIndex(2);
    const initial = ir.ValueId.fromIndex(3);
    const has_value = ir.ValueId.fromIndex(4);
    const prepared_iterator = ir.ValueId.fromIndex(5);
    const prepared_state = ir.ValueId.fromIndex(6);
    const first = ir.ValueId.fromIndex(7);
    const second = ir.ValueId.fromIndex(8);
    const values = [_]ir.Value{
        .{ .id = iterator, .function = function_id, .type = .dynamic, .name_hint = "iterator", .origin = .{ .parameter = 0 } },
        .{ .id = state, .function = function_id, .type = .dynamic, .name_hint = "state", .origin = .{ .parameter = 1 } },
        .{ .id = control, .function = function_id, .type = .dynamic, .name_hint = "control", .origin = .{ .parameter = 2 } },
        .{ .id = initial, .function = function_id, .type = .boolean, .name_hint = "initial", .origin = .{ .parameter = 3 } },
        .{ .id = has_value, .function = function_id, .type = .boolean, .name_hint = "has_value", .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } } },
        .{ .id = prepared_iterator, .function = function_id, .type = .dynamic, .name_hint = "prepared_iterator", .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 1 } } },
        .{ .id = prepared_state, .function = function_id, .type = .dynamic, .name_hint = "prepared_state", .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 2 } } },
        .{ .id = first, .function = function_id, .type = .dynamic, .name_hint = "first", .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 3 } } },
        .{ .id = second, .function = function_id, .type = .dynamic, .name_hint = "second", .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 4 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = block_id,
        .operation = .{ .generic_for_next = .{
            .iterator = iterator,
            .state = state,
            .control = control,
            .initial = initial,
            .variable_count = 2,
        } },
        .results = &.{ has_value, prepared_iterator, prepared_state, first, second },
        .effects = .generic_for_next,
        .evidence = &.{proof},
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{instruction_id},
        .terminator = .{ .return_values = &.{ has_value, prepared_iterator, prepared_state, first, second } },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ iterator, state, control, initial },
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:generic-for-dispatch-emission" }};
    const program: ir.Program = .{
        .program_id = "generic-for-dispatch-emission",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const source = try lifter.emit_luau.emitAdmittedAllocForTargetWithOptions(
        std.testing.allocator,
        &program,
        .standard_luau,
        .{ .force_dispatcher = true },
    );
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_getmetatable") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_next") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_type") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_generic_method") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, " ~= nil then") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, " = __lifter_generic_iterator") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_generic_iterator(__lifter_generic_state") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "has_value = first ~= nil") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "first, second =") != null);
}

test "forced dispatcher lowers luau numeric iteration protocol" {
    // The flat layout renders the default `luau_numeric` mode itself. A one-shot native
    // `for` coerces the three operands on the initial entry (FORNPREP's order and messages), a later entry advances by
    // the coerced step, and the test reads the step's sign without advancing first.
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const control = ir.ValueId.fromIndex(0);
    const limit = ir.ValueId.fromIndex(1);
    const step = ir.ValueId.fromIndex(2);
    const initial = ir.ValueId.fromIndex(3);
    const has_value = ir.ValueId.fromIndex(4);
    const next_limit = ir.ValueId.fromIndex(5);
    const next_step = ir.ValueId.fromIndex(6);
    const next_control = ir.ValueId.fromIndex(7);
    const values = [_]ir.Value{
        .{ .id = control, .function = function_id, .type = .dynamic, .name_hint = "control", .origin = .{ .parameter = 0 } },
        .{ .id = limit, .function = function_id, .type = .dynamic, .name_hint = "limit", .origin = .{ .parameter = 1 } },
        .{ .id = step, .function = function_id, .type = .dynamic, .name_hint = "step", .origin = .{ .parameter = 2 } },
        .{ .id = initial, .function = function_id, .type = .boolean, .name_hint = "initial", .origin = .{ .parameter = 3 } },
        .{ .id = has_value, .function = function_id, .type = .boolean, .name_hint = "has_value", .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } } },
        .{ .id = next_limit, .function = function_id, .type = .number, .name_hint = "next_limit", .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 1 } } },
        .{ .id = next_step, .function = function_id, .type = .number, .name_hint = "next_step", .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .type = .number, .name_hint = "next_control", .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 3 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = block_id,
        .operation = .{ .numeric_for_next = .{
            .control = control,
            .limit = limit,
            .step = step,
            .initial = initial,
        } },
        .results = &.{ has_value, next_limit, next_step, next_control },
        .effects = .numeric_for_next,
        .evidence = &.{proof},
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{instruction_id},
        .terminator = .{ .return_values = &.{ has_value, next_limit, next_step, next_control } },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ control, limit, step, initial },
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:luau-numeric-dispatch-emission" }};
    const program: ir.Program = .{
        .program_id = "luau-numeric-dispatch-emission",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const source = try lifter.emit_luau.emitAdmittedAllocForTargetWithOptions(
        std.testing.allocator,
        &program,
        .standard_luau,
        .{ .force_dispatcher = true },
    );
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "if initial then") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, " = control, limit, step do break end") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "next_limit = limit * 1") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "next_step = step * 1") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "next_control = control * 1") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "next_control = control + next_step") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "if next_step > 0 then") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "has_value = next_control <= next_limit") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "has_value = next_limit <= next_control") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "next_step <= 0") == null);
}

test "repeated table reads preserve fixed result calls and nil positions" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(0);
    const prefix = ir.ValueId.fromIndex(1);
    const table = ir.ValueId.fromIndex(2);
    const key = ir.ValueId.fromIndex(3);
    const from = ir.ValueId.fromIndex(4);
    const to = ir.ValueId.fromIndex(5);
    const step = ir.ValueId.fromIndex(6);
    const first = ir.ValueId.fromIndex(7);
    const second = ir.ValueId.fromIndex(8);
    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = prefix, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = table, .function = function_id, .type = .{ .kind = .table }, .origin = .{ .parameter = 2 } },
        .{ .id = key, .function = function_id, .type = .integer, .origin = .{ .parameter = 3 } },
        .{ .id = from, .function = function_id, .type = .integer, .origin = .{ .parameter = 4 } },
        .{ .id = to, .function = function_id, .type = .integer, .origin = .{ .parameter = 5 } },
        .{ .id = step, .function = function_id, .type = .integer, .origin = .{ .parameter = 6 } },
        .{ .id = first, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } } },
        .{ .id = second, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 1 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = block_id,
        .operation = .{ .call_repeated_table_get = .{
            .callee = callee,
            .prefix_arguments = &.{prefix},
            .table = table,
            .key = key,
            .from = from,
            .to = to,
            .step = step,
            .result_arity = .{ .fixed = 2 },
        } },
        .results = &.{ first, second },
        .effects = .dynamic_call,
        .evidence = &.{proof},
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{instruction_id},
        .terminator = .{ .return_values = &.{ first, second } },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ callee, prefix, table, key, from, to, step },
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:generic-repeated-table-call",
    }};
    const program: ir.Program = .{
        .program_id = "generic-repeated-table-call",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "for __lifter_repeated_cursor_0") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "table.unpack") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_repeated_count_0 + 1") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_repeated_table_0[__lifter_repeated_key_0]") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "return __lifter_repeated_callee_0(__lifter_repeated_prefix_0_0, __lifter_table_unpack(__lifter_repeated_values_0, 1, __lifter_repeated_count_0))") != null);
}

test "nested binary emission follows Luau precedence and associativity" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    var instructions = fixture.instructions;
    var blocks = fixture.blocks;
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.blocks = &blocks;

    blocks[fixture.b_add.index()].instructions = &.{ fixture.i_factor, fixture.i_sum, fixture.i_result };
    instructions[fixture.i_sum.index()].operation = .{ .binary = .{ .operator = .multiply, .left = fixture.v_right, .right = fixture.v_factor } };
    instructions[fixture.i_result.index()].operation = .{ .binary = .{ .operator = .add, .left = fixture.v_left, .right = fixture.v_sum } };
    const higher_precedence = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(higher_precedence);
    try std.testing.expect(std.mem.indexOf(u8, higher_precedence, "return left + right * 2") != null);

    instructions[fixture.i_sum.index()].operation = .{ .binary = .{ .operator = .subtract, .left = fixture.v_right, .right = fixture.v_factor } };
    instructions[fixture.i_result.index()].operation = .{ .binary = .{ .operator = .subtract, .left = fixture.v_left, .right = fixture.v_sum } };
    const right_nested = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(right_nested);
    try std.testing.expect(std.mem.indexOf(u8, right_nested, "return left - (right - 2)") != null);

    blocks[fixture.b_add.index()].instructions = &.{ fixture.i_sum, fixture.i_factor, fixture.i_result };
    instructions[fixture.i_sum.index()].operation = .{ .binary = .{ .operator = .subtract, .left = fixture.v_left, .right = fixture.v_right } };
    instructions[fixture.i_result.index()].operation = .{ .binary = .{ .operator = .subtract, .left = fixture.v_sum, .right = fixture.v_factor } };
    const left_nested = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(left_nested);
    try std.testing.expect(std.mem.indexOf(u8, left_nested, "return left - right - 2") != null);

    values[fixture.v_sum.index()].type = .number;
    values[fixture.v_result.index()].type = .number;
    blocks[fixture.b_add.index()].instructions = &.{ fixture.i_factor, fixture.i_sum, fixture.i_result };
    instructions[fixture.i_sum.index()].operation = .{ .binary = .{ .operator = .power, .left = fixture.v_right, .right = fixture.v_factor } };
    instructions[fixture.i_result.index()].operation = .{ .binary = .{ .operator = .power, .left = fixture.v_left, .right = fixture.v_sum } };
    const right_power = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(right_power);
    try std.testing.expect(std.mem.indexOf(u8, right_power, "return left ^ right ^ 2") != null);

    blocks[fixture.b_add.index()].instructions = &.{ fixture.i_sum, fixture.i_factor, fixture.i_result };
    instructions[fixture.i_sum.index()].operation = .{ .binary = .{ .operator = .power, .left = fixture.v_left, .right = fixture.v_right } };
    instructions[fixture.i_result.index()].operation = .{ .binary = .{ .operator = .power, .left = fixture.v_sum, .right = fixture.v_factor } };
    const left_power = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(left_power);
    try std.testing.expect(std.mem.indexOf(u8, left_power, "return (left ^ right) ^ 2") != null);

    values[fixture.v_sum.index()].type = .integer;
    values[fixture.v_result.index()].type = .integer;
    instructions[fixture.i_sum.index()].operation = .{ .unary = .{ .operator = .negate, .operand = fixture.v_left } };
    instructions[fixture.i_result.index()].operation = .{ .unary = .{ .operator = .negate, .operand = fixture.v_sum } };
    const double_negate = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(double_negate);
    try std.testing.expect(std.mem.indexOf(u8, double_negate, "return -(-left)") != null);
    try std.testing.expect(std.mem.indexOf(u8, double_negate, "--left") == null);

    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = "-2" } };
    instructions[fixture.i_result.index()].operation = .{ .unary = .{ .operator = .negate, .operand = fixture.v_factor } };
    const negative_literal = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(negative_literal);
    try std.testing.expect(std.mem.indexOf(u8, negative_literal, "return -(-2)") != null);
    try std.testing.expect(std.mem.indexOf(u8, negative_literal, "--2") == null);

    values[fixture.v_result.index()].type = .number;
    instructions[fixture.i_result.index()].operation = .{ .binary = .{ .operator = .power, .left = fixture.v_factor, .right = fixture.v_left } };
    const negative_power_base = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(negative_power_base);
    try std.testing.expect(std.mem.indexOf(u8, negative_power_base, "return (-2) ^ left") != null);
}

test "canonical expression diamond folds its sole result into an immediate return" {
    const fixtures = lifter.fixtures;
    const source = try emitAlloc(std.testing.allocator, &fixtures.absolute_value_module.program);
    defer std.testing.allocator.free(source);

    try std.testing.expect(std.mem.indexOf(u8, source, "return if input < 0 then -input else input") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "if input < 0 then -input else input"));
    try std.testing.expect(std.mem.indexOf(u8, source, "local absolute") == null);

    const forwarded = ir.ValueId.fromIndex(6);
    const forwarding_values = [_]ir.Value{
        fixtures.absolute_value_module.values[0],
        fixtures.absolute_value_module.values[1],
        fixtures.absolute_value_module.values[2],
        fixtures.absolute_value_module.values[3],
        fixtures.absolute_value_module.values[4],
        fixtures.absolute_value_module.values[5],
        .{ .id = forwarded, .function = fixtures.absolute_value_module.f_absolute, .type = .number, .origin = .{ .block_parameter = .{ .block = fixtures.absolute_value_module.b_nonnegative, .index = 0 } } },
    };
    var forwarding_blocks = fixtures.absolute_value_module.blocks;
    var forwarding_branch = forwarding_blocks[fixtures.absolute_value_module.b_entry.index()].terminator.branch;
    forwarding_branch.else_edge = .{ .target = fixtures.absolute_value_module.b_nonnegative, .arguments = &.{fixtures.absolute_value_module.v_input} };
    forwarding_blocks[fixtures.absolute_value_module.b_entry.index()].terminator = .{ .branch = forwarding_branch };
    forwarding_blocks[fixtures.absolute_value_module.b_nonnegative.index()].parameters = &.{forwarded};
    forwarding_blocks[fixtures.absolute_value_module.b_nonnegative.index()].terminator = .{ .jump = .{ .target = fixtures.absolute_value_module.b_join, .arguments = &.{forwarded} } };
    var forwarding_program = fixtures.absolute_value_module.program;
    forwarding_program.values = &forwarding_values;
    forwarding_program.blocks = &forwarding_blocks;
    const forwarding_source = try emitAlloc(std.testing.allocator, &forwarding_program);
    defer std.testing.allocator.free(forwarding_source);
    try std.testing.expect(std.mem.indexOf(u8, forwarding_source, "return if input < 0 then -input else input") != null);

    const effect_id = ir.InstructionId.fromIndex(4);
    const instructions = [_]ir.Instruction{
        fixtures.absolute_value_module.instructions[0],
        fixtures.absolute_value_module.instructions[1],
        fixtures.absolute_value_module.instructions[2],
        fixtures.absolute_value_module.instructions[3],
        .{
            .id = effect_id,
            .block = fixtures.absolute_value_module.b_negative,
            .operation = .{ .environment_set = .{ .target = .{ .ambient = {} }, .name = "observed", .value = fixtures.absolute_value_module.v_input } },
            .results = &.{},
            .effects = .semantic_environment_write,
            .evidence = &.{fixtures.absolute_value_module.proof},
        },
    };
    var blocks = fixtures.absolute_value_module.blocks;
    blocks[fixtures.absolute_value_module.b_negative.index()].instructions = &.{ effect_id, fixtures.absolute_value_module.i_negate };
    var statement_program = fixtures.absolute_value_module.program;
    statement_program.instructions = &instructions;
    statement_program.blocks = &blocks;
    const statement_source = try emitAlloc(std.testing.allocator, &statement_program);
    defer std.testing.allocator.free(statement_source);
    try std.testing.expect(std.mem.indexOf(u8, statement_source, "if input < 0 then") != null);
    try std.testing.expect(std.mem.indexOf(u8, statement_source, "if (input < 0) then") == null);
    try std.testing.expect(std.mem.indexOf(u8, statement_source, "observed = input") != null);
    try std.testing.expect(std.mem.indexOf(u8, statement_source, "absolute = if") == null);

    var intervening_instructions = instructions;
    intervening_instructions[effect_id.index()].block = fixtures.absolute_value_module.b_join;
    var intervening_blocks = fixtures.absolute_value_module.blocks;
    intervening_blocks[fixtures.absolute_value_module.b_join.index()].instructions = &.{effect_id};
    var intervening_program = fixtures.absolute_value_module.program;
    intervening_program.instructions = &intervening_instructions;
    intervening_program.blocks = &intervening_blocks;
    const intervening_source = try emitAlloc(std.testing.allocator, &intervening_program);
    defer std.testing.allocator.free(intervening_source);
    const expression_assignment = std.mem.indexOf(u8, intervening_source, "absolute = if input < 0 then -input else input") orelse return error.TestUnexpectedResult;
    const intervening_effect = std.mem.indexOf(u8, intervening_source, "observed = input") orelse return error.TestUnexpectedResult;
    const delayed_return = std.mem.indexOf(u8, intervening_source, "return absolute") orelse return error.TestUnexpectedResult;
    try std.testing.expect(expression_assignment < intervening_effect and intervening_effect < delayed_return);

    var negated_instructions = instructions;
    negated_instructions[effect_id.index()].block = fixtures.absolute_value_module.b_nonnegative;
    var negated_blocks = fixtures.absolute_value_module.blocks;
    var negated_branch = negated_blocks[fixtures.absolute_value_module.b_entry.index()].terminator.branch;
    negated_branch.then_edge = .{ .target = fixtures.absolute_value_module.b_join };
    negated_blocks[fixtures.absolute_value_module.b_entry.index()].terminator = .{ .branch = negated_branch };
    negated_blocks[fixtures.absolute_value_module.b_negative.index()].terminator = .{ .jump = .{ .target = fixtures.absolute_value_module.b_join } };
    negated_blocks[fixtures.absolute_value_module.b_nonnegative.index()].instructions = &.{effect_id};
    negated_blocks[fixtures.absolute_value_module.b_nonnegative.index()].terminator = .{ .jump = .{ .target = fixtures.absolute_value_module.b_join } };
    negated_blocks[fixtures.absolute_value_module.b_join.index()].parameters = &.{};
    negated_blocks[fixtures.absolute_value_module.b_join.index()].terminator = .{ .return_values = &.{} };
    var negated_program = fixtures.absolute_value_module.program;
    negated_program.instructions = &negated_instructions;
    negated_program.values = fixtures.absolute_value_module.values[0..5];
    negated_program.blocks = &negated_blocks;
    const negated_source = try emitAlloc(std.testing.allocator, &negated_program);
    defer std.testing.allocator.free(negated_source);
    try std.testing.expect(std.mem.indexOf(u8, negated_source, "if not (input < 0) then") != null);
    try std.testing.expect(std.mem.indexOf(u8, negated_source, "if not input < 0 then") == null);
}

test "identical parameterized branch edges emit one unconditional transfer" {
    const fixture = lifter.fixtures.absolute_value_module;
    var blocks = fixture.blocks;
    var branch = blocks[fixture.b_entry.index()].terminator.branch;
    const common_edge: ir.Edge = .{ .target = fixture.b_join, .arguments = &.{fixture.v_input} };
    branch.then_edge = common_edge;
    branch.else_edge = common_edge;
    blocks[fixture.b_entry.index()].terminator = .{ .branch = branch };

    var program = fixture.program;
    program.blocks = &blocks;
    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);

    try std.testing.expect(std.mem.indexOf(u8, source, "if ") == null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "absolute = input"));
    try std.testing.expect(std.mem.indexOf(u8, source, "return absolute") != null);
}

test "nested expression diamond folds into its immediate nested return" {
    const fixture = lifter.fixtures.absolute_value_module;
    const enabled = ir.ValueId.fromIndex(fixture.values.len);
    const outer = ir.BlockId.fromIndex(fixture.blocks.len);
    const fallback = ir.BlockId.fromIndex(fixture.blocks.len + 1);

    var values: [fixture.values.len + 1]ir.Value = undefined;
    @memcpy(values[0..fixture.values.len], &fixture.values);
    values[enabled.index()] = .{
        .id = enabled,
        .function = fixture.f_absolute,
        .type = .boolean,
        .name_hint = "enabled",
        .origin = .{ .parameter = 1 },
    };

    var blocks: [fixture.blocks.len + 2]ir.Block = undefined;
    @memcpy(blocks[0..fixture.blocks.len], &fixture.blocks);
    blocks[outer.index()] = .{
        .id = outer,
        .function = fixture.f_absolute,
        .terminator = .{ .branch = .{
            .condition = enabled,
            .then_edge = .{ .target = fixture.b_entry },
            .else_edge = .{ .target = fallback },
        } },
        .evidence = &.{fixture.proof},
    };
    blocks[fallback.index()] = .{
        .id = fallback,
        .function = fixture.f_absolute,
        .terminator = .{ .return_values = &.{fixture.v_input} },
        .evidence = &.{fixture.proof},
    };

    var functions = fixture.functions;
    functions[fixture.f_absolute.index()].parameters = &.{ fixture.v_input, enabled };
    functions[fixture.f_absolute.index()].blocks = &.{ outer, fixture.b_join, fixture.b_negative, fixture.b_entry, fixture.b_nonnegative, fallback };
    functions[fixture.f_absolute.index()].entry_block = outer;

    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.values = &values;

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "return if input < 0 then -input else input") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local absolute\n") == null);
}

test "projected shared terminal emits each edge transfer and effect once" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const direct_entry = ir.BlockId.fromIndex(1);
    const nested_entry = ir.BlockId.fromIndex(2);
    const nested = ir.BlockId.fromIndex(3);
    const early = ir.BlockId.fromIndex(4);
    const join = ir.BlockId.fromIndex(5);
    const terminal = ir.BlockId.fromIndex(6);
    const effect = ir.InstructionId.fromIndex(0);
    const outer_condition = ir.ValueId.fromIndex(0);
    const inner_condition = ir.ValueId.fromIndex(1);
    const early_value = ir.ValueId.fromIndex(2);
    const fallback_value = ir.ValueId.fromIndex(3);
    const result = ir.ValueId.fromIndex(4);
    const values = [_]ir.Value{
        .{ .id = outer_condition, .function = function_id, .type = .boolean, .name_hint = "outer_condition", .origin = .{ .parameter = 0 } },
        .{ .id = inner_condition, .function = function_id, .type = .boolean, .name_hint = "inner_condition", .origin = .{ .parameter = 1 } },
        .{ .id = early_value, .function = function_id, .type = .string, .name_hint = "early_value", .origin = .{ .parameter = 2 } },
        .{ .id = fallback_value, .function = function_id, .type = .string, .name_hint = "fallback_value", .origin = .{ .parameter = 3 } },
        .{ .id = result, .function = function_id, .type = .string, .name_hint = "result", .origin = .{ .block_parameter = .{ .block = terminal, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = effect,
        .block = early,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "observed",
            .value = early_value,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
        .evidence = &.{proof},
    }};
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = outer_condition,
            .then_edge = .{ .target = nested_entry },
            .else_edge = .{ .target = direct_entry },
        } }, .evidence = &.{proof} },
        .{ .id = direct_entry, .function = function_id, .terminator = .{ .jump = .{ .target = join } }, .evidence = &.{proof} },
        .{ .id = nested_entry, .function = function_id, .terminator = .{ .jump = .{ .target = nested } }, .evidence = &.{proof} },
        .{ .id = nested, .function = function_id, .terminator = .{ .branch = .{
            .condition = inner_condition,
            .then_edge = .{ .target = early },
            .else_edge = .{ .target = join },
        } }, .evidence = &.{proof} },
        .{ .id = early, .function = function_id, .instructions = &.{effect}, .terminator = .{ .jump = .{ .target = terminal, .arguments = &.{early_value} } }, .evidence = &.{proof} },
        .{ .id = join, .function = function_id, .terminator = .{ .jump = .{ .target = terminal, .arguments = &.{fallback_value} } }, .evidence = &.{proof} },
        .{ .id = terminal, .function = function_id, .parameters = &.{result}, .terminator = .{ .return_values = &.{result} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ outer_condition, inner_condition, early_value, fallback_value },
        .blocks = &.{ terminal, nested, direct_entry, entry, join, early, nested_entry },
        .entry_block = entry,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:projected-shared-terminal",
    }};
    const program: ir.Program = .{
        .program_id = "projected-shared-terminal",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "observed = early_value"));
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "result = early_value"));
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "result = fallback_value"));
    try std.testing.expectEqual(@as(usize, 2), std.mem.count(u8, source, "return result"));
}

test "adjacent expression diamonds compose only across a sole instruction-free condition" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const middle = ir.BlockId.fromIndex(1);
    const join = ir.BlockId.fromIndex(2);
    const i_selector = ir.InstructionId.fromIndex(0);
    const i_true = ir.InstructionId.fromIndex(1);
    const i_false = ir.InstructionId.fromIndex(2);
    const i_yes = ir.InstructionId.fromIndex(3);
    const i_no = ir.InstructionId.fromIndex(4);
    const i_observe = ir.InstructionId.fromIndex(5);
    const v_selector = ir.ValueId.fromIndex(0);
    const v_true = ir.ValueId.fromIndex(1);
    const v_false = ir.ValueId.fromIndex(2);
    const v_yes = ir.ValueId.fromIndex(3);
    const v_no = ir.ValueId.fromIndex(4);
    const v_first = ir.ValueId.fromIndex(5);
    const v_result = ir.ValueId.fromIndex(6);
    const values = [_]ir.Value{
        .{ .id = v_selector, .function = function_id, .type = .boolean, .name_hint = "selector", .origin = .{ .instruction_result = .{ .instruction = i_selector, .index = 0 } } },
        .{ .id = v_true, .function = function_id, .type = .boolean, .name_hint = "true_case", .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
        .{ .id = v_false, .function = function_id, .type = .boolean, .name_hint = "false_case", .origin = .{ .instruction_result = .{ .instruction = i_false, .index = 0 } } },
        .{ .id = v_yes, .function = function_id, .type = .string, .name_hint = "yes", .origin = .{ .instruction_result = .{ .instruction = i_yes, .index = 0 } } },
        .{ .id = v_no, .function = function_id, .type = .string, .name_hint = "no", .origin = .{ .instruction_result = .{ .instruction = i_no, .index = 0 } } },
        .{ .id = v_first, .function = function_id, .type = .boolean, .name_hint = "first", .origin = .{ .block_parameter = .{ .block = middle, .index = 0 } } },
        .{ .id = v_result, .function = function_id, .name_hint = "result", .origin = .{ .block_parameter = .{ .block = join, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = i_selector, .block = entry, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_selector}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_true, .block = entry, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_false, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{v_false}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_yes, .block = entry, .operation = .{ .constant = .{ .string = "yes" } }, .results = &.{v_yes}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_no, .block = entry, .operation = .{ .constant = .{ .string = "no" } }, .results = &.{v_no}, .effects = .pure, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{ i_selector, i_true, i_false, i_yes, i_no }, .terminator = .{ .branch = .{ .condition = v_selector, .then_edge = .{ .target = middle, .arguments = &.{v_true} }, .else_edge = .{ .target = middle, .arguments = &.{v_false} } } }, .evidence = &.{proof} },
        .{ .id = middle, .function = function_id, .parameters = &.{v_first}, .terminator = .{ .branch = .{ .condition = v_first, .then_edge = .{ .target = join, .arguments = &.{v_yes} }, .else_edge = .{ .target = join, .arguments = &.{v_no} } } }, .evidence = &.{proof} },
        .{ .id = join, .function = function_id, .parameters = &.{v_result}, .terminator = .{ .return_values = &.{v_result} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &.{ entry, middle, join }, .entry_block = entry, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:adjacent-expression-composition" }};
    const program: ir.Program = .{
        .program_id = "adjacent-expression-composition",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const composed = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(composed);
    try std.testing.expect(std.mem.indexOf(u8, composed, "return if (if true then true else false) then \"yes\" else \"no\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, composed, "local result") == null);
    try std.testing.expect(std.mem.indexOf(u8, composed, "local first") == null);

    const else_return = ir.BlockId.fromIndex(3);
    var condition_blocks = [_]ir.Block{
        blocks[entry.index()],
        blocks[middle.index()],
        blocks[join.index()],
        .{ .id = else_return, .function = function_id, .terminator = .{ .return_values = &.{v_no} }, .evidence = &.{proof} },
    };
    condition_blocks[middle.index()].terminator = .{ .branch = .{
        .condition = v_first,
        .then_edge = .{ .target = join },
        .else_edge = .{ .target = else_return },
    } };
    condition_blocks[join.index()].parameters = &.{};
    condition_blocks[join.index()].terminator = .{ .return_values = &.{v_yes} };
    const condition_functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ entry, middle, join, else_return },
        .entry_block = entry,
        .evidence = &.{proof},
    }};
    var condition_program = program;
    condition_program.functions = &condition_functions;
    condition_program.blocks = &condition_blocks;
    condition_program.values = values[0..6];
    const composed_condition = try emitAlloc(std.testing.allocator, &condition_program);
    defer std.testing.allocator.free(composed_condition);
    try std.testing.expect(std.mem.indexOf(u8, composed_condition, "if (if true then true else false) then") != null);
    try std.testing.expect(std.mem.indexOf(u8, composed_condition, "  return \"yes\"\nend\nreturn \"no\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, composed_condition, "local first") == null);

    var multi_use_blocks = blocks;
    var multi_use_branch = multi_use_blocks[middle.index()].terminator.branch;
    multi_use_branch.then_edge.arguments = &.{v_first};
    multi_use_blocks[middle.index()].terminator = .{ .branch = multi_use_branch };
    var multi_use_program = program;
    multi_use_program.blocks = &multi_use_blocks;
    const multi_use = try emitAlloc(std.testing.allocator, &multi_use_program);
    defer std.testing.allocator.free(multi_use);
    try std.testing.expect(std.mem.indexOf(u8, multi_use, "local first = if true then true else false") != null);

    var effect_instructions: [6]ir.Instruction = undefined;
    @memcpy(effect_instructions[0..instructions.len], &instructions);
    effect_instructions[i_observe.index()] = .{
        .id = i_observe,
        .block = middle,
        .operation = .{ .environment_set = .{ .target = .{ .ambient = {} }, .name = "observed", .value = v_yes } },
        .results = &.{},
        .effects = .semantic_environment_write,
        .evidence = &.{proof},
    };
    var effect_blocks = blocks;
    effect_blocks[middle.index()].instructions = &.{i_observe};
    var effect_program = program;
    effect_program.instructions = &effect_instructions;
    effect_program.blocks = &effect_blocks;
    const effectful = try emitAlloc(std.testing.allocator, &effect_program);
    defer std.testing.allocator.free(effectful);
    const first_assignment = std.mem.indexOf(u8, effectful, "local first = if true then true else false") orelse return error.TestUnexpectedResult;
    const observed_write = std.mem.indexOf(u8, effectful, "observed = yes") orelse return error.TestUnexpectedResult;
    try std.testing.expect(first_assignment < observed_write);
}

test "fixed entry parameters bind from chunk arguments once" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const first = ir.ValueId.fromIndex(0);
    const second = ir.ValueId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = first, .function = function_id, .name_hint = "first", .origin = .{ .parameter = 0 } },
        .{ .id = second, .function = function_id, .name_hint = "second", .origin = .{ .parameter = 1 } },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .terminator = .{ .return_values = &.{ first, second } },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ first, second },
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:fixed-entry-parameters",
    }};
    const program: ir.Program = .{
        .program_id = "fixed-entry-parameters",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expectEqualStrings(
        \\local first, second = ...
        \\return first, second
        \\
    , source);

    var ignored_vararg_functions = functions;
    ignored_vararg_functions[0].is_variadic = true;
    var ignored_vararg_program = program;
    ignored_vararg_program.functions = &ignored_vararg_functions;
    var ignored_vararg_report = try lifter.validate.validate(std.testing.allocator, &ignored_vararg_program, .readable_luau);
    defer ignored_vararg_report.deinit();
    try std.testing.expect(ignored_vararg_report.isClean());
    const ignored_vararg_source = try emitAlloc(std.testing.allocator, &ignored_vararg_program);
    defer std.testing.allocator.free(ignored_vararg_source);
    try std.testing.expectEqualStrings(source, ignored_vararg_source);

    const vararg_pack = ir.ValuePackId.fromIndex(0);
    const packs = [_]ir.ValuePack{.{
        .id = vararg_pack,
        .function = function_id,
        .origin = .{ .varargs = function_id },
        .evidence = &.{proof},
    }};
    var mixed_functions = functions;
    mixed_functions[0].is_variadic = true;
    mixed_functions[0].vararg_pack = vararg_pack;
    var mixed_values = values;
    mixed_values[second.index()].name_hint = "select";
    var mixed_blocks = blocks;
    mixed_blocks[0].terminator = .{ .return_expanded = .{
        .values = &.{ first, second },
        .pack = vararg_pack,
    } };
    var mixed_program = program;
    mixed_program.functions = &mixed_functions;
    mixed_program.blocks = &mixed_blocks;
    mixed_program.values = &mixed_values;
    mixed_program.value_packs = &packs;
    var mixed_core_report = try lifter.validate.validate(std.testing.allocator, &mixed_program, .core);
    defer mixed_core_report.deinit();
    try std.testing.expect(mixed_core_report.isClean());
    var mixed_report = try lifter.validate.validate(std.testing.allocator, &mixed_program, .readable_luau);
    defer mixed_report.deinit();
    try std.testing.expect(mixed_report.isClean());
    const mixed_source = try emitAlloc(std.testing.allocator, &mixed_program);
    defer std.testing.allocator.free(mixed_source);
    try std.testing.expectEqualStrings(
        \\local __lifter_select = select
        \\
        \\local first, select_2 = ...
        \\return first, select_2, __lifter_select(3, ...)
        \\
    , mixed_source);

    var pack_return_blocks = mixed_blocks;
    pack_return_blocks[0].terminator = .{ .return_pack = vararg_pack };
    var pack_return_program = mixed_program;
    pack_return_program.blocks = &pack_return_blocks;
    const pack_return_source = try emitAlloc(std.testing.allocator, &pack_return_program);
    defer std.testing.allocator.free(pack_return_source);
    try std.testing.expectEqualStrings(
        \\local __lifter_select = select
        \\
        \\local first, select_2 = ...
        \\return __lifter_select(3, ...)
        \\
    , pack_return_source);
}

test "owned vararg packs emit as direct pack returns" {
    const fixtures = lifter.fixtures;
    const source = try emitAlloc(std.testing.allocator, &fixtures.variadic_identity_module.program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "fn_identity = function(...)") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "  return ...\n") != null);
}

test "immutable captures emit as lexical closure snapshots" {
    const fixtures = lifter.fixtures;
    const source = try emitAlloc(std.testing.allocator, &fixtures.immutable_closure_module.program);
    defer std.testing.allocator.free(source);

    try std.testing.expect(std.mem.indexOf(u8, source, "local captured_base") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local adder = function(delta)\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "    return base + delta\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "fn_adder") == null);
}

test "materialized closure snapshots have independent lexical blocks" {
    const fixture = lifter.fixtures.immutable_closure_module;
    const source_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const source_value = ir.ValueId.fromIndex(fixture.values.len);
    const source_results = [_]ir.ValueId{source_value};
    const source_bindings = [_]ir.CaptureBinding{.{ .value = source_value }};
    const source_instruction: ir.Instruction = .{
        .id = source_id,
        .block = fixture.b_factory,
        .operation = .{ .constant = .{ .integer = "41" } },
        .results = &source_results,
        .effects = .pure,
        .evidence = &.{fixture.proof},
    };
    var instructions = fixture.instructions ++ [_]ir.Instruction{source_instruction};
    instructions[fixture.i_make_adder.index()].operation.make_closure.bindings = &source_bindings;
    const values = fixture.values ++ [_]ir.Value{.{
        .id = source_value,
        .function = fixture.f_factory,
        .type = .integer,
        .name_hint = "source",
        .origin = .{ .instruction_result = .{ .instruction = source_id, .index = 0 } },
    }};
    var blocks = fixture.blocks;
    blocks[fixture.b_factory.index()].instructions = &.{ source_id, fixture.i_make_adder };
    var program = fixture.program;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source,
        \\  local adder
        \\  do
        \\    local captured_base = 41
        \\    adder = function(delta)
        \\      return captured_base + delta
        \\    end
        \\  end
    ) != null);
}

test "sole closure result initializes its lexical destination directly" {
    const fixture = lifter.fixtures.immutable_closure_module;
    const write_id = ir.InstructionId.fromIndex(3);
    const place_id = ir.PlaceId.fromIndex(0);
    const instructions = [_]ir.Instruction{
        fixture.instructions[0],
        fixture.instructions[1],
        fixture.instructions[2],
        .{ .id = write_id, .block = fixture.b_factory, .operation = .{ .place_write = .{ .place = place_id, .value = fixture.v_adder } }, .results = &.{}, .effects = .place_write, .evidence = &.{fixture.proof} },
    };
    const places = [_]ir.Place{.{
        .id = place_id,
        .function = fixture.f_factory,
        .type = .function,
        .name_hint = "adder",
        .origin = .{ .local = 0 },
        .evidence = &.{fixture.proof},
    }};
    var blocks = fixture.blocks;
    blocks[fixture.b_factory.index()].instructions = &.{ fixture.i_make_adder, write_id };
    blocks[fixture.b_factory.index()].terminator = .{ .return_values = &.{} };
    var functions = fixture.functions;
    functions[fixture.f_factory.index()].local_places = &.{place_id};
    const program: ir.Program = .{
        .program_id = "generic-closure-place-initializer",
        .entry_function = fixture.f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &fixture.values,
        .places = &places,
        .captures = &fixture.captures,
        .evidence = &fixture.evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "local adder = function(delta)") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "adder_2 = function") == null);
}

test "shared place captures emit as native lexical upvalues" {
    const fixtures = lifter.fixtures;
    const source = try emitAlloc(std.testing.allocator, &fixtures.shared_place_closure_module.program);
    defer std.testing.allocator.free(source);

    try std.testing.expect(std.mem.indexOf(u8, source, "  local state = start\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "  local state\n") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "    local next = state + delta\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "    state = next\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "current") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "captured_state") == null);
}

test "entry external place aliases propagate through child closures" {
    const fixture = lifter.fixtures.shared_place_closure_module;
    const root_capture = ir.CaptureId.fromIndex(fixture.captures.len);
    const binding_id = ir.ExternalBindingId.fromIndex(0);
    var places = fixture.places;
    places[fixture.p_state.index()].origin = .{ .capture = root_capture };
    const captures = fixture.captures ++ [_]ir.Capture{.{
        .id = root_capture,
        .function = fixture.f_factory,
        .kind = .{ .shared_place = fixture.p_state },
        .evidence = &.{fixture.proof},
    }};
    var functions = fixture.functions;
    functions[fixture.f_factory.index()].captures = &.{root_capture};
    functions[fixture.f_factory.index()].local_places = &.{};
    var instructions = fixture.instructions;
    instructions[fixture.i_export.index()].operation = .{ .function_ref = fixture.f_entry };
    const external_bindings = [_]ir.ExternalBinding{.{
        .id = binding_id,
        .kind = .shared_place,
        .type = .integer,
        .evidence = &.{fixture.proof},
    }};
    var program = fixture.program;
    program.entry_function = fixture.f_factory;
    program.entry_bindings = &.{binding_id};
    program.external_bindings = &external_bindings;
    program.functions = &functions;
    program.instructions = &instructions;
    program.places = &places;
    program.captures = &captures;

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "local __lifter_rawget = rawget") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local __lifter_rawset = rawset") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local __lifter_external_place_0, start = ...") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local counter = function(delta)") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_rawget(__lifter_external_place_0, 1) + delta") != null);
    try std.testing.expectEqual(@as(usize, 2), std.mem.count(u8, source, "__lifter_rawset(__lifter_external_place_0, 1,"));
    try std.testing.expect(std.mem.indexOf(u8, source, "captured_state") == null);

    var dead_blocks = fixture.blocks;
    dead_blocks[fixture.b_factory.index()].terminator = .{ .return_values = &.{} };
    var dead_program = program;
    dead_program.blocks = &dead_blocks;
    const dead_source = try emitAlloc(std.testing.allocator, &dead_program);
    defer std.testing.allocator.free(dead_source);
    try std.testing.expect(std.mem.indexOf(u8, dead_source, "local __lifter_rawget = rawget") == null);
    try std.testing.expect(std.mem.indexOf(u8, dead_source, "local __lifter_rawset = rawset") != null);
    try std.testing.expect(std.mem.indexOf(u8, dead_source, "local counter = function") == null);
}

test "capture before first write keeps the shared cell predeclared" {
    const fixture = lifter.fixtures.shared_place_closure_module;
    var blocks = fixture.blocks;
    blocks[fixture.b_factory.index()].instructions = &.{ fixture.i_make_counter, fixture.i_initialize };
    var program = fixture.program;
    program.blocks = &blocks;

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    const declaration = std.mem.indexOf(u8, source, "local state\n") orelse return error.TestUnexpectedResult;
    const closure = std.mem.indexOf(u8, source, "local counter = function") orelse return error.TestUnexpectedResult;
    const assignment = std.mem.indexOf(u8, source, "state = start") orelse return error.TestUnexpectedResult;
    try std.testing.expect(declaration < closure and closure < assignment);
    try std.testing.expect(std.mem.indexOf(u8, source, "local state = start") == null);
}

test "adjacent lexical snapshots inline into branches" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const then_block = ir.BlockId.fromIndex(1);
    const else_block = ir.BlockId.fromIndex(2);
    const constant_id = ir.InstructionId.fromIndex(0);
    const write_id = ir.InstructionId.fromIndex(1);
    const read_id = ir.InstructionId.fromIndex(2);
    const then_id = ir.InstructionId.fromIndex(3);
    const else_id = ir.InstructionId.fromIndex(4);
    const initial = ir.ValueId.fromIndex(0);
    const condition = ir.ValueId.fromIndex(1);
    const then_value = ir.ValueId.fromIndex(2);
    const else_value = ir.ValueId.fromIndex(3);
    const place_id = ir.PlaceId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = initial, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = constant_id, .index = 0 } } },
        .{ .id = condition, .function = function_id, .type = .boolean, .name_hint = "snapshot", .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } } },
        .{ .id = then_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = then_id, .index = 0 } } },
        .{ .id = else_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = else_id, .index = 0 } } },
    };
    const places = [_]ir.Place{.{ .id = place_id, .function = function_id, .type = .boolean, .name_hint = "flag", .origin = .{ .local = 0 }, .evidence = &.{proof} }};
    const instructions = [_]ir.Instruction{
        .{ .id = constant_id, .block = entry, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{initial}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = write_id, .block = entry, .operation = .{ .place_write = .{ .place = place_id, .value = initial } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
        .{ .id = read_id, .block = entry, .operation = .{ .place_read = place_id }, .results = &.{condition}, .effects = .place_read, .evidence = &.{proof} },
        .{ .id = then_id, .block = then_block, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{then_value}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = else_id, .block = else_block, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{else_value}, .effects = .pure, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{ constant_id, write_id, read_id }, .terminator = .{ .branch = .{ .condition = condition, .then_edge = .{ .target = then_block }, .else_edge = .{ .target = else_block } } }, .evidence = &.{proof} },
        .{ .id = then_block, .function = function_id, .instructions = &.{then_id}, .terminator = .{ .return_values = &.{then_value} }, .evidence = &.{proof} },
        .{ .id = else_block, .function = function_id, .instructions = &.{else_id}, .terminator = .{ .return_values = &.{else_value} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &.{ entry, then_block, else_block }, .entry_block = entry, .local_places = &.{place_id}, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:place-read-branch" }};
    const program: ir.Program = .{
        .program_id = "generic-place-read-branch",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "if flag then") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "snapshot") == null);
}

test "lexical snapshot inlining refuses multiple runtime uses" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const constant_id = ir.InstructionId.fromIndex(0);
    const write_id = ir.InstructionId.fromIndex(1);
    const read_id = ir.InstructionId.fromIndex(2);
    const initial = ir.ValueId.fromIndex(0);
    const snapshot = ir.ValueId.fromIndex(1);
    const place_id = ir.PlaceId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = initial, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = constant_id, .index = 0 } } },
        .{ .id = snapshot, .function = function_id, .type = .integer, .name_hint = "snapshot", .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } } },
    };
    const places = [_]ir.Place{.{ .id = place_id, .function = function_id, .type = .integer, .name_hint = "state", .origin = .{ .local = 0 }, .evidence = &.{proof} }};
    const instructions = [_]ir.Instruction{
        .{ .id = constant_id, .block = block_id, .operation = .{ .constant = .{ .integer = "7" } }, .results = &.{initial}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = write_id, .block = block_id, .operation = .{ .place_write = .{ .place = place_id, .value = initial } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
        .{ .id = read_id, .block = block_id, .operation = .{ .place_read = place_id }, .results = &.{snapshot}, .effects = .place_read, .evidence = &.{proof} },
    };
    var blocks = [_]ir.Block{.{ .id = block_id, .function = function_id, .instructions = &.{ constant_id, write_id, read_id }, .terminator = .{ .return_values = &.{ snapshot, snapshot } }, .evidence = &.{proof} }};
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &.{block_id}, .entry_block = block_id, .local_places = &.{place_id}, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:place-read-multi-use" }};
    var program: ir.Program = .{
        .program_id = "generic-place-read-multi-use",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
        .evidence = &evidence,
    };

    const multi_use = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(multi_use);
    try std.testing.expect(std.mem.indexOf(u8, multi_use, "local snapshot = state") != null);
    try std.testing.expect(std.mem.indexOf(u8, multi_use, "return snapshot, snapshot") != null);

    blocks[0].terminator = .{ .return_values = &.{snapshot} };
    program.blocks = &blocks;
    const sole_use = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(sole_use);
    try std.testing.expect(std.mem.indexOf(u8, sole_use, "return state") != null);
    try std.testing.expect(std.mem.indexOf(u8, sole_use, "snapshot") == null);
}

test "adjacent open call and fixed adjustment emit as one call" {
    const fixtures = lifter.fixtures;
    const source = try emitAlloc(std.testing.allocator, &fixtures.open_pack_adjust_module.program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "return (produce())") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "produce()"));

    var non_tail_blocks = fixtures.open_pack_adjust_module.blocks;
    non_tail_blocks[fixtures.open_pack_adjust_module.b_entry.index()].terminator = .{ .return_values = &.{ fixtures.open_pack_adjust_module.v_first, fixtures.open_pack_adjust_module.v_callee } };
    var non_tail_program = fixtures.open_pack_adjust_module.program;
    non_tail_program.blocks = &non_tail_blocks;
    const non_tail = try emitAlloc(std.testing.allocator, &non_tail_program);
    defer std.testing.allocator.free(non_tail);
    const return_offset = std.mem.lastIndexOf(u8, non_tail, "return ") orelse return error.TestUnexpectedResult;
    const return_line = non_tail[return_offset..(std.mem.indexOfPos(u8, non_tail, return_offset, "\n") orelse non_tail.len)];
    try std.testing.expect(std.mem.indexOf(u8, return_line, "return (") == null);
    try std.testing.expect(std.mem.indexOf(u8, return_line, "(), ") != null);
}

test "nested fixed pack results declare together in their physical block" {
    const fixture = lifter.fixtures.open_pack_adjust_module;
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const consumer = ir.BlockId.fromIndex(2);
    const fallback = ir.BlockId.fromIndex(3);
    const condition_instruction = ir.InstructionId.fromIndex(3);
    const second = ir.ValueId.fromIndex(2);
    const condition = ir.ValueId.fromIndex(3);

    var values = [_]ir.Value{
        fixture.values[fixture.v_callee.index()],
        fixture.values[fixture.v_first.index()],
        .{ .id = second, .function = fixture.f_entry, .name_hint = "second", .origin = .{ .instruction_result = .{ .instruction = fixture.i_adjust, .index = 1 } } },
        .{ .id = condition, .function = fixture.f_entry, .type = .boolean, .name_hint = "condition", .origin = .{ .instruction_result = .{ .instruction = condition_instruction, .index = 0 } } },
    };
    values[fixture.v_callee.index()].name_hint = "produce";
    values[fixture.v_first.index()].name_hint = "first";

    var instructions = [_]ir.Instruction{
        fixture.instructions[fixture.i_get.index()],
        fixture.instructions[fixture.i_call.index()],
        fixture.instructions[fixture.i_adjust.index()],
        .{ .id = condition_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{condition}, .effects = .pure, .evidence = &.{fixture.proof} },
    };
    instructions[fixture.i_get.index()].block = producer;
    instructions[fixture.i_call.index()].block = producer;
    instructions[fixture.i_adjust.index()].block = producer;
    instructions[fixture.i_adjust.index()].results = &.{ fixture.v_first, second };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = fixture.f_entry, .instructions = &.{condition_instruction}, .terminator = .{ .branch = .{ .condition = condition, .then_edge = .{ .target = producer }, .else_edge = .{ .target = fallback } } }, .evidence = &.{fixture.proof} },
        .{ .id = producer, .function = fixture.f_entry, .instructions = &.{ fixture.i_get, fixture.i_call, fixture.i_adjust }, .terminator = .{ .jump = .{ .target = consumer } }, .evidence = &.{fixture.proof} },
        .{ .id = consumer, .function = fixture.f_entry, .terminator = .{ .return_values = &.{ fixture.v_first, second } }, .evidence = &.{fixture.proof} },
        .{ .id = fallback, .function = fixture.f_entry, .terminator = .{ .return_values = &.{} }, .evidence = &.{fixture.proof} },
    };
    const functions = [_]ir.Function{.{
        .id = fixture.f_entry,
        .blocks = &.{ entry, producer, consumer, fallback },
        .entry_block = entry,
        .evidence = &.{fixture.proof},
    }};
    const program: ir.Program = .{
        .program_id = "generic-nested-fixed-pack-results",
        .entry_function = fixture.f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &fixture.value_packs,
        .evidence = &fixture.evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "local first, second = produce()") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local first, second\n") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "return first, second") != null);
}

test "adjacent effectful condition fuses directly into its branch" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const then_block = ir.BlockId.fromIndex(1);
    const else_block = ir.BlockId.fromIndex(2);
    const get_id = ir.InstructionId.fromIndex(0);
    const call_id = ir.InstructionId.fromIndex(1);
    const then_id = ir.InstructionId.fromIndex(2);
    const else_id = ir.InstructionId.fromIndex(3);
    const callee = ir.ValueId.fromIndex(0);
    const condition = ir.ValueId.fromIndex(1);
    const then_value = ir.ValueId.fromIndex(2);
    const else_value = ir.ValueId.fromIndex(3);

    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .instruction_result = .{ .instruction = get_id, .index = 0 } } },
        .{ .id = condition, .function = function_id, .type = .boolean, .name_hint = "condition", .origin = .{ .instruction_result = .{ .instruction = call_id, .index = 0 } } },
        .{ .id = then_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = then_id, .index = 0 } } },
        .{ .id = else_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = else_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = get_id, .block = entry, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "condition" } }, .results = &.{callee}, .effects = .semantic_environment_read, .evidence = &.{proof} },
        .{ .id = call_id, .block = entry, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{condition}, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = then_id, .block = then_block, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{then_value}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = else_id, .block = else_block, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{else_value}, .effects = .pure, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{ get_id, call_id }, .terminator = .{ .branch = .{ .condition = condition, .then_edge = .{ .target = then_block }, .else_edge = .{ .target = else_block } } }, .evidence = &.{proof} },
        .{ .id = then_block, .function = function_id, .instructions = &.{then_id}, .terminator = .{ .return_values = &.{then_value} }, .evidence = &.{proof} },
        .{ .id = else_block, .function = function_id, .instructions = &.{else_id}, .terminator = .{ .return_values = &.{else_value} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &.{ entry, then_block, else_block }, .entry_block = entry, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:effectful-branch-fusion" }};
    const program: ir.Program = .{
        .program_id = "generic-effectful-branch-fusion",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "if condition() then") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "if (condition()) then") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local condition_2") == null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "condition()"));

    var converged_blocks = blocks;
    var converged_branch = converged_blocks[entry.index()].terminator.branch;
    converged_branch.else_edge = converged_branch.then_edge;
    converged_blocks[entry.index()].terminator = .{ .branch = converged_branch };
    var converged_program = program;
    converged_program.blocks = &converged_blocks;
    const converged = try emitAlloc(std.testing.allocator, &converged_program);
    defer std.testing.allocator.free(converged);
    try std.testing.expect(std.mem.indexOf(u8, converged, "if ") == null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, converged, "condition()"));
    try std.testing.expect(std.mem.indexOf(u8, converged, "return 1") != null);
}

test "fixed call result fusion preserves one-result adjustment and refuses multiple uses" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const get_id = ir.InstructionId.fromIndex(0);
    const call_id = ir.InstructionId.fromIndex(1);
    const callee = ir.ValueId.fromIndex(0);
    const result = ir.ValueId.fromIndex(1);

    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .instruction_result = .{ .instruction = get_id, .index = 0 } } },
        .{ .id = result, .function = function_id, .name_hint = "result", .origin = .{ .instruction_result = .{ .instruction = call_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = get_id, .block = block_id, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "produce" } }, .results = &.{callee}, .effects = .semantic_environment_read, .evidence = &.{proof} },
        .{ .id = call_id, .block = block_id, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{result}, .effects = .dynamic_call, .evidence = &.{proof} },
    };
    var blocks = [_]ir.Block{.{ .id = block_id, .function = function_id, .instructions = &.{ get_id, call_id }, .terminator = .{ .return_values = &.{result} }, .evidence = &.{proof} }};
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &.{block_id}, .entry_block = block_id, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:fixed-call-return-fusion" }};
    var program: ir.Program = .{
        .program_id = "generic-fixed-call-return-fusion",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const fused = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(fused);
    try std.testing.expect(std.mem.indexOf(u8, fused, "return (produce())") != null);
    try std.testing.expect(std.mem.indexOf(u8, fused, "result") == null);

    blocks[0].terminator = .{ .return_values = &.{ result, result } };
    program.blocks = &blocks;
    const materialized = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(materialized);
    try std.testing.expect(std.mem.indexOf(u8, materialized, "local result = produce()") != null);
    try std.testing.expect(std.mem.indexOf(u8, materialized, "return result, result") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, materialized, "produce()"));
}

test "sole adjacent effectful result initializes its lexical place directly" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const get_id = ir.InstructionId.fromIndex(0);
    const call_id = ir.InstructionId.fromIndex(1);
    const write_id = ir.InstructionId.fromIndex(2);
    const read_id = ir.InstructionId.fromIndex(3);
    const callee = ir.ValueId.fromIndex(0);
    const call_result = ir.ValueId.fromIndex(1);
    const loaded = ir.ValueId.fromIndex(2);
    const place_id = ir.PlaceId.fromIndex(0);

    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .name_hint = "produce", .origin = .{ .instruction_result = .{ .instruction = get_id, .index = 0 } } },
        .{ .id = call_result, .function = function_id, .name_hint = "call_result", .origin = .{ .instruction_result = .{ .instruction = call_id, .index = 0 } } },
        .{ .id = loaded, .function = function_id, .name_hint = "loaded", .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } } },
    };
    const places = [_]ir.Place{.{
        .id = place_id,
        .function = function_id,
        .name_hint = "result",
        .origin = .{ .instruction = write_id },
        .evidence = &.{proof},
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = get_id, .block = block_id, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "produce" } }, .results = &.{callee}, .effects = .semantic_environment_read, .evidence = &.{proof} },
        .{ .id = call_id, .block = block_id, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{call_result}, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = write_id, .block = block_id, .operation = .{ .place_write = .{ .place = place_id, .value = call_result } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
        .{ .id = read_id, .block = block_id, .operation = .{ .place_read = place_id }, .results = &.{loaded}, .effects = .place_read, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ get_id, call_id, write_id, read_id },
        .terminator = .{ .return_values = &.{loaded} },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{block_id},
        .entry_block = block_id,
        .local_places = &.{place_id},
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:adjacent-effectful-place-write" }};
    const program: ir.Program = .{
        .program_id = "generic-adjacent-effectful-place-write",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "local result = produce()") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "call_result") == null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "produce()"));

    var multi_use_blocks = blocks;
    multi_use_blocks[0].terminator = .{ .return_values = &.{ call_result, loaded } };
    var multi_use_program = program;
    multi_use_program.blocks = &multi_use_blocks;
    const multi_use_source = try emitAlloc(std.testing.allocator, &multi_use_program);
    defer std.testing.allocator.free(multi_use_source);
    try std.testing.expect(std.mem.indexOf(u8, multi_use_source, "local call_result = produce()") != null);
    try std.testing.expect(std.mem.indexOf(u8, multi_use_source, "local result = call_result") != null);

    var transitive_values = values;
    transitive_values[loaded.index()].type = .boolean;
    var transitive_instructions = instructions;
    transitive_instructions[read_id.index()].operation = .{ .unary = .{
        .operator = .logical_not,
        .operand = call_result,
    } };
    transitive_instructions[read_id.index()].effects = .pure;
    var transitive_program = program;
    transitive_program.values = &transitive_values;
    transitive_program.instructions = &transitive_instructions;
    const transitive_source = try emitAlloc(std.testing.allocator, &transitive_program);
    defer std.testing.allocator.free(transitive_source);
    try std.testing.expect(std.mem.indexOf(u8, transitive_source, "local call_result = produce()") != null);
    try std.testing.expect(std.mem.indexOf(u8, transitive_source, "return not call_result") != null);
}

test "place initialization preserves transitive invocation pack fusion" {
    const fixture = lifter.fixtures.open_pack_adjust_module;
    const write_id = ir.InstructionId.fromIndex(3);
    const place_id = ir.PlaceId.fromIndex(0);
    var values = fixture.values;
    values[fixture.v_first.index()].name_hint = "nested_result";
    var instructions = [_]ir.Instruction{
        fixture.instructions[0],
        fixture.instructions[1],
        fixture.instructions[2],
        .{ .id = write_id, .block = fixture.b_entry, .operation = .{ .place_write = .{ .place = place_id, .value = fixture.v_first } }, .results = &.{}, .effects = .place_write, .evidence = &.{fixture.proof} },
    };
    instructions[fixture.i_adjust.index()].operation = .{ .call = .{
        .callee = fixture.v_callee,
        .arguments = &.{},
        .argument_pack = fixture.p_results,
        .result_arity = .{ .fixed = 1 },
    } };
    instructions[fixture.i_adjust.index()].effects = .dynamic_call;
    const places = [_]ir.Place{.{
        .id = place_id,
        .function = fixture.f_entry,
        .name_hint = "nested",
        .origin = .{ .instruction = write_id },
        .evidence = &.{fixture.proof},
    }};
    const blocks = [_]ir.Block{.{
        .id = fixture.b_entry,
        .function = fixture.f_entry,
        .instructions = &.{ fixture.i_get, fixture.i_call, fixture.i_adjust, write_id },
        .terminator = .{ .return_values = &.{} },
        .evidence = &.{fixture.proof},
    }};
    const functions = [_]ir.Function{.{
        .id = fixture.f_entry,
        .blocks = &.{fixture.b_entry},
        .entry_block = fixture.b_entry,
        .local_places = &.{place_id},
        .evidence = &.{fixture.proof},
    }};
    const program: ir.Program = .{
        .program_id = "generic-transitive-pack-place-write",
        .entry_function = fixture.f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &fixture.value_packs,
        .places = &places,
        .evidence = &fixture.evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "local nested = value_0(value_0())") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "nested_result") == null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "value_0()"));

    instructions[fixture.i_adjust.index()] = fixture.instructions[fixture.i_adjust.index()];
    const adjusted_source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(adjusted_source);
    try std.testing.expect(std.mem.indexOf(u8, adjusted_source, "local nested = produce()") != null);
    try std.testing.expect(std.mem.indexOf(u8, adjusted_source, "nested_result") == null);

    values[fixture.v_first.index()].type = .{ .kind = .table };
    instructions[fixture.i_adjust.index()].operation = .{ .make_table_literal = .{ .fields = &.{}, .tail_pack = fixture.p_results } };
    instructions[fixture.i_adjust.index()].effects = .table_constructor;
    const table_source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(table_source);
    try std.testing.expect(std.mem.indexOf(u8, table_source, "local nested = { produce() }") != null);
    try std.testing.expect(std.mem.indexOf(u8, table_source, "nested_result") == null);
}

test "final open call and pack return emit as one return call" {
    const fixtures = lifter.fixtures;
    const instruction_ids = [_]ir.InstructionId{
        fixtures.open_pack_adjust_module.i_get,
        fixtures.open_pack_adjust_module.i_call,
    };
    var blocks = fixtures.open_pack_adjust_module.blocks;
    blocks[0].instructions = &instruction_ids;
    blocks[0].terminator = .{ .return_pack = fixtures.open_pack_adjust_module.p_results };
    var program = fixtures.open_pack_adjust_module.program;
    program.instructions = fixtures.open_pack_adjust_module.instructions[0..2];
    program.values = fixtures.open_pack_adjust_module.values[0..1];
    program.blocks = &blocks;

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "return produce()") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "produce()"));
}

test "open pack return projects through a pure direct successor" {
    const fixture = lifter.fixtures.open_pack_adjust_module;
    const consumer_block = ir.BlockId.fromIndex(fixture.blocks.len);
    const producer_gap_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const producer_gap_value = ir.ValueId.fromIndex(fixture.values.len);
    var values = fixture.values ++ [_]ir.Value{.{
        .id = producer_gap_value,
        .function = fixture.f_entry,
        .type = .integer,
        .origin = .{ .instruction_result = .{ .instruction = producer_gap_id, .index = 0 } },
    }};
    values[fixture.v_first.index()].type = .integer;
    var instructions = fixture.instructions ++ [_]ir.Instruction{.{
        .id = producer_gap_id,
        .block = fixture.b_entry,
        .operation = .{ .constant = .{ .integer = "1" } },
        .results = &.{producer_gap_value},
        .effects = .pure,
        .evidence = &.{fixture.proof},
    }};
    instructions[fixture.i_adjust.index()].block = consumer_block;
    instructions[fixture.i_adjust.index()].operation = .{ .constant = .{ .integer = "7" } };
    instructions[fixture.i_adjust.index()].effects = .pure;
    const producer_ids = [_]ir.InstructionId{ fixture.i_get, fixture.i_call, producer_gap_id };
    const consumer_ids = [_]ir.InstructionId{fixture.i_adjust};
    var blocks = fixture.blocks ++ [_]ir.Block{.{
        .id = consumer_block,
        .function = fixture.f_entry,
        .instructions = &consumer_ids,
        .terminator = .{ .return_expanded = .{
            .values = &.{ producer_gap_value, fixture.v_first },
            .pack = fixture.p_results,
        } },
        .evidence = &.{fixture.proof},
    }};
    blocks[fixture.b_entry.index()].instructions = &producer_ids;
    blocks[fixture.b_entry.index()].terminator = .{ .jump = .{ .target = consumer_block } };
    const function_blocks = [_]ir.BlockId{ fixture.b_entry, consumer_block };
    var functions = fixture.functions;
    functions[fixture.f_entry.index()].blocks = &function_blocks;
    var program = fixture.program;
    program.functions = &functions;
    program.values = &values;
    program.instructions = &instructions;
    program.blocks = &blocks;

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "return 1, 7, produce()") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "produce()"));
    try std.testing.expect(std.mem.indexOf(u8, source, "table.pack") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_pack") == null);

    instructions[fixture.i_adjust.index()].operation = .{ .environment_get = .{
        .target = .{ .ambient = {} },
        .name = "impure_gap",
    } };
    instructions[fixture.i_adjust.index()].effects = .semantic_environment_read;
    program.instructions = &instructions;
    var core_report = try lifter.validate.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try lifter.validate.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());
}

test "all lifted functions are predeclared before forward references" {
    const proof = ir.EvidenceId.fromIndex(0);
    const f_entry = ir.FunctionId.fromIndex(0);
    const f_first = ir.FunctionId.fromIndex(1);
    const f_second = ir.FunctionId.fromIndex(2);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_first = ir.BlockId.fromIndex(1);
    const b_second = ir.BlockId.fromIndex(2);
    const i_export = ir.InstructionId.fromIndex(0);
    const i_forward = ir.InstructionId.fromIndex(1);
    const i_constant = ir.InstructionId.fromIndex(2);
    const v_export = ir.ValueId.fromIndex(0);
    const v_forward = ir.ValueId.fromIndex(1);
    const v_constant = ir.ValueId.fromIndex(2);

    const values = [_]ir.Value{
        .{ .id = v_export, .function = f_entry, .type = .function, .origin = .{ .instruction_result = .{ .instruction = i_export, .index = 0 } } },
        .{ .id = v_forward, .function = f_first, .type = .function, .origin = .{ .instruction_result = .{ .instruction = i_forward, .index = 0 } } },
        .{ .id = v_constant, .function = f_second, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = i_constant, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = i_export, .block = b_entry, .operation = .{ .function_ref = f_first }, .results = &.{v_export}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_forward, .block = b_first, .operation = .{ .function_ref = f_second }, .results = &.{v_forward}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_constant, .block = b_second, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_constant}, .effects = .pure, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f_entry, .instructions = &.{i_export}, .terminator = .{ .return_values = &.{v_export} }, .evidence = &.{proof} },
        .{ .id = b_first, .function = f_first, .instructions = &.{i_forward}, .terminator = .{ .return_values = &.{v_forward} }, .evidence = &.{proof} },
        .{ .id = b_second, .function = f_second, .instructions = &.{i_constant}, .terminator = .{ .return_values = &.{v_constant} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{
        .{ .id = f_entry, .blocks = &.{b_entry}, .entry_block = b_entry, .evidence = &.{proof} },
        .{ .id = f_first, .name_hint = "first", .blocks = &.{b_first}, .entry_block = b_first, .evidence = &.{proof} },
        .{ .id = f_second, .name_hint = "second", .blocks = &.{b_second}, .entry_block = b_second, .evidence = &.{proof} },
    };
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:forward-reference" }};
    const program: ir.Program = .{
        .program_id = "generic-forward-reference",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    const second_declaration = std.mem.indexOf(u8, source, "local fn_second") orelse return error.TestUnexpectedResult;
    const first_definition = std.mem.indexOf(u8, source, "fn_first = function") orelse return error.TestUnexpectedResult;
    try std.testing.expect(second_declaration < first_definition);
    try std.testing.expect(std.mem.indexOf(u8, source, "return fn_second") != null);
}

test "exact primitive u32 bit operations emit through bit32" {
    const fixtures = lifter.fixtures;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32, .signed = false };
    var values = fixtures.arithmetic_module.values;
    values[1].type = u32_type;
    values[2].type = u32_type;
    values[3].type = u32_type;
    var instructions = fixtures.arithmetic_module.instructions;
    instructions[1].operation = .{ .binary = .{
        .operator = .bit_xor,
        .left = fixtures.arithmetic_module.v_left,
        .right = fixtures.arithmetic_module.v_right,
        .mode = .primitive,
    } };
    var program = fixtures.arithmetic_module.program;
    program.values = &values;
    program.instructions = &instructions;
    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "bit32.bxor") != null);
}

test "u32 shift emission preserves explicit high-count behavior" {
    const fixture = lifter.fixtures.arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32, .signed = false };
    var values = fixture.values;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_factor.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation = .{ .constant = .{ .integer = "1" } };
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = "2147483648" } };
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .shift_left,
        .left = fixture.v_sum,
        .right = fixture.v_factor,
        .mode = .primitive,
        .shift_behavior = .zero_saturating,
    } };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;

    const zero_saturating = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(zero_saturating);
    try std.testing.expect(std.mem.indexOf(u8, zero_saturating, ">= 32 then 0 else") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, zero_saturating, "2147483648"));
    try std.testing.expect(std.mem.indexOf(u8, zero_saturating, "bit32.lshift") != null);

    instructions[fixture.i_result.index()].operation.binary.shift_behavior = .luau_bit32;
    const luau_bit32 = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(luau_bit32);
    try std.testing.expect(std.mem.indexOf(u8, luau_bit32, ">= 32 then 0 else") == null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, luau_bit32, "2147483648"));
    try std.testing.expect(std.mem.indexOf(u8, luau_bit32, "bit32.lshift") != null);
}

test "zero-saturating shift materializes effectful operands in source order" {
    const fixture = lifter.fixtures.arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32, .signed = false };
    var values = fixture.values;
    values[fixture.v_left.index()].type = .function;
    values[fixture.v_right.index()].type = .function;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_factor.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation = .{ .call = .{
        .callee = fixture.v_left,
        .arguments = &.{},
        .result_arity = .{ .fixed = 1 },
    } };
    instructions[fixture.i_sum.index()].effects = .dynamic_call;
    instructions[fixture.i_factor.index()].operation = .{ .call = .{
        .callee = fixture.v_right,
        .arguments = &.{},
        .result_arity = .{ .fixed = 1 },
    } };
    instructions[fixture.i_factor.index()].effects = .dynamic_call;
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .shift_right,
        .left = fixture.v_sum,
        .right = fixture.v_factor,
        .mode = .primitive,
        .shift_behavior = .zero_saturating,
    } };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    const left_call = std.mem.indexOf(u8, source, "left()") orelse return error.TestExpectedEqual;
    const right_call = std.mem.indexOf(u8, source, "right()") orelse return error.TestExpectedEqual;
    const shift_guard = std.mem.indexOf(u8, source, ">= 32 then 0 else") orelse return error.TestExpectedEqual;
    try std.testing.expect(left_call < right_call and right_call < shift_guard);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "left()"));
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "right()"));
}

test "emission removes transitive dead exact-pure instructions" {
    const proof = ir.EvidenceId.fromIndex(0);
    const f = ir.FunctionId.fromIndex(0);
    const b = ir.BlockId.fromIndex(0);
    const i_constant = ir.InstructionId.fromIndex(0);
    const i_copy = ir.InstructionId.fromIndex(1);
    const i_observable = ir.InstructionId.fromIndex(2);
    const v_constant = ir.ValueId.fromIndex(0);
    const v_copy = ir.ValueId.fromIndex(1);
    const v_observable = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = v_constant, .function = f, .type = .integer, .name_hint = "dead_constant", .origin = .{ .instruction_result = .{ .instruction = i_constant, .index = 0 } } },
        .{ .id = v_copy, .function = f, .type = .integer, .name_hint = "dead_copy", .origin = .{ .instruction_result = .{ .instruction = i_copy, .index = 0 } } },
        .{ .id = v_observable, .function = f, .name_hint = "observable_read", .origin = .{ .instruction_result = .{ .instruction = i_observable, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = i_constant, .block = b, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_constant}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_copy, .block = b, .operation = .{ .copy = v_constant }, .results = &.{v_copy}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_observable, .block = b, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "observable" } }, .results = &.{v_observable}, .effects = .semantic_environment_read, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{.{ .id = b, .function = f, .instructions = &.{ i_constant, i_copy, i_observable }, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} }};
    const functions = [_]ir.Function{.{ .id = f, .blocks = &.{b}, .entry_block = b, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:emission-dead-code" }};
    const program: ir.Program = .{
        .program_id = "generic-emission-dead-code",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "dead_constant") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "dead_copy") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local observable_read = observable") != null);
}

test "emission resolves live exact-pure copy aliases" {
    const fixture = lifter.fixtures.arithmetic_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .copy = fixture.v_sum };
    var program = fixture.program;
    program.instructions = &instructions;

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "factor") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "result") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "return left + right") != null);
}

test "inlined literals are parenthesized before postfix indexing" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const nil_instruction = ir.InstructionId.fromIndex(0);
    const key_instruction = ir.InstructionId.fromIndex(1);
    const get_instruction = ir.InstructionId.fromIndex(2);
    const nil_value = ir.ValueId.fromIndex(0);
    const key_value = ir.ValueId.fromIndex(1);
    const result_value = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = nil_value, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = nil_instruction, .index = 0 } } },
        .{ .id = key_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = key_instruction, .index = 0 } } },
        .{ .id = result_value, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = get_instruction, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = nil_instruction, .block = block_id, .operation = .{ .constant = .{ .nil_value = {} } }, .results = &.{nil_value}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = key_instruction, .block = block_id, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{key_value}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = get_instruction, .block = block_id, .operation = .{ .table_get = .{ .table = nil_value, .key = key_value, .mode = .semantic } }, .results = &.{result_value}, .effects = .semantic_table_read, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ nil_instruction, key_instruction, get_instruction },
        .terminator = .{ .return_values = &.{result_value} },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &.{block_id}, .entry_block = block_id, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:postfix-literal-index" }};
    const program: ir.Program = .{
        .program_id = "generic-postfix-literal-index",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "(nil)[1]") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "nil[1]") == null);
}

test "parenthesized statement calls receive an explicit separator" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const nil_instruction = ir.InstructionId.fromIndex(0);
    const call_instruction = ir.InstructionId.fromIndex(1);
    const nil_value = ir.ValueId.fromIndex(0);
    var values = [_]ir.Value{.{
        .id = nil_value,
        .function = function_id,
        .origin = .{ .instruction_result = .{ .instruction = nil_instruction, .index = 0 } },
    }};
    var instructions = [_]ir.Instruction{
        .{
            .id = nil_instruction,
            .block = block_id,
            .operation = .{ .constant = .{ .nil_value = {} } },
            .results = &.{nil_value},
            .effects = .pure,
            .evidence = &.{proof},
        },
        .{
            .id = call_instruction,
            .block = block_id,
            .operation = .{ .call = .{ .callee = nil_value, .arguments = &.{}, .result_arity = .{ .fixed = 0 } } },
            .results = &.{},
            .effects = .dynamic_call,
            .evidence = &.{proof},
        },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ nil_instruction, call_instruction },
        .terminator = .{ .return_values = &.{} },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &.{block_id}, .entry_block = block_id, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:parenthesized-statement" }};
    var program: ir.Program = .{
        .program_id = "generic-parenthesized-statement",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "do\n  (nil)()\nend") != null);

    values[0].type = .function;
    instructions[0].operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "observable" } };
    instructions[0].effects = .semantic_environment_read;
    program.values = &values;
    program.instructions = &instructions;
    const identifier_source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(identifier_source);
    try std.testing.expect(std.mem.indexOf(u8, identifier_source, "observable()\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, identifier_source, "do\n") == null);
}

test "instruction-scoped place emits its local declaration at allocation" {
    const fixture = lifter.fixtures.shared_place_closure_module;
    var places = fixture.places;
    places[fixture.p_state.index()].origin = .{ .instruction = fixture.i_initialize };
    var program = fixture.program;
    program.places = &places;

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "local state = start") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local state\nstate =") == null);
}

test "dominating nested write coalesces while path-dependent writes stay predeclared" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const then_block = ir.BlockId.fromIndex(1);
    const else_block = ir.BlockId.fromIndex(2);
    const join = ir.BlockId.fromIndex(3);
    const make_condition = ir.InstructionId.fromIndex(0);
    const make_initial = ir.InstructionId.fromIndex(1);
    const write_then = ir.InstructionId.fromIndex(2);
    const read_then = ir.InstructionId.fromIndex(3);
    const write_else = ir.InstructionId.fromIndex(4);
    const read_join = ir.InstructionId.fromIndex(5);
    const condition = ir.ValueId.fromIndex(0);
    const initial = ir.ValueId.fromIndex(1);
    const then_snapshot = ir.ValueId.fromIndex(2);
    const joined_snapshot = ir.ValueId.fromIndex(3);
    const state = ir.PlaceId.fromIndex(0);

    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .name_hint = "condition", .origin = .{ .instruction_result = .{ .instruction = make_condition, .index = 0 } } },
        .{ .id = initial, .function = function_id, .type = .integer, .name_hint = "initial", .origin = .{ .instruction_result = .{ .instruction = make_initial, .index = 0 } } },
        .{ .id = then_snapshot, .function = function_id, .type = .integer, .name_hint = "then_snapshot", .origin = .{ .instruction_result = .{ .instruction = read_then, .index = 0 } } },
        .{ .id = joined_snapshot, .function = function_id, .type = .integer, .name_hint = "joined_snapshot", .origin = .{ .instruction_result = .{ .instruction = read_join, .index = 0 } } },
    };
    const places = [_]ir.Place{.{
        .id = state,
        .function = function_id,
        .type = .integer,
        .name_hint = "state",
        .origin = .{ .local = 0 },
        .evidence = &.{proof},
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = make_condition, .block = entry, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{condition}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = make_initial, .block = entry, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{initial}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = write_then, .block = then_block, .operation = .{ .place_write = .{ .place = state, .value = initial } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
        .{ .id = read_then, .block = then_block, .operation = .{ .place_read = state }, .results = &.{then_snapshot}, .effects = .place_read, .evidence = &.{proof} },
        .{ .id = write_else, .block = else_block, .operation = .{ .place_write = .{ .place = state, .value = initial } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
        .{ .id = read_join, .block = join, .operation = .{ .place_read = state }, .results = &.{joined_snapshot}, .effects = .place_read, .evidence = &.{proof} },
    };
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{ make_condition, make_initial }, .terminator = .{ .branch = .{ .condition = condition, .then_edge = .{ .target = then_block }, .else_edge = .{ .target = else_block } } }, .evidence = &.{proof} },
        .{ .id = then_block, .function = function_id, .instructions = &.{ write_then, read_then }, .terminator = .{ .return_values = &.{then_snapshot} }, .evidence = &.{proof} },
        .{ .id = else_block, .function = function_id, .terminator = .{ .return_values = &.{initial} }, .evidence = &.{proof} },
        .{ .id = join, .function = function_id, .instructions = &.{read_join}, .terminator = .{ .return_values = &.{joined_snapshot} }, .evidence = &.{proof} },
    };
    var functions = [_]ir.Function{.{
        .id = function_id,
        .local_places = &.{state},
        .blocks = &.{ entry, then_block, else_block },
        .entry_block = entry,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:dominating-place-initializer" }};
    var program: ir.Program = .{
        .program_id = "generic-dominating-place-initializer",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = blocks[0..3],
        .instructions = instructions[0..4],
        .values = values[0..3],
        .places = &places,
        .evidence = &evidence,
    };

    const dominating = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(dominating);
    try std.testing.expect(std.mem.indexOf(u8, dominating, "local state = initial") != null);
    try std.testing.expect(std.mem.indexOf(u8, dominating, "local state\n") == null);

    blocks[then_block.index()].terminator = .{ .jump = .{ .target = join } };
    blocks[else_block.index()].instructions = &.{write_else};
    blocks[else_block.index()].terminator = .{ .jump = .{ .target = join } };
    functions[0].blocks = &.{ entry, then_block, else_block, join };
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;

    const path_dependent = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(path_dependent);
    try std.testing.expect(std.mem.indexOf(u8, path_dependent, "local state\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, path_dependent, "local state = initial") == null);
}

test "function-local place initialization stays outside an entry backedge" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const constant_id = ir.InstructionId.fromIndex(0);
    const write_id = ir.InstructionId.fromIndex(1);
    const value_id = ir.ValueId.fromIndex(0);
    const place_id = ir.PlaceId.fromIndex(0);
    const values = [_]ir.Value{.{ .id = value_id, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = constant_id, .index = 0 } } }};
    const places = [_]ir.Place{.{ .id = place_id, .function = function_id, .type = .integer, .name_hint = "state", .origin = .{ .local = 0 }, .evidence = &.{proof} }};
    const instructions = [_]ir.Instruction{
        .{ .id = constant_id, .block = block_id, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{value_id}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = write_id, .block = block_id, .operation = .{ .place_write = .{ .place = place_id, .value = value_id } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{.{ .id = block_id, .function = function_id, .instructions = &.{ constant_id, write_id }, .terminator = .{ .jump = .{ .target = block_id } }, .evidence = &.{proof} }};
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &.{block_id}, .entry_block = block_id, .local_places = &.{place_id}, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:entry-backedge-place" }};
    const program: ir.Program = .{
        .program_id = "generic-entry-backedge-place",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    const declaration = std.mem.indexOf(u8, source, "local state\n") orelse return error.TestUnexpectedResult;
    const loop = std.mem.indexOf(u8, source, "while true do\n") orelse return error.TestUnexpectedResult;
    const assignment = std.mem.lastIndexOf(u8, source, "state = 1") orelse return error.TestUnexpectedResult;
    try std.testing.expect(declaration < loop and loop < assignment);
    try std.testing.expect(std.mem.indexOf(u8, source, "while true do\n  local state") == null);
}

test "unreachable entry predecessor does not force loop-style declarations" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const dead_id = ir.BlockId.fromIndex(1);
    const constant_id = ir.InstructionId.fromIndex(0);
    const write_id = ir.InstructionId.fromIndex(1);
    const value_id = ir.ValueId.fromIndex(0);
    const place_id = ir.PlaceId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = value_id,
        .function = function_id,
        .type = .integer,
        .origin = .{ .instruction_result = .{ .instruction = constant_id, .index = 0 } },
    }};
    const places = [_]ir.Place{.{
        .id = place_id,
        .function = function_id,
        .type = .integer,
        .name_hint = "state",
        .origin = .{ .local = 0 },
        .evidence = &.{proof},
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = constant_id, .block = entry_id, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{value_id}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = write_id, .block = entry_id, .operation = .{ .place_write = .{ .place = place_id, .value = value_id } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .instructions = &.{ constant_id, write_id }, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
        .{ .id = dead_id, .function = function_id, .terminator = .{ .jump = .{ .target = entry_id } }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .entry_block = entry_id,
        .blocks = &.{ entry_id, dead_id },
        .local_places = &.{place_id},
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:unreachable-entry-predecessor",
    }};
    const program: ir.Program = .{
        .program_id = "unreachable-entry-predecessor",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "local state = 1") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local state\n") == null);
}

test "dead symbol collisions do not change emitted Luau" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const dead_id = ir.BlockId.fromIndex(1);
    const dead_global_id = ir.InstructionId.fromIndex(0);
    const dead_shared_id = ir.InstructionId.fromIndex(1);
    const dead_write_id = ir.InstructionId.fromIndex(2);
    const live_name_id = ir.InstructionId.fromIndex(3);
    const live_shared_id = ir.InstructionId.fromIndex(4);
    const live_write_id = ir.InstructionId.fromIndex(5);
    const dead_global_value = ir.ValueId.fromIndex(0);
    const dead_shared_value = ir.ValueId.fromIndex(1);
    const live_name_value = ir.ValueId.fromIndex(2);
    const live_shared_value = ir.ValueId.fromIndex(3);
    const dead_place = ir.PlaceId.fromIndex(0);
    const live_place = ir.PlaceId.fromIndex(1);
    var neutral_values = [_]ir.Value{
        .{ .id = dead_global_value, .function = function_id, .name_hint = "dead_global", .origin = .{ .instruction_result = .{ .instruction = dead_global_id, .index = 0 } } },
        .{ .id = dead_shared_value, .function = function_id, .type = .integer, .name_hint = "dead_shared", .origin = .{ .instruction_result = .{ .instruction = dead_shared_id, .index = 0 } } },
        .{ .id = live_name_value, .function = function_id, .name_hint = "live_name", .origin = .{ .instruction_result = .{ .instruction = live_name_id, .index = 0 } } },
        .{ .id = live_shared_value, .function = function_id, .type = .integer, .name_hint = "shared", .origin = .{ .instruction_result = .{ .instruction = live_shared_id, .index = 0 } } },
    };
    var neutral_places = [_]ir.Place{
        .{ .id = dead_place, .function = function_id, .type = .integer, .name_hint = "dead_state", .origin = .{ .local = 0 }, .evidence = &.{proof} },
        .{ .id = live_place, .function = function_id, .type = .integer, .name_hint = "state", .origin = .{ .local = 1 }, .evidence = &.{proof} },
    };
    var neutral_instructions = [_]ir.Instruction{
        .{ .id = dead_global_id, .block = dead_id, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "dead_global_api" } }, .results = &.{dead_global_value}, .effects = .semantic_environment_read, .evidence = &.{proof} },
        .{ .id = dead_shared_id, .block = dead_id, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{dead_shared_value}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = dead_write_id, .block = dead_id, .operation = .{ .place_write = .{ .place = dead_place, .value = dead_shared_value } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
        .{ .id = live_name_id, .block = entry_id, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "actual_api" } }, .results = &.{live_name_value}, .effects = .semantic_environment_read, .evidence = &.{proof} },
        .{ .id = live_shared_id, .block = entry_id, .operation = .{ .constant = .{ .integer = "2" } }, .results = &.{live_shared_value}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = live_write_id, .block = entry_id, .operation = .{ .place_write = .{ .place = live_place, .value = live_shared_value } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .instructions = &.{ live_name_id, live_shared_id, live_write_id }, .terminator = .{ .return_values = &.{ live_name_value, live_shared_value } }, .evidence = &.{proof} },
        .{ .id = dead_id, .function = function_id, .instructions = &.{ dead_global_id, dead_shared_id, dead_write_id }, .terminator = .{ .return_values = &.{ dead_global_value, dead_shared_value } }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .entry_block = entry_id,
        .blocks = &.{ entry_id, dead_id },
        .local_places = &.{ dead_place, live_place },
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:dead-symbol-collisions",
    }};
    var neutral_program: ir.Program = .{
        .program_id = "dead-symbol-collisions",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &neutral_instructions,
        .values = &neutral_values,
        .places = &neutral_places,
        .evidence = &evidence,
    };

    const neutral = try emitAlloc(std.testing.allocator, &neutral_program);
    defer std.testing.allocator.free(neutral);

    var colliding_values = neutral_values;
    colliding_values[dead_shared_value.index()].name_hint = "shared";
    var colliding_places = neutral_places;
    colliding_places[dead_place.index()].name_hint = "state";
    var colliding_instructions = neutral_instructions;
    colliding_instructions[dead_global_id.index()].operation.environment_get.name = "live_name";
    var colliding_program = neutral_program;
    colliding_program.instructions = &colliding_instructions;
    colliding_program.values = &colliding_values;
    colliding_program.places = &colliding_places;

    const colliding = try emitAlloc(std.testing.allocator, &colliding_program);
    defer std.testing.allocator.free(colliding);
    try std.testing.expectEqualStrings(neutral, colliding);
    try std.testing.expect(std.mem.indexOf(u8, colliding, "live_name") != null);
    try std.testing.expect(std.mem.indexOf(u8, colliding, "state") != null);
    try std.testing.expect(std.mem.indexOf(u8, colliding, "shared") != null);
}

test "loop-local escape uses a distinct carrier without collapsing closure snapshots" {
    const proof = ir.EvidenceId.fromIndex(0);
    const entry_function = ir.FunctionId.fromIndex(0);
    const worker_function = ir.FunctionId.fromIndex(1);
    const snapshot_function = ir.FunctionId.fromIndex(2);
    const entry_block = ir.BlockId.fromIndex(0);
    const worker_entry = ir.BlockId.fromIndex(1);
    const loop_header = ir.BlockId.fromIndex(2);
    const loop_body = ir.BlockId.fromIndex(3);
    const loop_exit = ir.BlockId.fromIndex(4);
    const snapshot_block = ir.BlockId.fromIndex(5);
    const export_id = ir.InstructionId.fromIndex(0);
    const next_id = ir.InstructionId.fromIndex(1);
    const closure_id = ir.InstructionId.fromIndex(2);
    const record_id = ir.InstructionId.fromIndex(3);
    const exported_worker = ir.ValueId.fromIndex(0);
    const next_callback = ir.ValueId.fromIndex(1);
    const record_callback = ir.ValueId.fromIndex(2);
    const continue_loop = ir.ValueId.fromIndex(3);
    const iteration = ir.ValueId.fromIndex(4);
    const snapshot = ir.ValueId.fromIndex(5);
    const captured_iteration = ir.ValueId.fromIndex(6);
    const capture = ir.CaptureId.fromIndex(0);

    const values = [_]ir.Value{
        .{ .id = exported_worker, .function = entry_function, .type = .function, .name_hint = "worker", .origin = .{ .instruction_result = .{ .instruction = export_id, .index = 0 } } },
        .{ .id = next_callback, .function = worker_function, .type = .function, .name_hint = "next_value", .origin = .{ .parameter = 0 } },
        .{ .id = record_callback, .function = worker_function, .type = .function, .name_hint = "record", .origin = .{ .parameter = 1 } },
        .{ .id = continue_loop, .function = worker_function, .type = .boolean, .name_hint = "continue_loop", .origin = .{ .instruction_result = .{ .instruction = next_id, .index = 0 } } },
        .{ .id = iteration, .function = worker_function, .type = .integer, .name_hint = "iteration", .origin = .{ .instruction_result = .{ .instruction = next_id, .index = 1 } } },
        .{ .id = snapshot, .function = worker_function, .type = .function, .name_hint = "snapshot", .origin = .{ .instruction_result = .{ .instruction = closure_id, .index = 0 } } },
        .{ .id = captured_iteration, .function = snapshot_function, .type = .integer, .name_hint = "captured_iteration", .origin = .{ .capture = capture } },
    };
    const captures = [_]ir.Capture{.{
        .id = capture,
        .function = snapshot_function,
        .kind = .{ .immutable_value = captured_iteration },
        .evidence = &.{proof},
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = export_id, .block = entry_block, .operation = .{ .function_ref = worker_function }, .results = &.{exported_worker}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = next_id, .block = loop_body, .operation = .{ .call = .{ .callee = next_callback, .arguments = &.{}, .result_arity = .{ .fixed = 2 } } }, .results = &.{ continue_loop, iteration }, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = closure_id, .block = loop_body, .operation = .{ .make_closure = .{ .function = snapshot_function, .bindings = &.{.{ .value = iteration }} } }, .results = &.{snapshot}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = record_id, .block = loop_body, .operation = .{ .call = .{ .callee = record_callback, .arguments = &.{snapshot}, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry_block, .function = entry_function, .instructions = &.{export_id}, .terminator = .{ .return_values = &.{exported_worker} }, .evidence = &.{proof} },
        .{ .id = worker_entry, .function = worker_function, .terminator = .{ .jump = .{ .target = loop_header } }, .evidence = &.{proof} },
        .{ .id = loop_header, .function = worker_function, .terminator = .{ .jump = .{ .target = loop_body } }, .evidence = &.{proof} },
        .{ .id = loop_body, .function = worker_function, .instructions = &.{ next_id, closure_id, record_id }, .terminator = .{ .branch = .{
            .condition = continue_loop,
            .then_edge = .{ .target = loop_header },
            .else_edge = .{ .target = loop_exit },
        } }, .evidence = &.{proof} },
        .{ .id = loop_exit, .function = worker_function, .terminator = .{ .return_values = &.{iteration} }, .evidence = &.{proof} },
        .{ .id = snapshot_block, .function = snapshot_function, .terminator = .{ .return_values = &.{captured_iteration} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{
        .{ .id = entry_function, .name_hint = "chunk", .blocks = &.{entry_block}, .entry_block = entry_block, .evidence = &.{proof} },
        .{ .id = worker_function, .name_hint = "worker", .parameters = &.{ next_callback, record_callback }, .blocks = &.{ worker_entry, loop_header, loop_body, loop_exit }, .entry_block = worker_entry, .evidence = &.{proof} },
        .{ .id = snapshot_function, .name_hint = "snapshot", .lexical_parent = worker_function, .captures = &.{capture}, .blocks = &.{snapshot_block}, .entry_block = snapshot_block, .evidence = &.{proof} },
    };
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:loop-local-lexical-transfer",
    }};
    const program: ir.Program = .{
        .program_id = "loop-local-lexical-transfer",
        .entry_function = entry_function,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .captures = &captures,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "local iteration\n") != null);
    try std.testing.expect(std.mem.count(u8, source, "iteration_2") >= 3);
    try std.testing.expect(std.mem.indexOf(u8, source, "iteration = iteration_2") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "return iteration_2\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "return iteration\n") != null);
}

test "table tail pack emits its adjacent invocation as native constructor syntax" {
    const fixture = lifter.fixtures.open_pack_adjust_module;
    var values = fixture.values;
    values[fixture.v_first.index()].type = .{ .kind = .table };
    var instructions = fixture.instructions;
    instructions[fixture.i_adjust.index()].operation = .{ .make_table_literal = .{
        .fields = &.{},
        .tail_pack = fixture.p_results,
    } };
    instructions[fixture.i_adjust.index()].effects = .table_constructor;
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "return { produce() }") != null);

    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].terminator = .{ .return_values = &.{ fixture.v_first, fixture.v_first } };
    program.blocks = &blocks;
    const multi_use = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(multi_use);
    try std.testing.expect(std.mem.indexOf(u8, multi_use, "local value_1 = {\n  produce()\n}") != null);
    try std.testing.expect(std.mem.indexOf(u8, multi_use, "return value_1, value_1") != null);
}

test "ordered table pack writes preserve a direct vararg pack" {
    const source = try emitAlloc(std.testing.allocator, &lifter.fixtures.ordered_table_vararg_module.program);
    defer std.testing.allocator.free(source);

    try std.testing.expect(std.mem.indexOf(u8, source, "local __lifter_rawset = rawset") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local __lifter_select = select") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "(function(__lifter_pack_table_1, __lifter_pack_first_1, ...)") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "for __lifter_pack_offset_1 = 0, __lifter_select(\"#\", ...) - 1 do") != null);
    try std.testing.expect(std.mem.indexOf(
        u8,
        source,
        "__lifter_rawset(__lifter_pack_table_1, __lifter_pack_first_1 + __lifter_pack_offset_1, (__lifter_select(__lifter_pack_offset_1 + 1, ...)))",
    ) != null);
    try std.testing.expect(std.mem.indexOf(u8, source, ", 2, ...)\n") != null);
}

test "bounded emission scopes prevent sequential temporaries from exhausting Luau registers" {
    const allocator = std.testing.allocator;
    const instruction_count = 240;
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);

    const values = try allocator.alloc(ir.Value, instruction_count);
    defer allocator.free(values);
    const instructions = try allocator.alloc(ir.Instruction, instruction_count);
    defer allocator.free(instructions);
    const instruction_ids = try allocator.alloc(ir.InstructionId, instruction_count);
    defer allocator.free(instruction_ids);
    const result_ids = try allocator.alloc([1]ir.ValueId, instruction_count);
    defer allocator.free(result_ids);

    for (0..instruction_count) |index| {
        const instruction_id = ir.InstructionId.fromIndex(index);
        const value_id = ir.ValueId.fromIndex(index);
        instruction_ids[index] = instruction_id;
        result_ids[index] = .{value_id};
        values[index] = .{
            .id = value_id,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } },
        };
        instructions[index] = .{
            .id = instruction_id,
            .block = block_id,
            .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "observable" } },
            .results = &result_ids[index],
            .effects = .semantic_environment_read,
            .evidence = &.{proof},
        };
    }

    const returned = [_]ir.ValueId{ir.ValueId.fromIndex(0)};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = instruction_ids,
        .terminator = .{ .return_values = &returned },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:bounded-emission-scopes" }};
    const program: ir.Program = .{
        .program_id = "generic-bounded-emission-scopes",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = instructions,
        .values = values,
        .evidence = &evidence,
    };

    const source = try lifter.emit_luau.emitAllocForTarget(allocator, &program, .direct_locals_luau);
    defer allocator.free(source);
    try std.testing.expectEqual(instruction_count, std.mem.count(u8, source, "observable"));
    try std.testing.expect(std.mem.count(u8, source, "do\n") >= 7);
    try std.testing.expect(std.mem.indexOf(u8, source, "local value_0\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "value_0 = observable") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "return value_0") != null);
}

test "infinite loop with a unique internal exit emits break and post-loop continuation" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const decision = ir.BlockId.fromIndex(1);
    const latch = ir.BlockId.fromIndex(2);
    const exit_block = ir.BlockId.fromIndex(3);
    const condition_instruction = ir.InstructionId.fromIndex(0);
    const condition_value = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = condition_value,
        .function = function_id,
        .type = .boolean,
        .name_hint = "should_break",
        .origin = .{ .instruction_result = .{ .instruction = condition_instruction, .index = 0 } },
    }};
    const instructions = [_]ir.Instruction{.{
        .id = condition_instruction,
        .block = decision,
        .operation = .{ .constant = .{ .boolean = false } },
        .results = &.{condition_value},
        .effects = .pure,
        .evidence = &.{proof},
    }};
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = decision } }, .evidence = &.{proof} },
        .{ .id = decision, .function = function_id, .instructions = &.{condition_instruction}, .terminator = .{ .branch = .{
            .condition = condition_value,
            .then_edge = .{ .target = exit_block },
            .else_edge = .{ .target = latch },
        } }, .evidence = &.{proof} },
        .{ .id = latch, .function = function_id, .terminator = .{ .jump = .{ .target = header } }, .evidence = &.{proof} },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ header, decision, latch, exit_block },
        .entry_block = header,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:infinite-loop-break" }};
    const program: ir.Program = .{
        .program_id = "generic-infinite-loop-break",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "while true do\n") != null);
    const loop_break = std.mem.indexOf(u8, source, "break\n") orelse return error.TestUnexpectedResult;
    const loop_end = std.mem.lastIndexOf(u8, source, "end\n") orelse return error.TestUnexpectedResult;
    try std.testing.expect(loop_break < loop_end);
    try std.testing.expect(std.mem.indexOf(u8, source, "return\n") == null);
}

test "loop terminal omits only a structurally empty natural continue arm" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const terminal = ir.BlockId.fromIndex(3);
    const exit_block = ir.BlockId.fromIndex(4);
    const loop_instruction = ir.InstructionId.fromIndex(0);
    const terminal_instruction = ir.InstructionId.fromIndex(1);
    const loop_value = ir.ValueId.fromIndex(0);
    const terminal_value = ir.ValueId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = loop_value, .function = function_id, .type = .boolean, .name_hint = "loop", .origin = .{ .instruction_result = .{ .instruction = loop_instruction, .index = 0 } } },
        .{ .id = terminal_value, .function = function_id, .type = .boolean, .name_hint = "terminal", .origin = .{ .instruction_result = .{ .instruction = terminal_instruction, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = loop_instruction, .block = preheader, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{loop_value}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = terminal_instruction, .block = body, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{terminal_value}, .effects = .pure, .evidence = &.{proof} },
    };
    var blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .instructions = &.{loop_instruction}, .terminator = .{ .jump = .{ .target = header } }, .evidence = &.{proof} },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = loop_value,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit_block },
        } }, .evidence = &.{proof} },
        .{ .id = body, .function = function_id, .instructions = &.{terminal_instruction}, .terminator = .{ .branch = .{
            .condition = terminal_value,
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = terminal },
        } }, .evidence = &.{proof} },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ preheader, header, body, terminal, exit_block },
        .entry_block = preheader,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:loop-terminal-natural-continue" }};
    var program: ir.Program = .{
        .program_id = "generic-loop-terminal-natural-continue",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const continue_on_true = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(continue_on_true);
    try std.testing.expect(std.mem.indexOf(u8, continue_on_true, "if not ") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, continue_on_true, "else\n"));
    try std.testing.expect(std.mem.indexOf(u8, continue_on_true, " then\n    else\n") == null);

    blocks[body.index()].terminator = .{ .branch = .{
        .condition = terminal_value,
        .then_edge = .{ .target = terminal },
        .else_edge = .{ .target = header },
    } };
    const continue_on_false = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(continue_on_false);
    try std.testing.expect(std.mem.indexOf(u8, continue_on_false, "if true then\n") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, continue_on_false, "else\n"));
    try std.testing.expect(std.mem.indexOf(u8, continue_on_false, "\n    else\n    end\n") == null);

    const seed_instruction = ir.InstructionId.fromIndex(2);
    const next_instruction = ir.InstructionId.fromIndex(3);
    const seed_value = ir.ValueId.fromIndex(2);
    const next_value = ir.ValueId.fromIndex(3);
    const carried_value = ir.ValueId.fromIndex(4);
    const carried_values = [_]ir.Value{
        values[0],
        values[1],
        .{ .id = seed_value, .function = function_id, .type = .integer, .name_hint = "seed", .origin = .{ .instruction_result = .{ .instruction = seed_instruction, .index = 0 } } },
        .{ .id = next_value, .function = function_id, .type = .integer, .name_hint = "next", .origin = .{ .instruction_result = .{ .instruction = next_instruction, .index = 0 } } },
        .{ .id = carried_value, .function = function_id, .type = .integer, .name_hint = "carried", .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
    };
    const carried_instructions = [_]ir.Instruction{
        instructions[0],
        instructions[1],
        .{ .id = seed_instruction, .block = preheader, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{seed_value}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = next_instruction, .block = body, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{next_value}, .effects = .pure, .evidence = &.{proof} },
    };
    blocks[preheader.index()].instructions = &.{ loop_instruction, seed_instruction };
    blocks[preheader.index()].terminator = .{ .jump = .{ .target = header, .arguments = &.{seed_value} } };
    blocks[header.index()].parameters = &.{carried_value};
    blocks[body.index()].instructions = &.{ terminal_instruction, next_instruction };
    blocks[body.index()].terminator = .{ .branch = .{
        .condition = terminal_value,
        .then_edge = .{ .target = header, .arguments = &.{next_value} },
        .else_edge = .{ .target = terminal },
    } };
    blocks[terminal.index()].terminator = .{ .return_values = &.{carried_value} };
    blocks[exit_block.index()].terminator = .{ .return_values = &.{carried_value} };
    program.instructions = &carried_instructions;
    program.values = &carried_values;

    const parameterized = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(parameterized);
    try std.testing.expectEqual(@as(usize, 2), std.mem.count(u8, parameterized, "else\n"));
}

test "a frame-local register read between an open call and its return fuses into the return" {
    const fixture = lifter.fixtures.open_pack_adjust_module;
    const register_place = ir.PlaceId.fromIndex(0);
    // `i_adjust` is dropped, so the new instructions take ids from its slot on.
    const i_seed = ir.InstructionId.fromIndex(2);
    const i_write = ir.InstructionId.fromIndex(3);
    const i_read = ir.InstructionId.fromIndex(4);
    const v_seed = ir.ValueId.fromIndex(1);
    const v_read = ir.ValueId.fromIndex(2);
    const places = [_]ir.Place{.{
        .id = register_place,
        .function = fixture.f_entry,
        .type = .dynamic,
        .name_hint = "r1",
        .origin = .{ .local = 0 },
        .evidence = &.{fixture.proof},
    }};
    const values = [_]ir.Value{
        fixture.values[fixture.v_callee.index()],
        .{ .id = v_seed, .function = fixture.f_entry, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = i_seed, .index = 0 } } },
        .{ .id = v_read, .function = fixture.f_entry, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = i_read, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        fixture.instructions[fixture.i_get.index()],
        fixture.instructions[fixture.i_call.index()],
        .{
            .id = i_seed,
            .block = fixture.b_entry,
            .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "seed" } },
            .results = &.{v_seed},
            .effects = .semantic_environment_read,
            .evidence = &.{fixture.proof},
        },
        .{
            .id = i_write,
            .block = fixture.b_entry,
            .operation = .{ .place_write = .{ .place = register_place, .value = v_seed } },
            .results = &.{},
            .effects = .place_write,
            .evidence = &.{fixture.proof},
        },
        .{
            .id = i_read,
            .block = fixture.b_entry,
            .operation = .{ .place_read = register_place },
            .results = &.{v_read},
            .effects = .place_read,
            .evidence = &.{fixture.proof},
        },
    };
    // The block order under test: the callee read sits next to the open call.
    const block_instructions = [_]ir.InstructionId{ i_seed, i_write, fixture.i_get, fixture.i_call, i_read };
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].instructions = &block_instructions;
    blocks[fixture.b_entry.index()].terminator = .{ .return_expanded = .{
        .values = &.{v_read},
        .pack = fixture.p_results,
    } };
    var functions = fixture.functions;
    functions[fixture.f_entry.index()].local_places = &.{register_place};
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;
    program.places = &places;

    var core_report = try lifter.validate.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try lifter.validate.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_stored_values_") == null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "produce()"));
}

/// True when `source` holds `return r1, ` directly followed by `produce()` or by
/// `value_<digits>()`: the pattern `return r1, (produce|value_[0-9]+)()` with
/// literal parentheses, a return statement that calls the open producer itself.
fn returnFusesOpenCall(source: []const u8) bool {
    const prefix = "return r1, ";
    var start: usize = 0;
    while (std.mem.indexOfPos(u8, source, start, prefix)) |at| {
        start = at + 1;
        const rest = source[at + prefix.len ..];
        if (std.mem.startsWith(u8, rest, "produce()")) return true;
        if (!std.mem.startsWith(u8, rest, "value_")) continue;
        var end: usize = "value_".len;
        while (end < rest.len and std.ascii.isDigit(rest[end])) end += 1;
        if (end > "value_".len and std.mem.startsWith(u8, rest[end..], "()")) return true;
    }
    return false;
}

test "a frame-local register read between an open call and its return fuses into the return when an ambient read separates the callee read from the call" {
    const fixture = lifter.fixtures.open_pack_adjust_module;
    const register_place = ir.PlaceId.fromIndex(0);
    // `i_adjust` is dropped, so the new instructions take ids from its slot on.
    const i_seed = ir.InstructionId.fromIndex(2);
    const i_write = ir.InstructionId.fromIndex(3);
    const i_read = ir.InstructionId.fromIndex(4);
    const v_seed = ir.ValueId.fromIndex(1);
    const v_read = ir.ValueId.fromIndex(2);
    const places = [_]ir.Place{.{
        .id = register_place,
        .function = fixture.f_entry,
        .type = .dynamic,
        .name_hint = "r1",
        .origin = .{ .local = 0 },
        .evidence = &.{fixture.proof},
    }};
    const values = [_]ir.Value{
        fixture.values[fixture.v_callee.index()],
        .{ .id = v_seed, .function = fixture.f_entry, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = i_seed, .index = 0 } } },
        .{ .id = v_read, .function = fixture.f_entry, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = i_read, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        fixture.instructions[fixture.i_get.index()],
        fixture.instructions[fixture.i_call.index()],
        .{
            .id = i_seed,
            .block = fixture.b_entry,
            .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "seed" } },
            .results = &.{v_seed},
            .effects = .semantic_environment_read,
            .evidence = &.{fixture.proof},
        },
        .{
            .id = i_write,
            .block = fixture.b_entry,
            .operation = .{ .place_write = .{ .place = register_place, .value = v_seed } },
            .results = &.{},
            .effects = .place_write,
            .evidence = &.{fixture.proof},
        },
        .{
            .id = i_read,
            .block = fixture.b_entry,
            .operation = .{ .place_read = register_place },
            .results = &.{v_read},
            .effects = .place_read,
            .evidence = &.{fixture.proof},
        },
    };
    // The listed order: the ambient `seed` read separates the callee read from the open call.
    const block_instructions = [_]ir.InstructionId{ fixture.i_get, i_seed, i_write, fixture.i_call, i_read };
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].instructions = &block_instructions;
    blocks[fixture.b_entry.index()].terminator = .{ .return_expanded = .{
        .values = &.{v_read},
        .pack = fixture.p_results,
    } };
    var functions = fixture.functions;
    functions[fixture.f_entry.index()].local_places = &.{register_place};
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;
    program.places = &places;

    var core_report = try lifter.validate.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try lifter.validate.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_stored_values_") == null);
    try std.testing.expect(returnFusesOpenCall(source));
}

test "acyclic native iteration whose body always returns emits no break after the return" {
    // The loop body returns, so the header has no join of its own. The loop is
    // admitted and written as one native `for` whose body ends in its `return`, followed by the exit code, with no
    // `break` after the return (Luau accepts `return` only as the last statement of a block).
    const proof = ir.EvidenceId.fromIndex(0);
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_header = ir.BlockId.fromIndex(1);
    const b_body = ir.BlockId.fromIndex(2);
    const b_exit = ir.BlockId.fromIndex(3);
    const i_control = ir.InstructionId.fromIndex(0);
    const i_limit = ir.InstructionId.fromIndex(1);
    const i_step = ir.InstructionId.fromIndex(2);
    const i_true = ir.InstructionId.fromIndex(3);
    const i_next = ir.InstructionId.fromIndex(4);
    const v_control = ir.ValueId.fromIndex(0);
    const v_limit = ir.ValueId.fromIndex(1);
    const v_step = ir.ValueId.fromIndex(2);
    const v_true = ir.ValueId.fromIndex(3);
    const v_header_control = ir.ValueId.fromIndex(4);
    const v_header_limit = ir.ValueId.fromIndex(5);
    const v_header_step = ir.ValueId.fromIndex(6);
    const v_header_initial = ir.ValueId.fromIndex(7);
    const v_has = ir.ValueId.fromIndex(8);
    const v_normalized_limit = ir.ValueId.fromIndex(9);
    const v_normalized_step = ir.ValueId.fromIndex(10);
    const v_index = ir.ValueId.fromIndex(11);
    const v_body_index = ir.ValueId.fromIndex(12);
    const values = [_]ir.Value{
        .{ .id = v_control, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_control, .index = 0 } } },
        .{ .id = v_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_limit, .index = 0 } } },
        .{ .id = v_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_step, .index = 0 } } },
        .{ .id = v_true, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
        .{ .id = v_header_control, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 0 } } },
        .{ .id = v_header_limit, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 1 } } },
        .{ .id = v_header_step, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 2 } } },
        .{ .id = v_header_initial, .function = f, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_header, .index = 3 } } },
        .{ .id = v_has, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 0 } } },
        .{ .id = v_normalized_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 1 } } },
        .{ .id = v_normalized_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 2 } } },
        .{ .id = v_index, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 3 } } },
        .{ .id = v_body_index, .function = f, .type = .number, .origin = .{ .block_parameter = .{ .block = b_body, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = i_control, .block = b_entry, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_control}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_limit, .block = b_entry, .operation = .{ .constant = .{ .integer = "3" } }, .results = &.{v_limit}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_step, .block = b_entry, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_step}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_true, .block = b_entry, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure, .evidence = &.{proof} },
        .{
            .id = i_next,
            .block = b_header,
            .operation = .{ .numeric_for_next = .{
                .control = v_header_control,
                .limit = v_header_limit,
                .step = v_header_step,
                .initial = v_header_initial,
            } },
            .results = &.{ v_has, v_normalized_limit, v_normalized_step, v_index },
            .effects = .numeric_for_next,
            .evidence = &.{proof},
        },
    };
    const blocks = [_]ir.Block{
        .{
            .id = b_entry,
            .function = f,
            .instructions = &.{ i_control, i_limit, i_step, i_true },
            .terminator = .{ .jump = .{ .target = b_header, .arguments = &.{ v_control, v_limit, v_step, v_true } } },
            .evidence = &.{proof},
        },
        .{
            .id = b_header,
            .function = f,
            .parameters = &.{ v_header_control, v_header_limit, v_header_step, v_header_initial },
            .instructions = &.{i_next},
            .terminator = .{ .branch = .{
                .condition = v_has,
                .then_edge = .{ .target = b_body, .arguments = &.{v_index} },
                .else_edge = .{ .target = b_exit },
            } },
            .evidence = &.{proof},
        },
        .{ .id = b_body, .function = f, .parameters = &.{v_body_index}, .terminator = .{ .return_values = &.{v_body_index} }, .evidence = &.{proof} },
        .{ .id = b_exit, .function = f, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{
        .id = f,
        .blocks = &.{ b_entry, b_header, b_body, b_exit },
        .entry_block = b_entry,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:always-returning-iteration" }};
    const program: ir.Program = .{
        .program_id = "always-returning-iteration",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    var for_lines: usize = 0;
    var lines = std.mem.splitScalar(u8, source, '\n');
    while (lines.next()) |line| {
        const trimmed = std.mem.trim(u8, line, " \t");
        if (std.mem.startsWith(u8, trimmed, "for ") and std.mem.endsWith(u8, trimmed, " do")) for_lines += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), for_lines);
    try std.testing.expect(std.mem.indexOf(u8, source, "return") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "break") == null);
}

test "acyclic iteration in a loop boundary inside a while loop emits one native for loop" {
    // A numeric loop whose body always returns, inside a `while` body, is planned as a
    // loop boundary of the enclosing loop body. It is admitted and written as one native `for` whose body ends in
    // its `return`, followed by the exit arm: no `if` form and no `break` inside the loop.
    const proof = ir.EvidenceId.fromIndex(0);
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_while = ir.BlockId.fromIndex(1);
    const b_pre = ir.BlockId.fromIndex(2);
    const b_header = ir.BlockId.fromIndex(3);
    const b_body = ir.BlockId.fromIndex(4);
    const b_next = ir.BlockId.fromIndex(5);
    const b_done = ir.BlockId.fromIndex(6);
    const i_cond = ir.InstructionId.fromIndex(0);
    const i_control = ir.InstructionId.fromIndex(1);
    const i_limit = ir.InstructionId.fromIndex(2);
    const i_step = ir.InstructionId.fromIndex(3);
    const i_true = ir.InstructionId.fromIndex(4);
    const i_false = ir.InstructionId.fromIndex(5);
    const i_next = ir.InstructionId.fromIndex(6);
    const v_left = ir.ValueId.fromIndex(0);
    const v_right = ir.ValueId.fromIndex(1);
    const v_cond = ir.ValueId.fromIndex(2);
    const v_control = ir.ValueId.fromIndex(3);
    const v_limit = ir.ValueId.fromIndex(4);
    const v_step = ir.ValueId.fromIndex(5);
    const v_true = ir.ValueId.fromIndex(6);
    const v_false = ir.ValueId.fromIndex(7);
    const v_header_control = ir.ValueId.fromIndex(8);
    const v_header_limit = ir.ValueId.fromIndex(9);
    const v_header_step = ir.ValueId.fromIndex(10);
    const v_header_initial = ir.ValueId.fromIndex(11);
    const v_has = ir.ValueId.fromIndex(12);
    const v_normalized_limit = ir.ValueId.fromIndex(13);
    const v_normalized_step = ir.ValueId.fromIndex(14);
    const v_index = ir.ValueId.fromIndex(15);
    const v_body_index = ir.ValueId.fromIndex(16);
    const values = [_]ir.Value{
        .{ .id = v_left, .function = f, .type = .number, .origin = .{ .parameter = 0 } },
        .{ .id = v_right, .function = f, .type = .number, .origin = .{ .parameter = 1 } },
        .{ .id = v_cond, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_cond, .index = 0 } } },
        .{ .id = v_control, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_control, .index = 0 } } },
        .{ .id = v_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_limit, .index = 0 } } },
        .{ .id = v_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_step, .index = 0 } } },
        .{ .id = v_true, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
        .{ .id = v_false, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_false, .index = 0 } } },
        .{ .id = v_header_control, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 0 } } },
        .{ .id = v_header_limit, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 1 } } },
        .{ .id = v_header_step, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 2 } } },
        .{ .id = v_header_initial, .function = f, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_header, .index = 3 } } },
        .{ .id = v_has, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 0 } } },
        .{ .id = v_normalized_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 1 } } },
        .{ .id = v_normalized_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 2 } } },
        .{ .id = v_index, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 3 } } },
        .{ .id = v_body_index, .function = f, .type = .number, .origin = .{ .block_parameter = .{ .block = b_body, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = i_cond, .block = b_while, .operation = .{ .binary = .{ .operator = .less, .left = v_left, .right = v_right } }, .results = &.{v_cond}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_control, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_control}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_limit, .block = b_pre, .operation = .{ .constant = .{ .integer = "3" } }, .results = &.{v_limit}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_step, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_step}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_true, .block = b_pre, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_false, .block = b_pre, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{v_false}, .effects = .pure, .evidence = &.{proof} },
        .{
            .id = i_next,
            .block = b_header,
            .operation = .{ .numeric_for_next = .{
                .control = v_header_control,
                .limit = v_header_limit,
                .step = v_header_step,
                .initial = v_header_initial,
            } },
            .results = &.{ v_has, v_normalized_limit, v_normalized_step, v_index },
            .effects = .numeric_for_next,
            .evidence = &.{proof},
        },
    };
    const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f, .terminator = .{ .jump = .{ .target = b_while } }, .evidence = &.{proof} },
        .{
            .id = b_while,
            .function = f,
            .instructions = &.{i_cond},
            .terminator = .{ .branch = .{
                .condition = v_cond,
                .then_edge = .{ .target = b_pre },
                .else_edge = .{ .target = b_done },
            } },
            .evidence = &.{proof},
        },
        .{
            .id = b_pre,
            .function = f,
            .instructions = &.{ i_control, i_limit, i_step, i_true, i_false },
            .terminator = .{ .jump = .{ .target = b_header, .arguments = &.{ v_control, v_limit, v_step, v_true } } },
            .evidence = &.{proof},
        },
        .{
            .id = b_header,
            .function = f,
            .parameters = &.{ v_header_control, v_header_limit, v_header_step, v_header_initial },
            .instructions = &.{i_next},
            .terminator = .{ .branch = .{
                .condition = v_has,
                .then_edge = .{ .target = b_body, .arguments = &.{v_index} },
                .else_edge = .{ .target = b_next },
            } },
            .evidence = &.{proof},
        },
        .{ .id = b_body, .function = f, .parameters = &.{v_body_index}, .terminator = .{ .return_values = &.{v_body_index} }, .evidence = &.{proof} },
        .{ .id = b_next, .function = f, .terminator = .{ .jump = .{ .target = b_while } }, .evidence = &.{proof} },
        .{ .id = b_done, .function = f, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{
        .id = f,
        .parameters = &.{ v_left, v_right },
        .blocks = &.{ b_entry, b_while, b_pre, b_header, b_body, b_next, b_done },
        .entry_block = b_entry,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:always-returning-iteration-in-loop" }};
    const program: ir.Program = .{
        .program_id = "always-returning-iteration-in-loop",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    var for_lines: usize = 0;
    var for_indent: ?[]const u8 = null;
    var loop_closed = false;
    var body_returns = false;
    var body_breaks = false;
    var body_branches = false;
    var lines = std.mem.splitScalar(u8, source, '\n');
    while (lines.next()) |line| {
        const trimmed = std.mem.trim(u8, line, " \t");
        const indent = line[0 .. line.len - std.mem.trimStart(u8, line, " \t").len];
        if (std.mem.startsWith(u8, trimmed, "for ") and std.mem.endsWith(u8, trimmed, " do")) {
            for_lines += 1;
            for_indent = indent;
            continue;
        }
        const open = for_indent orelse continue;
        if (loop_closed) continue;
        if (std.mem.eql(u8, trimmed, "end") and std.mem.eql(u8, indent, open)) {
            loop_closed = true;
            continue;
        }
        if (std.mem.indexOf(u8, trimmed, "return") != null) body_returns = true;
        if (std.mem.indexOf(u8, trimmed, "break") != null) body_breaks = true;
        if (std.mem.startsWith(u8, trimmed, "if ") or std.mem.startsWith(u8, trimmed, "elseif ") or
            std.mem.indexOf(u8, trimmed, " if ") != null) body_branches = true;
    }
    try std.testing.expectEqual(@as(usize, 1), for_lines);
    try std.testing.expect(loop_closed);
    try std.testing.expect(body_returns);
    try std.testing.expect(!body_breaks);
    try std.testing.expect(!body_branches);
    try std.testing.expect(std.mem.indexOf(u8, source, "while ") != null);
}

test "direct-locals declares a fused generic-for producer's operand before the preheader's closed do" {
    const allocator = std.testing.allocator;
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_header = ir.BlockId.fromIndex(1);
    const b_body = ir.BlockId.fromIndex(2);
    const b_exit = ir.BlockId.fromIndex(3);
    const p_pack = ir.ValuePackId.fromIndex(0);

    const observable_count: usize = 32;
    // Entry block instructions: 32 ambient reads, then make_table, keep read, keep
    // call, ipairs read, ipairs call, adjust_pack, true, false (40 total); the
    // generic_for_next lives in the header, so 41 instructions in all.
    const instruction_count: usize = observable_count + 9;
    // 32 observable results + 8 entry values + 4 header parameters + 5
    // generic_for_next results + 2 body parameters = 51 values.
    const value_count: usize = observable_count + 19;

    const i_make = ir.InstructionId.fromIndex(32);
    const i_keep_get = ir.InstructionId.fromIndex(33);
    const i_keep_call = ir.InstructionId.fromIndex(34);
    const i_ipairs_get = ir.InstructionId.fromIndex(35);
    const i_ipairs_call = ir.InstructionId.fromIndex(36);
    const i_adjust = ir.InstructionId.fromIndex(37);
    const i_true = ir.InstructionId.fromIndex(38);
    const i_false = ir.InstructionId.fromIndex(39);
    const i_gfn = ir.InstructionId.fromIndex(40);

    const v_list = ir.ValueId.fromIndex(32);
    const v_keep = ir.ValueId.fromIndex(33);
    const v_ipairs = ir.ValueId.fromIndex(34);
    const v_adj0 = ir.ValueId.fromIndex(35);
    const v_adj1 = ir.ValueId.fromIndex(36);
    const v_adj2 = ir.ValueId.fromIndex(37);
    const v_true = ir.ValueId.fromIndex(38);
    const v_false = ir.ValueId.fromIndex(39);
    const hp0 = ir.ValueId.fromIndex(40);
    const hp1 = ir.ValueId.fromIndex(41);
    const hp2 = ir.ValueId.fromIndex(42);
    const hp3 = ir.ValueId.fromIndex(43);
    const r0 = ir.ValueId.fromIndex(44);
    const r1 = ir.ValueId.fromIndex(45);
    const r2 = ir.ValueId.fromIndex(46);
    const r3 = ir.ValueId.fromIndex(47);
    const r4 = ir.ValueId.fromIndex(48);
    const bp0 = ir.ValueId.fromIndex(49);
    const bp1 = ir.ValueId.fromIndex(50);

    const values = try arena.alloc(ir.Value, value_count);
    const instructions = try arena.alloc(ir.Instruction, instruction_count);
    const instruction_ids = try arena.alloc(ir.InstructionId, instruction_count);

    for (0..observable_count) |index| {
        const instruction_id = ir.InstructionId.fromIndex(index);
        const value_id = ir.ValueId.fromIndex(index);
        instruction_ids[index] = instruction_id;
        values[index] = .{
            .id = value_id,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } },
        };
        instructions[index] = .{
            .id = instruction_id,
            .block = b_entry,
            .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "observable" } },
            .results = try arena.dupe(ir.ValueId, &.{value_id}),
            .effects = .semantic_environment_read,
            .evidence = &.{proof},
        };
    }

    values[32] = .{ .id = v_list, .function = function_id, .name_hint = "list", .origin = .{ .instruction_result = .{ .instruction = i_make, .index = 0 } } };
    values[33] = .{ .id = v_keep, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_keep_get, .index = 0 } } };
    values[34] = .{ .id = v_ipairs, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_ipairs_get, .index = 0 } } };
    values[35] = .{ .id = v_adj0, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_adjust, .index = 0 } } };
    values[36] = .{ .id = v_adj1, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_adjust, .index = 1 } } };
    values[37] = .{ .id = v_adj2, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_adjust, .index = 2 } } };
    values[38] = .{ .id = v_true, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } };
    values[39] = .{ .id = v_false, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_false, .index = 0 } } };
    values[40] = .{ .id = hp0, .function = function_id, .origin = .{ .block_parameter = .{ .block = b_header, .index = 0 } } };
    values[41] = .{ .id = hp1, .function = function_id, .origin = .{ .block_parameter = .{ .block = b_header, .index = 1 } } };
    values[42] = .{ .id = hp2, .function = function_id, .origin = .{ .block_parameter = .{ .block = b_header, .index = 2 } } };
    values[43] = .{ .id = hp3, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_header, .index = 3 } } };
    values[44] = .{ .id = r0, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 0 } } };
    values[45] = .{ .id = r1, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 1 } } };
    values[46] = .{ .id = r2, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 2 } } };
    values[47] = .{ .id = r3, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 3 } } };
    values[48] = .{ .id = r4, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 4 } } };
    values[49] = .{ .id = bp0, .function = function_id, .name_hint = "key", .origin = .{ .block_parameter = .{ .block = b_body, .index = 0 } } };
    values[50] = .{ .id = bp1, .function = function_id, .name_hint = "value", .origin = .{ .block_parameter = .{ .block = b_body, .index = 1 } } };

    instruction_ids[32] = i_make;
    instructions[32] = .{ .id = i_make, .block = b_entry, .operation = .{ .make_table = {} }, .results = try arena.dupe(ir.ValueId, &.{v_list}), .effects = .table_constructor, .evidence = &.{proof} };
    instruction_ids[33] = i_keep_get;
    instructions[33] = .{ .id = i_keep_get, .block = b_entry, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "keep" } }, .results = try arena.dupe(ir.ValueId, &.{v_keep}), .effects = .semantic_environment_read, .evidence = &.{proof} };
    instruction_ids[34] = i_keep_call;
    instructions[34] = .{ .id = i_keep_call, .block = b_entry, .operation = .{ .call = .{ .callee = v_keep, .arguments = try arena.dupe(ir.ValueId, &.{v_list}), .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call, .evidence = &.{proof} };
    instruction_ids[35] = i_ipairs_get;
    instructions[35] = .{ .id = i_ipairs_get, .block = b_entry, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "ipairs" } }, .results = try arena.dupe(ir.ValueId, &.{v_ipairs}), .effects = .semantic_environment_read, .evidence = &.{proof} };
    instruction_ids[36] = i_ipairs_call;
    instructions[36] = .{ .id = i_ipairs_call, .block = b_entry, .operation = .{ .call = .{ .callee = v_ipairs, .arguments = try arena.dupe(ir.ValueId, &.{v_list}), .result_arity = .{ .variadic = {} } } }, .results = &.{}, .pack_result = p_pack, .effects = .dynamic_call, .evidence = &.{proof} };
    instruction_ids[37] = i_adjust;
    instructions[37] = .{ .id = i_adjust, .block = b_entry, .operation = .{ .adjust_pack = p_pack }, .results = try arena.dupe(ir.ValueId, &.{ v_adj0, v_adj1, v_adj2 }), .effects = .pure, .evidence = &.{proof} };
    instruction_ids[38] = i_true;
    instructions[38] = .{ .id = i_true, .block = b_entry, .operation = .{ .constant = .{ .boolean = true } }, .results = try arena.dupe(ir.ValueId, &.{v_true}), .effects = .pure, .evidence = &.{proof} };
    instruction_ids[39] = i_false;
    instructions[39] = .{ .id = i_false, .block = b_entry, .operation = .{ .constant = .{ .boolean = false } }, .results = try arena.dupe(ir.ValueId, &.{v_false}), .effects = .pure, .evidence = &.{proof} };
    instruction_ids[40] = i_gfn;
    instructions[40] = .{ .id = i_gfn, .block = b_header, .operation = .{ .generic_for_next = .{ .iterator = hp0, .state = hp1, .control = hp2, .initial = hp3, .variable_count = 2 } }, .results = try arena.dupe(ir.ValueId, &.{ r0, r1, r2, r3, r4 }), .effects = ir.EffectSummary.generic_for_next, .evidence = &.{proof} };

    const blocks = [_]ir.Block{
        .{
            .id = b_entry,
            .function = function_id,
            .instructions = instruction_ids[0..40],
            .terminator = .{ .jump = .{ .target = b_header, .arguments = try arena.dupe(ir.ValueId, &.{ v_adj0, v_adj1, v_adj2, v_true }) } },
            .evidence = &.{proof},
        },
        .{
            .id = b_header,
            .function = function_id,
            .parameters = try arena.dupe(ir.ValueId, &.{ hp0, hp1, hp2, hp3 }),
            .instructions = instruction_ids[40..41],
            .terminator = .{ .branch = .{
                .condition = r0,
                .then_edge = .{ .target = b_body, .arguments = try arena.dupe(ir.ValueId, &.{ r3, r4 }) },
                .else_edge = .{ .target = b_exit },
            } },
            .evidence = &.{proof},
        },
        .{
            .id = b_body,
            .function = function_id,
            .parameters = try arena.dupe(ir.ValueId, &.{ bp0, bp1 }),
            .terminator = .{ .jump = .{ .target = b_header, .arguments = try arena.dupe(ir.ValueId, &.{ r1, r2, r3, v_false }) } },
            .evidence = &.{proof},
        },
        .{
            .id = b_exit,
            .function = function_id,
            .terminator = .{ .return_values = &.{} },
            .evidence = &.{proof},
        },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ b_entry, b_header, b_body, b_exit },
        .entry_block = b_entry,
        .evidence = &.{proof},
    }};
    const value_packs = [_]ir.ValuePack{.{
        .id = p_pack,
        .function = function_id,
        .origin = .{ .instruction_result = i_ipairs_call },
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:generic-initializer-scope" }};
    const program: ir.Program = .{
        .program_id = "generic-initializer-scope-unit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = instructions,
        .values = values,
        .value_packs = &value_packs,
        .evidence = &evidence,
    };

    const source = try lifter.emit_luau.emitAdmittedAllocForTarget(allocator, &program, .direct_locals_luau);
    defer allocator.free(source);

    // (G1) the structured layout, not the dispatcher.
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_pc") == null);

    // (G2) the fused producer is written onto the `for` line; read the table name X.
    var table_name: []const u8 = "";
    var for_line_index: ?usize = null;
    {
        var lines = std.mem.splitScalar(u8, source, '\n');
        var index: usize = 0;
        while (lines.next()) |line| : (index += 1) {
            const trimmed = std.mem.trim(u8, line, " \t");
            if (std.mem.startsWith(u8, trimmed, "for ") and std.mem.endsWith(u8, trimmed, " do") and
                std.mem.indexOf(u8, trimmed, " in ipairs(") != null)
            {
                const open = std.mem.indexOf(u8, trimmed, "ipairs(").? + "ipairs(".len;
                const close = open + std.mem.indexOfScalar(u8, trimmed[open..], ')').?;
                table_name = trimmed[open..close];
                for_line_index = index;
                break;
            }
        }
    }
    try std.testing.expect(for_line_index != null);
    try std.testing.expect(table_name.len != 0);

    // (G3) at least one line whose trimmed text is exactly `do` precedes the `for` line.
    var first_do_index: ?usize = null;
    {
        var lines = std.mem.splitScalar(u8, source, '\n');
        var index: usize = 0;
        while (lines.next()) |line| : (index += 1) {
            if (std.mem.eql(u8, std.mem.trim(u8, line, " \t"), "do")) {
                first_do_index = index;
                break;
            }
        }
    }
    try std.testing.expect(first_do_index != null);
    try std.testing.expect(first_do_index.? < for_line_index.?);

    // (D) a `local` line before the first such `do` line declares X.
    var declares_table = false;
    {
        var lines = std.mem.splitScalar(u8, source, '\n');
        var index: usize = 0;
        while (lines.next()) |line| : (index += 1) {
            if (index >= first_do_index.?) break;
            const trimmed = std.mem.trim(u8, line, " \t");
            if (!std.mem.startsWith(u8, trimmed, "local ")) continue;
            const rest = trimmed["local ".len..];
            const names = if (std.mem.indexOf(u8, rest, " = ")) |eq| rest[0..eq] else rest;
            var parts = std.mem.splitScalar(u8, names, ',');
            while (parts.next()) |part| {
                if (std.mem.eql(u8, std.mem.trim(u8, part, " \t"), table_name)) declares_table = true;
            }
        }
    }
    try std.testing.expect(declares_table);
}

test "a fused generic-for producer keeps its place before a later effect in its block" {
    const allocator = std.testing.allocator;

    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_header = ir.BlockId.fromIndex(1);
    const b_body = ir.BlockId.fromIndex(2);
    const b_exit = ir.BlockId.fromIndex(3);
    const p_pack = ir.ValuePackId.fromIndex(0);

    const i_producer = ir.InstructionId.fromIndex(0);
    const i_adjust = ir.InstructionId.fromIndex(1);
    const i_effect = ir.InstructionId.fromIndex(2);
    const i_true = ir.InstructionId.fromIndex(3);
    const i_false = ir.InstructionId.fromIndex(4);
    const i_gfn = ir.InstructionId.fromIndex(5);

    const f = ir.ValueId.fromIndex(0);
    const g = ir.ValueId.fromIndex(1);
    const t = ir.ValueId.fromIndex(2);
    const v_adj0 = ir.ValueId.fromIndex(3);
    const v_adj1 = ir.ValueId.fromIndex(4);
    const v_adj2 = ir.ValueId.fromIndex(5);
    const v_true = ir.ValueId.fromIndex(6);
    const v_false = ir.ValueId.fromIndex(7);
    const hp0 = ir.ValueId.fromIndex(8);
    const hp1 = ir.ValueId.fromIndex(9);
    const hp2 = ir.ValueId.fromIndex(10);
    const hp3 = ir.ValueId.fromIndex(11);
    const r0 = ir.ValueId.fromIndex(12);
    const r1 = ir.ValueId.fromIndex(13);
    const r2 = ir.ValueId.fromIndex(14);
    const r3 = ir.ValueId.fromIndex(15);
    const r4 = ir.ValueId.fromIndex(16);
    const bp0 = ir.ValueId.fromIndex(17);
    const bp1 = ir.ValueId.fromIndex(18);

    const values = [_]ir.Value{
        .{ .id = f, .function = function_id, .type = .dynamic, .name_hint = "f", .origin = .{ .parameter = 0 } },
        .{ .id = g, .function = function_id, .type = .dynamic, .name_hint = "g", .origin = .{ .parameter = 1 } },
        .{ .id = t, .function = function_id, .type = .dynamic, .name_hint = "t", .origin = .{ .parameter = 2 } },
        .{ .id = v_adj0, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_adjust, .index = 0 } } },
        .{ .id = v_adj1, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_adjust, .index = 1 } } },
        .{ .id = v_adj2, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_adjust, .index = 2 } } },
        .{ .id = v_true, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
        .{ .id = v_false, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_false, .index = 0 } } },
        .{ .id = hp0, .function = function_id, .origin = .{ .block_parameter = .{ .block = b_header, .index = 0 } } },
        .{ .id = hp1, .function = function_id, .origin = .{ .block_parameter = .{ .block = b_header, .index = 1 } } },
        .{ .id = hp2, .function = function_id, .origin = .{ .block_parameter = .{ .block = b_header, .index = 2 } } },
        .{ .id = hp3, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_header, .index = 3 } } },
        .{ .id = r0, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 0 } } },
        .{ .id = r1, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 1 } } },
        .{ .id = r2, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 2 } } },
        .{ .id = r3, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 3 } } },
        .{ .id = r4, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 4 } } },
        .{ .id = bp0, .function = function_id, .name_hint = "key", .origin = .{ .block_parameter = .{ .block = b_body, .index = 0 } } },
        .{ .id = bp1, .function = function_id, .name_hint = "value", .origin = .{ .block_parameter = .{ .block = b_body, .index = 1 } } },
    };

    const instructions = [_]ir.Instruction{
        .{ .id = i_producer, .block = b_entry, .operation = .{ .call = .{ .callee = f, .arguments = &.{t}, .result_arity = .{ .variadic = {} } } }, .results = &.{}, .pack_result = p_pack, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = i_adjust, .block = b_entry, .operation = .{ .adjust_pack = p_pack }, .results = &.{ v_adj0, v_adj1, v_adj2 }, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_effect, .block = b_entry, .operation = .{ .call = .{ .callee = g, .arguments = &.{}, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = i_true, .block = b_entry, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_false, .block = b_entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{v_false}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_gfn, .block = b_header, .operation = .{ .generic_for_next = .{ .iterator = hp0, .state = hp1, .control = hp2, .initial = hp3, .variable_count = 2 } }, .results = &.{ r0, r1, r2, r3, r4 }, .effects = ir.EffectSummary.generic_for_next, .evidence = &.{proof} },
    };

    const blocks = [_]ir.Block{
        .{
            .id = b_entry,
            .function = function_id,
            .instructions = &.{ i_producer, i_adjust, i_effect, i_true, i_false },
            .terminator = .{ .jump = .{ .target = b_header, .arguments = &.{ v_adj0, v_adj1, v_adj2, v_true } } },
            .evidence = &.{proof},
        },
        .{
            .id = b_header,
            .function = function_id,
            .parameters = &.{ hp0, hp1, hp2, hp3 },
            .instructions = &.{i_gfn},
            .terminator = .{ .branch = .{
                .condition = r0,
                .then_edge = .{ .target = b_body, .arguments = &.{ r3, r4 } },
                .else_edge = .{ .target = b_exit },
            } },
            .evidence = &.{proof},
        },
        .{
            .id = b_body,
            .function = function_id,
            .parameters = &.{ bp0, bp1 },
            .terminator = .{ .jump = .{ .target = b_header, .arguments = &.{ r1, r2, r3, v_false } } },
            .evidence = &.{proof},
        },
        .{
            .id = b_exit,
            .function = function_id,
            .terminator = .{ .return_values = &.{} },
            .evidence = &.{proof},
        },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ f, g, t },
        .blocks = &.{ b_entry, b_header, b_body, b_exit },
        .entry_block = b_entry,
        .evidence = &.{proof},
    }};
    const value_packs = [_]ir.ValuePack{.{
        .id = p_pack,
        .function = function_id,
        .origin = .{ .instruction_result = i_producer },
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:generic-initializer-order" }};
    const program: ir.Program = .{
        .program_id = "generic-initializer-order-unit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &value_packs,
        .evidence = &evidence,
    };

    const source = try lifter.emit_luau.emitAdmittedAllocForTarget(allocator, &program, .standard_luau);
    defer allocator.free(source);

    // (G1) the structured layout, not the dispatcher.
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_pc") == null);

    // (G2) the producer call and the later effect are both present, and the loop is native.
    const producer_at = std.mem.indexOf(u8, source, "f(t)");
    const effect_at = std.mem.indexOf(u8, source, "g()");
    try std.testing.expect(producer_at != null);
    try std.testing.expect(effect_at != null);
    var native_for = false;
    {
        var lines = std.mem.splitScalar(u8, source, '\n');
        while (lines.next()) |line| {
            const trimmed = std.mem.trim(u8, line, " \t");
            if (std.mem.startsWith(u8, trimmed, "for ") and std.mem.endsWith(u8, trimmed, " do")) {
                native_for = true;
                break;
            }
        }
    }
    try std.testing.expect(native_for);

    // (D1) the fused producer keeps its place before the later effect in its block.
    try std.testing.expect(producer_at.? < effect_at.?);

    // (D2) the producer is written exactly once, never both in place and on the `for` line.
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "f(t)"));
}

test "a capture-free closure store stays before a gap that may run code" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const child_id = ir.FunctionId.fromIndex(1);
    const block_id = ir.BlockId.fromIndex(0);
    const child_block_id = ir.BlockId.fromIndex(1);
    const closure_instruction = ir.InstructionId.fromIndex(0);
    const gap_instruction = ir.InstructionId.fromIndex(1);
    const key_instruction = ir.InstructionId.fromIndex(2);
    const store_instruction = ir.InstructionId.fromIndex(3);
    const holder = ir.ValueId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(1);
    const closure = ir.ValueId.fromIndex(2);
    const key = ir.ValueId.fromIndex(3);
    const slot_value = ir.ValueId.fromIndex(4);
    const slot = ir.PlaceId.fromIndex(0);
    // The call program uses values 0-3; value 4 is the quiet gap's unused result.
    const values = [_]ir.Value{
        .{ .id = holder, .function = function_id, .type = .{ .kind = .table }, .name_hint = "holder", .origin = .{ .parameter = 0 } },
        .{ .id = callee, .function = function_id, .type = .function, .name_hint = "callee", .origin = .{ .parameter = 1 } },
        .{ .id = closure, .function = function_id, .type = .function, .origin = .{ .instruction_result = .{ .instruction = closure_instruction, .index = 0 } } },
        .{ .id = key, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = key_instruction, .index = 0 } } },
        .{ .id = slot_value, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = gap_instruction, .index = 0 } } },
    };
    const places = [_]ir.Place{.{ .id = slot, .function = function_id, .name_hint = "slot", .origin = .{ .local = 0 }, .evidence = &.{proof} }};
    const quiet_instructions = [_]ir.Instruction{
        .{ .id = closure_instruction, .block = block_id, .operation = .{ .make_closure = .{ .function = child_id, .bindings = &.{} } }, .results = &.{closure}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = gap_instruction, .block = block_id, .operation = .{ .place_read = slot }, .results = &.{slot_value}, .effects = .place_read, .evidence = &.{proof} },
        .{ .id = key_instruction, .block = block_id, .operation = .{ .constant = .{ .string = "get" } }, .results = &.{key}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = store_instruction, .block = block_id, .operation = .{ .table_set = .{ .table = holder, .key = key, .value = closure, .mode = .semantic } }, .results = &.{}, .effects = .semantic_table_write, .evidence = &.{proof} },
    };
    const call_instructions = [_]ir.Instruction{
        .{ .id = closure_instruction, .block = block_id, .operation = .{ .make_closure = .{ .function = child_id, .bindings = &.{} } }, .results = &.{closure}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = gap_instruction, .block = block_id, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = key_instruction, .block = block_id, .operation = .{ .constant = .{ .string = "get" } }, .results = &.{key}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = store_instruction, .block = block_id, .operation = .{ .table_set = .{ .table = holder, .key = key, .value = closure, .mode = .semantic } }, .results = &.{}, .effects = .semantic_table_write, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{
        .{ .id = block_id, .function = function_id, .name_hint = "entry", .instructions = &.{ closure_instruction, gap_instruction, key_instruction, store_instruction }, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
        .{ .id = child_block_id, .function = child_id, .name_hint = "entry", .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
    };
    const quiet_functions = [_]ir.Function{
        .{ .id = function_id, .name_hint = "chunk", .parameters = &.{ holder, callee }, .local_places = &.{slot}, .blocks = &.{block_id}, .entry_block = block_id, .evidence = &.{proof} },
        .{ .id = child_id, .name_hint = "child", .lexical_parent = function_id, .blocks = &.{child_block_id}, .entry_block = child_block_id, .evidence = &.{proof} },
    };
    const call_functions = [_]ir.Function{
        .{ .id = function_id, .name_hint = "chunk", .parameters = &.{ holder, callee }, .blocks = &.{block_id}, .entry_block = block_id, .evidence = &.{proof} },
        .{ .id = child_id, .name_hint = "child", .lexical_parent = function_id, .blocks = &.{child_block_id}, .entry_block = child_block_id, .evidence = &.{proof} },
    };
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:closure-store-gap" }};
    const quiet_program: ir.Program = .{
        .program_id = "closure-store-quiet-gap",
        .entry_function = function_id,
        .functions = &quiet_functions,
        .blocks = &blocks,
        .instructions = &quiet_instructions,
        .values = &values,
        .places = &places,
        .evidence = &evidence,
    };
    const call_program: ir.Program = .{
        .program_id = "closure-store-call-gap",
        .entry_function = function_id,
        .functions = &call_functions,
        .blocks = &blocks,
        .instructions = &call_instructions,
        .values = values[0..4],
        .evidence = &evidence,
    };

    // A gap that cannot run code (an exact read of a local place) leaves the closure fused into its store.
    const quiet = try emitAlloc(std.testing.allocator, &quiet_program);
    defer std.testing.allocator.free(quiet);
    try std.testing.expect(std.mem.indexOf(u8, quiet, "holder.get = function()") != null);
    // A call may replace the running function's environment (setfenv), and a closure takes the
    // environment current at its creation, so the closure is created before the call.
    const source = try emitAlloc(std.testing.allocator, &call_program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "function()").? < std.mem.indexOf(u8, source, "callee()").?);
    // A call whose summary a proved effect_summary claim narrows to an exact memory write (a callee
    // that only runs setfenv) is still a call, whatever the claim certifies: the closure is created
    // before it too.
    const term_id = ir.SolverTermId.fromIndex(0);
    const query_id = ir.QueryId.fromIndex(0);
    const certificate_id = ir.CertificateId.fromIndex(0);
    const claim_id = ir.ClaimId.fromIndex(0);
    const narrowed: ir.EffectSummary = .{ .precision = .exact, .reads_memory = true, .writes_memory = true, .may_throw = true };
    const certified_instructions = [_]ir.Instruction{
        .{ .id = closure_instruction, .block = block_id, .operation = .{ .make_closure = .{ .function = child_id, .bindings = &.{} } }, .results = &.{closure}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = gap_instruction, .block = block_id, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = narrowed, .evidence = &.{proof}, .claims = &.{claim_id} },
        .{ .id = key_instruction, .block = block_id, .operation = .{ .constant = .{ .string = "get" } }, .results = &.{key}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = store_instruction, .block = block_id, .operation = .{ .table_set = .{ .table = holder, .key = key, .value = closure, .mode = .semantic } }, .results = &.{}, .effects = .semantic_table_write, .evidence = &.{proof} },
    };
    const terms = [_]ir.SolverTerm{.{ .id = term_id, .sort = .{ .kind = .boolean }, .operation = .{ .semantic_atom = .{ .instruction_effects = gap_instruction } } }};
    const queries = [_]ir.SolverQuery{.{ .id = query_id, .kind = .prove_true, .goal = term_id }};
    const certificates = [_]ir.SolverCertificate{.{ .id = certificate_id, .query = query_id, .engine = .imported, .resolution = .proved, .evidence = &.{proof}, .certificate_digest = "fixture:instruction-effects" }};
    const claims = [_]ir.Claim{.{ .id = claim_id, .subject = .{ .instruction = gap_instruction }, .predicate = term_id, .purpose = .{ .effect_summary = narrowed }, .status = .proved, .required_for_emission = true, .evidence = &.{proof}, .query = query_id, .certificate = certificate_id }};
    const certified_program: ir.Program = .{
        .program_id = "closure-store-certified-call-gap",
        .entry_function = function_id,
        .functions = &call_functions,
        .blocks = &blocks,
        .instructions = &certified_instructions,
        .values = values[0..4],
        .evidence = &evidence,
        .solver_terms = &terms,
        .queries = &queries,
        .certificates = &certificates,
        .claims = &claims,
    };
    const certified = try emitAlloc(std.testing.allocator, &certified_program);
    defer std.testing.allocator.free(certified);
    try std.testing.expect(std.mem.indexOf(u8, certified, "function()").? < std.mem.indexOf(u8, certified, "callee()").?);
}

test "a generic-for initializer result read after the loop keeps its triple in place" {
    const allocator = std.testing.allocator;

    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_header = ir.BlockId.fromIndex(1);
    const b_body = ir.BlockId.fromIndex(2);
    const b_exit = ir.BlockId.fromIndex(3);
    const p_pack = ir.ValuePackId.fromIndex(0);

    const i_producer = ir.InstructionId.fromIndex(0);
    const i_adjust = ir.InstructionId.fromIndex(1);
    const i_true = ir.InstructionId.fromIndex(2);
    const i_false = ir.InstructionId.fromIndex(3);
    const i_gfn = ir.InstructionId.fromIndex(4);

    const f = ir.ValueId.fromIndex(0);
    const t = ir.ValueId.fromIndex(1);
    const v_step = ir.ValueId.fromIndex(2);
    const v_state = ir.ValueId.fromIndex(3);
    const v_start = ir.ValueId.fromIndex(4);
    const v_true = ir.ValueId.fromIndex(5);
    const v_false = ir.ValueId.fromIndex(6);
    const hp0 = ir.ValueId.fromIndex(7);
    const hp1 = ir.ValueId.fromIndex(8);
    const hp2 = ir.ValueId.fromIndex(9);
    const hp3 = ir.ValueId.fromIndex(10);
    const r0 = ir.ValueId.fromIndex(11);
    const r1 = ir.ValueId.fromIndex(12);
    const r2 = ir.ValueId.fromIndex(13);
    const r3 = ir.ValueId.fromIndex(14);
    const r4 = ir.ValueId.fromIndex(15);
    const bp0 = ir.ValueId.fromIndex(16);
    const bp1 = ir.ValueId.fromIndex(17);

    const values = [_]ir.Value{
        .{ .id = f, .function = function_id, .type = .dynamic, .name_hint = "f", .origin = .{ .parameter = 0 } },
        .{ .id = t, .function = function_id, .type = .dynamic, .name_hint = "t", .origin = .{ .parameter = 1 } },
        .{ .id = v_step, .function = function_id, .name_hint = "step", .origin = .{ .instruction_result = .{ .instruction = i_adjust, .index = 0 } } },
        .{ .id = v_state, .function = function_id, .name_hint = "state", .origin = .{ .instruction_result = .{ .instruction = i_adjust, .index = 1 } } },
        .{ .id = v_start, .function = function_id, .name_hint = "start", .origin = .{ .instruction_result = .{ .instruction = i_adjust, .index = 2 } } },
        .{ .id = v_true, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
        .{ .id = v_false, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_false, .index = 0 } } },
        .{ .id = hp0, .function = function_id, .origin = .{ .block_parameter = .{ .block = b_header, .index = 0 } } },
        .{ .id = hp1, .function = function_id, .origin = .{ .block_parameter = .{ .block = b_header, .index = 1 } } },
        .{ .id = hp2, .function = function_id, .origin = .{ .block_parameter = .{ .block = b_header, .index = 2 } } },
        .{ .id = hp3, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_header, .index = 3 } } },
        .{ .id = r0, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 0 } } },
        .{ .id = r1, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 1 } } },
        .{ .id = r2, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 2 } } },
        .{ .id = r3, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 3 } } },
        .{ .id = r4, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = i_gfn, .index = 4 } } },
        .{ .id = bp0, .function = function_id, .name_hint = "key", .origin = .{ .block_parameter = .{ .block = b_body, .index = 0 } } },
        .{ .id = bp1, .function = function_id, .name_hint = "value", .origin = .{ .block_parameter = .{ .block = b_body, .index = 1 } } },
    };

    const instructions = [_]ir.Instruction{
        .{ .id = i_producer, .block = b_entry, .operation = .{ .call = .{ .callee = f, .arguments = &.{t}, .result_arity = .{ .variadic = {} } } }, .results = &.{}, .pack_result = p_pack, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = i_adjust, .block = b_entry, .operation = .{ .adjust_pack = p_pack }, .results = &.{ v_step, v_state, v_start }, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_true, .block = b_entry, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_false, .block = b_entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{v_false}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_gfn, .block = b_header, .operation = .{ .generic_for_next = .{ .iterator = hp0, .state = hp1, .control = hp2, .initial = hp3, .variable_count = 2 } }, .results = &.{ r0, r1, r2, r3, r4 }, .effects = ir.EffectSummary.generic_for_next, .evidence = &.{proof} },
    };

    const blocks = [_]ir.Block{
        .{
            .id = b_entry,
            .function = function_id,
            .instructions = &.{ i_producer, i_adjust, i_true, i_false },
            .terminator = .{ .jump = .{ .target = b_header, .arguments = &.{ v_step, v_state, v_start, v_true } } },
            .evidence = &.{proof},
        },
        .{
            .id = b_header,
            .function = function_id,
            .parameters = &.{ hp0, hp1, hp2, hp3 },
            .instructions = &.{i_gfn},
            .terminator = .{ .branch = .{
                .condition = r0,
                .then_edge = .{ .target = b_body, .arguments = &.{ r3, r4 } },
                .else_edge = .{ .target = b_exit },
            } },
            .evidence = &.{proof},
        },
        .{
            .id = b_body,
            .function = function_id,
            .parameters = &.{ bp0, bp1 },
            .terminator = .{ .jump = .{ .target = b_header, .arguments = &.{ r1, r2, r3, v_false } } },
            .evidence = &.{proof},
        },
        .{
            .id = b_exit,
            .function = function_id,
            .terminator = .{ .return_values = &.{v_start} },
            .evidence = &.{proof},
        },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ f, t },
        .blocks = &.{ b_entry, b_header, b_body, b_exit },
        .entry_block = b_entry,
        .evidence = &.{proof},
    }};
    const value_packs = [_]ir.ValuePack{.{
        .id = p_pack,
        .function = function_id,
        .origin = .{ .instruction_result = i_producer },
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:generic-initializer-read-after" }};
    const program: ir.Program = .{
        .program_id = "generic-initializer-read-after-unit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &value_packs,
        .evidence = &evidence,
    };

    const source = try lifter.emit_luau.emitAdmittedAllocForTarget(allocator, &program, .standard_luau);
    defer allocator.free(source);

    // (G1) the structured layout, not the dispatcher.
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_pc") == null);

    // (G2) the producer call and the read after the loop are present, and the loop is native.
    try std.testing.expect(std.mem.indexOf(u8, source, "f(t)") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "return start") != null);
    var for_at: ?usize = null;
    var fused_for = false;
    {
        var offset: usize = 0;
        var lines = std.mem.splitScalar(u8, source, '\n');
        while (lines.next()) |line| : (offset += line.len + 1) {
            const trimmed = std.mem.trim(u8, line, " \t");
            if (std.mem.startsWith(u8, trimmed, "for ") and std.mem.endsWith(u8, trimmed, " do")) {
                if (for_at == null) for_at = offset;
                if (std.mem.indexOf(u8, trimmed, "f(t)") != null) fused_for = true;
            }
        }
    }
    try std.testing.expect(for_at != null);

    // (D1) a producer whose result is read after the loop is not written on the `for` line.
    try std.testing.expect(!fused_for);

    // (D2) the triple is written in place, before the loop.
    const triple_at = std.mem.indexOf(u8, source, "local step, state, start = f(t)");
    try std.testing.expect(triple_at != null);
    try std.testing.expect(triple_at.? < for_at.?);

    // (D3) the producer is written exactly once.
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "f(t)"));
}

test "a loop left through the exit of the loop around it declares that exit's flag in the outer loop" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const outer_header = ir.BlockId.fromIndex(1);
    const inner_header = ir.BlockId.fromIndex(2);
    const inner_body = ir.BlockId.fromIndex(3);
    const exit_block = ir.BlockId.fromIndex(4);
    const inner_latch = ir.BlockId.fromIndex(5);
    const outer_call = ir.InstructionId.fromIndex(0);
    const latch_call = ir.InstructionId.fromIndex(1);
    const again = ir.ValueId.fromIndex(0);
    const stay = ir.ValueId.fromIndex(1);
    const observe = ir.ValueId.fromIndex(2);
    const go = ir.ValueId.fromIndex(3);
    const values = [_]ir.Value{
        .{ .id = again, .function = function_id, .type = .boolean, .name_hint = "again", .origin = .{ .parameter = 0 } },
        .{ .id = stay, .function = function_id, .type = .boolean, .name_hint = "stay", .origin = .{ .parameter = 1 } },
        .{ .id = observe, .function = function_id, .type = .function, .name_hint = "observe", .origin = .{ .parameter = 2 } },
        .{ .id = go, .function = function_id, .type = .boolean, .name_hint = "go", .origin = .{ .parameter = 3 } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = outer_call, .block = outer_header, .operation = .{ .call = .{ .callee = observe, .arguments = &.{}, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = latch_call, .block = inner_latch, .operation = .{ .call = .{ .callee = observe, .arguments = &.{}, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call, .evidence = &.{proof} },
    };
    // The outer loop (header 1) is left only through the inner loop's exit (block 4); the inner body (block 3)
    // continues the outer loop or, through block 5, the inner loop.
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } }, .evidence = &.{proof} },
        .{ .id = outer_header, .function = function_id, .instructions = &.{outer_call}, .terminator = .{ .jump = .{ .target = inner_header } }, .evidence = &.{proof} },
        .{ .id = inner_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = again,
            .then_edge = .{ .target = inner_body },
            .else_edge = .{ .target = exit_block },
        } }, .evidence = &.{proof} },
        .{ .id = inner_body, .function = function_id, .terminator = .{ .branch = .{
            .condition = stay,
            .then_edge = .{ .target = outer_header },
            .else_edge = .{ .target = inner_latch },
        } }, .evidence = &.{proof} },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
        .{ .id = inner_latch, .function = function_id, .instructions = &.{latch_call}, .terminator = .{ .jump = .{ .target = inner_header } }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ again, stay, observe, go },
        .blocks = &.{ entry, outer_header, inner_header, inner_body, exit_block, inner_latch },
        .entry_block = entry,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:nested-loop-enclosing-exit" }};
    const program: ir.Program = .{
        .program_id = "generic-nested-loop-enclosing-exit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    // An outer loop with no exit test of its own.
    const untested = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(untested);
    try expectExitFlagDeclaredInOuterLoop(untested);

    // The same loops with an exit test in the outer header.
    blocks[outer_header.index()].terminator = .{ .branch = .{
        .condition = go,
        .then_edge = .{ .target = inner_header },
        .else_edge = .{ .target = exit_block },
    } };
    const tested = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(tested);
    try expectExitFlagDeclaredInOuterLoop(tested);
}

/// The flag of block 4 (the exit both loops share) is declared once, inside the outer loop and before its body,
/// and before any read or write of it.
fn expectExitFlagDeclaredInOuterLoop(source: []const u8) !void {
    const declaration_text = "local __lifter_escape_4 = false\n";
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, declaration_text));
    const declaration = std.mem.indexOf(u8, source, declaration_text) orelse return error.TestUnexpectedResult;
    const outer_loop = std.mem.indexOf(u8, source, "while true do\n") orelse return error.TestUnexpectedResult;
    const body_wrapper = std.mem.indexOf(u8, source, "repeat\n") orelse return error.TestUnexpectedResult;
    const first_write = std.mem.indexOf(u8, source, "__lifter_escape_4 = true\n") orelse return error.TestUnexpectedResult;
    const first_read = std.mem.indexOf(u8, source, "if __lifter_escape_4 then\n") orelse return error.TestUnexpectedResult;
    try std.testing.expect(outer_loop < declaration);
    try std.testing.expect(declaration < body_wrapper);
    try std.testing.expect(declaration < first_write);
    try std.testing.expect(declaration < first_read);
}

test "a structurable closure of an unstructurable entry keeps its own layout" {
    // The entry opens with a two-entry cycle that never iterates, so the structurer refuses the entry and it is
    // written flat, while the closure it makes has one block and structures by itself. An explicit dispatcher
    // request writes both functions flat; without it only the entry is flat.
    const proof = ir.EvidenceId.fromIndex(0);
    const entry_id = ir.FunctionId.fromIndex(0);
    const closure_id = ir.FunctionId.fromIndex(1);
    const start_block = ir.BlockId.fromIndex(0);
    const first_block = ir.BlockId.fromIndex(1);
    const second_block = ir.BlockId.fromIndex(2);
    const exit_block = ir.BlockId.fromIndex(3);
    const closure_block = ir.BlockId.fromIndex(4);
    const never_instruction = ir.InstructionId.fromIndex(0);
    const make_instruction = ir.InstructionId.fromIndex(1);
    const never = ir.ValueId.fromIndex(0);
    const closure = ir.ValueId.fromIndex(1);
    const parameter = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = never, .function = entry_id, .type = .boolean, .name_hint = "never", .origin = .{ .instruction_result = .{ .instruction = never_instruction, .index = 0 } } },
        .{ .id = closure, .function = entry_id, .type = .function, .name_hint = "closure", .origin = .{ .instruction_result = .{ .instruction = make_instruction, .index = 0 } } },
        .{ .id = parameter, .function = closure_id, .type = .dynamic, .name_hint = "value", .origin = .{ .parameter = 0 } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = never_instruction, .block = start_block, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{never}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = make_instruction, .block = start_block, .operation = .{ .make_closure = .{
            .function = closure_id,
            .bindings = &.{},
        } }, .results = &.{closure}, .effects = .pure, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{
        .{ .id = start_block, .function = entry_id, .instructions = &.{ never_instruction, make_instruction }, .terminator = .{ .branch = .{ .condition = never, .then_edge = .{ .target = first_block }, .else_edge = .{ .target = second_block } } }, .evidence = &.{proof} },
        .{ .id = first_block, .function = entry_id, .terminator = .{ .branch = .{ .condition = never, .then_edge = .{ .target = second_block }, .else_edge = .{ .target = exit_block } } }, .evidence = &.{proof} },
        .{ .id = second_block, .function = entry_id, .terminator = .{ .branch = .{ .condition = never, .then_edge = .{ .target = first_block }, .else_edge = .{ .target = exit_block } } }, .evidence = &.{proof} },
        .{ .id = exit_block, .function = entry_id, .terminator = .{ .return_values = &.{closure} }, .evidence = &.{proof} },
        .{ .id = closure_block, .function = closure_id, .terminator = .{ .return_values = &.{parameter} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{
        .{ .id = entry_id, .blocks = &.{ start_block, first_block, second_block, exit_block }, .entry_block = start_block, .evidence = &.{proof} },
        .{ .id = closure_id, .lexical_parent = entry_id, .parameters = &.{parameter}, .blocks = &.{closure_block}, .entry_block = closure_block, .evidence = &.{proof} },
    };
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:structurable-closure-of-unstructurable-entry" }};
    const program: ir.Program = .{
        .program_id = "structurable-closure-of-unstructurable-entry",
        .entry_function = entry_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const dispatcher = try lifter.emit_luau.emitAllocForTargetWithOptions(
        std.testing.allocator,
        &program,
        .standard_luau,
        .{ .force_dispatcher = true },
    );
    defer std.testing.allocator.free(dispatcher);
    try std.testing.expectEqual(@as(usize, 2), std.mem.count(u8, dispatcher, "local __lifter_pc"));
    const automatic = try lifter.emit_luau.emitAllocForTargetWithOptions(
        std.testing.allocator,
        &program,
        .standard_luau,
        .{},
    );
    defer std.testing.allocator.free(automatic);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, automatic, "local __lifter_pc"));
}

test "the function probe writes a structurable closure in its own layout as publication does" {
    // The entry is structured and makes an outer closure that opens with a two-entry cycle that never iterates, so
    // the outer closure is flat by its own decision; the inner closure it makes has one block and structures by
    // itself. Publication writes only the outer closure flat, and the probe of the outer closure agrees.
    const proof = ir.EvidenceId.fromIndex(0);
    const entry_id = ir.FunctionId.fromIndex(0);
    const outer_id = ir.FunctionId.fromIndex(1);
    const inner_id = ir.FunctionId.fromIndex(2);
    const entry_block = ir.BlockId.fromIndex(0);
    const start_block = ir.BlockId.fromIndex(1);
    const first_block = ir.BlockId.fromIndex(2);
    const second_block = ir.BlockId.fromIndex(3);
    const exit_block = ir.BlockId.fromIndex(4);
    const inner_block = ir.BlockId.fromIndex(5);
    const make_outer_instruction = ir.InstructionId.fromIndex(0);
    const never_instruction = ir.InstructionId.fromIndex(1);
    const make_inner_instruction = ir.InstructionId.fromIndex(2);
    const outer_closure = ir.ValueId.fromIndex(0);
    const never = ir.ValueId.fromIndex(1);
    const inner_closure = ir.ValueId.fromIndex(2);
    const parameter = ir.ValueId.fromIndex(3);
    const values = [_]ir.Value{
        .{ .id = outer_closure, .function = entry_id, .type = .function, .name_hint = "outer_closure", .origin = .{ .instruction_result = .{ .instruction = make_outer_instruction, .index = 0 } } },
        .{ .id = never, .function = outer_id, .type = .boolean, .name_hint = "never", .origin = .{ .instruction_result = .{ .instruction = never_instruction, .index = 0 } } },
        .{ .id = inner_closure, .function = outer_id, .type = .function, .name_hint = "inner_closure", .origin = .{ .instruction_result = .{ .instruction = make_inner_instruction, .index = 0 } } },
        .{ .id = parameter, .function = inner_id, .type = .dynamic, .name_hint = "value", .origin = .{ .parameter = 0 } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = make_outer_instruction, .block = entry_block, .operation = .{ .make_closure = .{
            .function = outer_id,
            .bindings = &.{},
        } }, .results = &.{outer_closure}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = never_instruction, .block = start_block, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{never}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = make_inner_instruction, .block = start_block, .operation = .{ .make_closure = .{
            .function = inner_id,
            .bindings = &.{},
        } }, .results = &.{inner_closure}, .effects = .pure, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry_block, .function = entry_id, .instructions = &.{make_outer_instruction}, .terminator = .{ .return_values = &.{outer_closure} }, .evidence = &.{proof} },
        .{ .id = start_block, .function = outer_id, .instructions = &.{ never_instruction, make_inner_instruction }, .terminator = .{ .branch = .{ .condition = never, .then_edge = .{ .target = first_block }, .else_edge = .{ .target = second_block } } }, .evidence = &.{proof} },
        .{ .id = first_block, .function = outer_id, .terminator = .{ .branch = .{ .condition = never, .then_edge = .{ .target = second_block }, .else_edge = .{ .target = exit_block } } }, .evidence = &.{proof} },
        .{ .id = second_block, .function = outer_id, .terminator = .{ .branch = .{ .condition = never, .then_edge = .{ .target = first_block }, .else_edge = .{ .target = exit_block } } }, .evidence = &.{proof} },
        .{ .id = exit_block, .function = outer_id, .terminator = .{ .return_values = &.{inner_closure} }, .evidence = &.{proof} },
        .{ .id = inner_block, .function = inner_id, .terminator = .{ .return_values = &.{parameter} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{
        .{ .id = entry_id, .blocks = &.{entry_block}, .entry_block = entry_block, .evidence = &.{proof} },
        .{ .id = outer_id, .lexical_parent = entry_id, .blocks = &.{ start_block, first_block, second_block, exit_block }, .entry_block = start_block, .evidence = &.{proof} },
        .{ .id = inner_id, .lexical_parent = outer_id, .parameters = &.{parameter}, .blocks = &.{inner_block}, .entry_block = inner_block, .evidence = &.{proof} },
    };
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:function-probe-structurable-closure" }};
    const program: ir.Program = .{
        .program_id = "function-probe-structurable-closure",
        .entry_function = entry_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const published = try lifter.emit_luau.emitAllocForTargetWithOptions(
        std.testing.allocator,
        &program,
        .standard_luau,
        .{},
    );
    defer std.testing.allocator.free(published);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, published, "local __lifter_pc"));
    const probed = try lifter.emit_luau.emitAdmittedFunctionAlloc(
        std.testing.allocator,
        &program,
        .standard_luau,
        ir.FunctionId.fromIndex(1),
    );
    defer std.testing.allocator.free(probed);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, probed, "local __lifter_pc"));
}

test "closure stores whose target renders in parentheses open their own block" {
    const proof = ir.EvidenceId.fromIndex(0);
    const chunk = ir.FunctionId.fromIndex(0);
    const child = ir.FunctionId.fromIndex(1);
    const entry = ir.BlockId.fromIndex(0);
    const child_entry = ir.BlockId.fromIndex(1);
    const call_instruction = ir.InstructionId.fromIndex(0);
    const target_instruction = ir.InstructionId.fromIndex(1);
    const key_instruction = ir.InstructionId.fromIndex(2);
    const closure_instruction = ir.InstructionId.fromIndex(3);
    const store_instruction = ir.InstructionId.fromIndex(4);
    const callee = ir.ValueId.fromIndex(0);
    const target = ir.ValueId.fromIndex(1);
    const key = ir.ValueId.fromIndex(2);
    const closure = ir.ValueId.fromIndex(3);
    const result = ir.ValueId.fromIndex(4);
    const captured = ir.ValueId.fromIndex(5);
    const capture = ir.CaptureId.fromIndex(0);
    // The program without a capture uses values 0-3; values 4 and 5 are the call result its twin's closure captures.
    const values = [_]ir.Value{
        .{ .id = callee, .function = chunk, .type = .function, .name_hint = "callee", .origin = .{ .parameter = 0 } },
        .{ .id = target, .function = chunk, .origin = .{ .instruction_result = .{ .instruction = target_instruction, .index = 0 } } },
        .{ .id = key, .function = chunk, .type = .string, .origin = .{ .instruction_result = .{ .instruction = key_instruction, .index = 0 } } },
        .{ .id = closure, .function = chunk, .type = .function, .origin = .{ .instruction_result = .{ .instruction = closure_instruction, .index = 0 } } },
        .{ .id = result, .function = chunk, .name_hint = "x", .origin = .{ .instruction_result = .{ .instruction = call_instruction, .index = 0 } } },
        .{ .id = captured, .function = child, .name_hint = "x", .origin = .{ .capture = capture } },
    };
    var instructions = [_]ir.Instruction{
        .{ .id = call_instruction, .block = entry, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = target_instruction, .block = entry, .operation = .{ .constant = .{ .nil_value = {} } }, .results = &.{target}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = key_instruction, .block = entry, .operation = .{ .constant = .{ .string = "get" } }, .results = &.{key}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = closure_instruction, .block = entry, .operation = .{ .make_closure = .{ .function = child, .bindings = &.{} } }, .results = &.{closure}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = store_instruction, .block = entry, .operation = .{ .table_set = .{ .table = target, .key = key, .value = closure, .mode = .semantic } }, .results = &.{}, .effects = .semantic_table_write, .evidence = &.{proof} },
    };
    const capture_results = [_]ir.ValueId{result};
    const capture_bindings = [_]ir.CaptureBinding{.{ .value = result }};
    var capture_instructions = instructions;
    capture_instructions[0].operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } };
    capture_instructions[0].results = &capture_results;
    capture_instructions[3].operation = .{ .make_closure = .{ .function = child, .bindings = &capture_bindings } };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = chunk, .instructions = &.{ call_instruction, target_instruction, key_instruction, closure_instruction, store_instruction }, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
        .{ .id = child_entry, .function = child, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
    };
    const capture_blocks = [_]ir.Block{
        blocks[0],
        .{ .id = child_entry, .function = child, .terminator = .{ .return_values = &.{captured} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{
        .{ .id = chunk, .name_hint = "chunk", .parameters = &.{callee}, .blocks = &.{entry}, .entry_block = entry, .evidence = &.{proof} },
        .{ .id = child, .name_hint = "child", .lexical_parent = chunk, .blocks = &.{child_entry}, .entry_block = child_entry, .evidence = &.{proof} },
    };
    const capture_functions = [_]ir.Function{
        functions[0],
        .{ .id = child, .name_hint = "child", .lexical_parent = chunk, .captures = &.{capture}, .blocks = &.{child_entry}, .entry_block = child_entry, .evidence = &.{proof} },
    };
    const captures = [_]ir.Capture{.{ .id = capture, .function = child, .kind = .{ .immutable_value = captured }, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:closure-store-into-nil" }};
    const program: ir.Program = .{
        .program_id = "closure-store-into-nil",
        .entry_function = chunk,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = values[0..4],
        .evidence = &evidence,
    };
    const capture_program: ir.Program = .{
        .program_id = "closure-store-into-nil-after-capture",
        .entry_function = chunk,
        .functions = &capture_functions,
        .blocks = &capture_blocks,
        .instructions = &capture_instructions,
        .values = &values,
        .captures = &captures,
        .evidence = &evidence,
    };

    // After a call statement the store's head begins with `(`, so the store opens its own block: as a table store, then
    // as an environment store whose environment is the value nil.
    const table_source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(table_source);
    try std.testing.expect(std.mem.indexOf(u8, table_source, "callee()\n(") == null);
    try std.testing.expect(std.mem.indexOf(u8, table_source, "callee()\ndo\n  (nil).get = function()\n  end\nend\n") != null);
    instructions[4].operation = .{ .environment_set = .{ .target = .{ .value = target }, .name = "get", .value = closure } };
    const environment_source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(environment_source);
    try std.testing.expect(std.mem.indexOf(u8, environment_source, "callee()\n(") == null);
    try std.testing.expect(std.mem.indexOf(u8, environment_source, "callee()\ndo\n  (nil).get = function()\n  end\nend\n") != null);

    // A closure that captures the call's result is written inside its bindings' `do` after `local <capture> =
    // callee()`; the store opens its own block there too.
    const captured_table_source = try emitAlloc(std.testing.allocator, &capture_program);
    defer std.testing.allocator.free(captured_table_source);
    try std.testing.expect(std.mem.indexOf(u8, captured_table_source, "callee()\n  (") == null);
    try std.testing.expect(std.mem.indexOf(u8, captured_table_source, "= callee()\n  do\n    (nil).get = function()\n") != null);
    capture_instructions[4].operation = .{ .environment_set = .{ .target = .{ .value = target }, .name = "get", .value = closure } };
    const captured_environment_source = try emitAlloc(std.testing.allocator, &capture_program);
    defer std.testing.allocator.free(captured_environment_source);
    try std.testing.expect(std.mem.indexOf(u8, captured_environment_source, "callee()\n  (") == null);
    try std.testing.expect(std.mem.indexOf(u8, captured_environment_source, "= callee()\n  do\n    (nil).get = function()\n") != null);
}

test "a condition block declares the result it first defines as a local before its if" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const then_block = ir.BlockId.fromIndex(1);
    const else_block = ir.BlockId.fromIndex(2);
    const get_id = ir.InstructionId.fromIndex(0);
    const call_id = ir.InstructionId.fromIndex(1);
    const else_id = ir.InstructionId.fromIndex(2);
    const callee = ir.ValueId.fromIndex(0);
    const result = ir.ValueId.fromIndex(1);
    const else_value = ir.ValueId.fromIndex(2);

    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .instruction_result = .{ .instruction = get_id, .index = 0 } } },
        .{ .id = result, .function = function_id, .name_hint = "result", .origin = .{ .instruction_result = .{ .instruction = call_id, .index = 0 } } },
        .{ .id = else_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = else_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = get_id, .block = entry, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "produce" } }, .results = &.{callee}, .effects = .semantic_environment_read, .evidence = &.{proof} },
        .{ .id = call_id, .block = entry, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{result}, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = else_id, .block = else_block, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{else_value}, .effects = .pure, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{ get_id, call_id }, .terminator = .{ .branch = .{ .condition = result, .then_edge = .{ .target = then_block }, .else_edge = .{ .target = else_block } } }, .evidence = &.{proof} },
        .{ .id = then_block, .function = function_id, .terminator = .{ .return_values = &.{result} }, .evidence = &.{proof} },
        .{ .id = else_block, .function = function_id, .instructions = &.{else_id}, .terminator = .{ .return_values = &.{else_value} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &.{ entry, then_block, else_block }, .entry_block = entry, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:branch-condition-block-declaration" }};
    const program: ir.Program = .{
        .program_id = "branch-condition-block-declaration",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    // The entry block is the branch's own condition block, which the region writes before its `if`. The call result is
    // read by the condition and by the then arm, so the scope plan declares it in that block: the block writes it as a
    // `local`, never as an assignment to an undeclared name.
    const source = try emitAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "local result = produce()\nif result then\n") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "produce()"));
}

/// Emits a native numeric loop from the constant 1 to the constant 3 and returns its source. A literal `step` is a
/// constant of the entry block; a null `step` is the function's one parameter, `step`, passed in its place. With
/// `back_edge` the body jumps back to the header with the next index, the normalized limit and step and `false`,
/// the shape the source frontend writes for `for i = 1, 3 do`: the header has two predecessors, each constant has
/// one use, and the start, limit and step are written inline at the `for` line. Without it the body returns its
/// index, as in "acyclic native iteration whose body always returns emits no break after the return": the header's
/// one predecessor makes its parameters aliases of the constants, which then have two uses each and are written as
/// locals.
fn emitNativeNumericLoop(allocator: std.mem.Allocator, comptime step: ?ir.Literal, comptime back_edge: bool) ![]u8 {
    const proof = ir.EvidenceId.fromIndex(0);
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_header = ir.BlockId.fromIndex(1);
    const b_body = ir.BlockId.fromIndex(2);
    const b_exit = ir.BlockId.fromIndex(3);
    // Instruction ids are dense: the start, the limit, the step (a literal step only), `true`, the header's
    // `numeric_for_next` and `false` (the back edge only).
    const step_count: usize = if (step == null) 0 else 1;
    const i_control = ir.InstructionId.fromIndex(0);
    const i_limit = ir.InstructionId.fromIndex(1);
    const i_step = ir.InstructionId.fromIndex(2);
    const i_true = ir.InstructionId.fromIndex(2 + step_count);
    const i_next = ir.InstructionId.fromIndex(3 + step_count);
    const i_false = ir.InstructionId.fromIndex(4 + step_count);
    const v_control = ir.ValueId.fromIndex(0);
    const v_limit = ir.ValueId.fromIndex(1);
    const v_step = ir.ValueId.fromIndex(2);
    const v_true = ir.ValueId.fromIndex(3);
    const v_header_control = ir.ValueId.fromIndex(4);
    const v_header_limit = ir.ValueId.fromIndex(5);
    const v_header_step = ir.ValueId.fromIndex(6);
    const v_header_initial = ir.ValueId.fromIndex(7);
    const v_has = ir.ValueId.fromIndex(8);
    const v_normalized_limit = ir.ValueId.fromIndex(9);
    const v_normalized_step = ir.ValueId.fromIndex(10);
    const v_index = ir.ValueId.fromIndex(11);
    const v_body_index = ir.ValueId.fromIndex(12);
    const v_false = ir.ValueId.fromIndex(13);
    const values = [_]ir.Value{
        .{ .id = v_control, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_control, .index = 0 } } },
        .{ .id = v_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_limit, .index = 0 } } },
        if (step == null)
            .{ .id = v_step, .function = f, .type = .number, .name_hint = "step", .origin = .{ .parameter = 0 } }
        else
            .{ .id = v_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_step, .index = 0 } } },
        .{ .id = v_true, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
        .{ .id = v_header_control, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 0 } } },
        .{ .id = v_header_limit, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 1 } } },
        .{ .id = v_header_step, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 2 } } },
        .{ .id = v_header_initial, .function = f, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_header, .index = 3 } } },
        .{ .id = v_has, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 0 } } },
        .{ .id = v_normalized_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 1 } } },
        .{ .id = v_normalized_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 2 } } },
        .{ .id = v_index, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 3 } } },
        .{ .id = v_body_index, .function = f, .type = .number, .origin = .{ .block_parameter = .{ .block = b_body, .index = 0 } } },
    } ++ (if (back_edge) [_]ir.Value{
        .{ .id = v_false, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_false, .index = 0 } } },
    } else [_]ir.Value{});
    const instructions = [_]ir.Instruction{
        .{ .id = i_control, .block = b_entry, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_control}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_limit, .block = b_entry, .operation = .{ .constant = .{ .integer = "3" } }, .results = &.{v_limit}, .effects = .pure, .evidence = &.{proof} },
    } ++ (if (step) |literal| [_]ir.Instruction{
        .{ .id = i_step, .block = b_entry, .operation = .{ .constant = literal }, .results = &.{v_step}, .effects = .pure, .evidence = &.{proof} },
    } else [_]ir.Instruction{}) ++ [_]ir.Instruction{
        .{ .id = i_true, .block = b_entry, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure, .evidence = &.{proof} },
        .{
            .id = i_next,
            .block = b_header,
            .operation = .{ .numeric_for_next = .{
                .control = v_header_control,
                .limit = v_header_limit,
                .step = v_header_step,
                .initial = v_header_initial,
            } },
            .results = &.{ v_has, v_normalized_limit, v_normalized_step, v_index },
            .effects = .numeric_for_next,
            .evidence = &.{proof},
        },
    } ++ (if (back_edge) [_]ir.Instruction{
        .{ .id = i_false, .block = b_entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{v_false}, .effects = .pure, .evidence = &.{proof} },
    } else [_]ir.Instruction{});
    const entry_instructions = [_]ir.InstructionId{ i_control, i_limit } ++
        (if (step == null) [_]ir.InstructionId{} else [_]ir.InstructionId{i_step}) ++
        [_]ir.InstructionId{i_true} ++
        (if (back_edge) [_]ir.InstructionId{i_false} else [_]ir.InstructionId{});
    const blocks = [_]ir.Block{
        .{
            .id = b_entry,
            .function = f,
            .instructions = &entry_instructions,
            .terminator = .{ .jump = .{ .target = b_header, .arguments = &.{ v_control, v_limit, v_step, v_true } } },
            .evidence = &.{proof},
        },
        .{
            .id = b_header,
            .function = f,
            .parameters = &.{ v_header_control, v_header_limit, v_header_step, v_header_initial },
            .instructions = &.{i_next},
            .terminator = .{ .branch = .{
                .condition = v_has,
                .then_edge = .{ .target = b_body, .arguments = &.{v_index} },
                .else_edge = .{ .target = b_exit },
            } },
            .evidence = &.{proof},
        },
        .{
            .id = b_body,
            .function = f,
            .parameters = &.{v_body_index},
            .terminator = if (back_edge)
                .{ .jump = .{ .target = b_header, .arguments = &.{ v_index, v_normalized_limit, v_normalized_step, v_false } } }
            else
                .{ .return_values = &.{v_body_index} },
            .evidence = &.{proof},
        },
        .{ .id = b_exit, .function = f, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{
        .id = f,
        .parameters = if (step == null) &.{v_step} else &.{},
        .blocks = &.{ b_entry, b_header, b_body, b_exit },
        .entry_block = b_entry,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:native-numeric-loop" }};
    const program: ir.Program = .{
        .program_id = "native-numeric-loop",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };
    return emitAlloc(allocator, &program);
}

/// The one line of `source` that, trimmed, starts with `for ` and ends with ` do`.
fn onlyForLine(source: []const u8) ![]const u8 {
    var for_line: ?[]const u8 = null;
    var for_lines: usize = 0;
    var lines = std.mem.splitScalar(u8, source, '\n');
    while (lines.next()) |line| {
        const trimmed = std.mem.trim(u8, line, " \t");
        if (std.mem.startsWith(u8, trimmed, "for ") and std.mem.endsWith(u8, trimmed, " do")) {
            for_lines += 1;
            for_line = trimmed;
        }
    }
    try std.testing.expectEqual(@as(usize, 1), for_lines);
    return for_line.?;
}

test "a native numeric for omits only a literal integer unit step" {
    const allocator = std.testing.allocator;
    // The controls run first. Where the start, limit and step are written inline at the `for` line, a constant step
    // other than the integer 1 stays in the line.
    const two = try emitNativeNumericLoop(allocator, .{ .integer = "2" }, true);
    defer allocator.free(two);
    try std.testing.expect(std.mem.endsWith(u8, try onlyForLine(two), " = 1, 3, 2 do"));
    // A number constant is not the literal integer 1, even when its value is one, so it stays as well.
    const number_one = try emitNativeNumericLoop(allocator, .{ .number = 1.0 }, true);
    defer allocator.free(number_one);
    try std.testing.expect(std.mem.endsWith(u8, try onlyForLine(number_one), " = 1, 3, 1 do"));
    // A step that is not a constant is written as its expression.
    const parameter = try emitNativeNumericLoop(allocator, null, true);
    defer allocator.free(parameter);
    try std.testing.expect(std.mem.endsWith(u8, try onlyForLine(parameter), " = 1, 3, step do"));
    // A step 1 that the line reads from a declared local keeps its place, so that local stays declared and read.
    const local_one = try emitNativeNumericLoop(allocator, .{ .integer = "1" }, false);
    defer allocator.free(local_one);
    try std.testing.expect(std.mem.endsWith(u8, try onlyForLine(local_one), " = value_0, value_1, value_2 do"));
    try std.testing.expect(std.mem.indexOf(u8, local_one, "local value_0 = 1\nlocal value_1 = 3\nlocal value_2 = 1\n") != null);
    // Luau steps by 1 when the step is omitted, so the literal integer 1 written in the line is left out.
    const unit = try emitNativeNumericLoop(allocator, .{ .integer = "1" }, true);
    defer allocator.free(unit);
    try std.testing.expect(std.mem.endsWith(u8, try onlyForLine(unit), " = 1, 3 do"));
}

// The worker of a post-tested loop whose body leaves through a loop boundary's side exit once the structure feedback
// has split the loop: the side exit is written under the loop body's transfer wrapper, so it leaves by the loop exit's
// flag, which the loop declares on every pass, and its side region owns escapes to that exit as well. The fixture is
// the normalized lifted IR, since the side region exists only after the split.
test "a flagged side exit's side region declares no flag of the loop exit its arm sets after it" {
    const allocator = std.testing.allocator;
    var parsed = try lifter.codec.parse(allocator, @embedFile("testdata/side_exit_owned_escape_flag.lifter-ir.json"));
    defer parsed.deinit();
    const source = try lifter.emit_luau.emitAllocForTargetWithOptions(allocator, &parsed.value, .standard_luau, .{});
    defer allocator.free(source);
    // Written structured, and a consumer reads the loop exit's flag.
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_pc") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "if __lifter_escape_4 then") != null);
    // Below the function's own scope the flag is declared once, by the loop at the top of each pass: the side arm's
    // set after its side region, and every exit to the loop exit inside that region, reach the flag the consumer reads.
    var nested_declarations: usize = 0;
    var text_lines = std.mem.splitScalar(u8, source, '\n');
    while (text_lines.next()) |line| {
        const trimmed = std.mem.trimStart(u8, line, " ");
        if (std.mem.eql(u8, trimmed, "local __lifter_escape_4 = false") and line.len - trimmed.len > 2) nested_declarations += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), nested_declarations);
}

/// A worker whose loop allocates `cell` on every pass (the place's origin is the pass's own write of the value
/// `next_value` returns), hands `record` a closure that captures it, and, when `read_after` holds, returns `cell`
/// after the loop. The IR gives every pass a fresh cell, so each recorded closure keeps its own pass's value.
fn capturedLoopCellModule(comptime read_after: bool) type {
    return struct {
        const proof = ir.EvidenceId.fromIndex(0);
        const entry_function = ir.FunctionId.fromIndex(0);
        const worker_function = ir.FunctionId.fromIndex(1);
        const getter_function = ir.FunctionId.fromIndex(2);
        const entry_block = ir.BlockId.fromIndex(0);
        const worker_entry = ir.BlockId.fromIndex(1);
        const loop_header = ir.BlockId.fromIndex(2);
        const loop_body = ir.BlockId.fromIndex(3);
        const loop_exit = ir.BlockId.fromIndex(4);
        const getter_block = ir.BlockId.fromIndex(5);
        const export_id = ir.InstructionId.fromIndex(0);
        const next_id = ir.InstructionId.fromIndex(1);
        const allocate_id = ir.InstructionId.fromIndex(2);
        const closure_id = ir.InstructionId.fromIndex(3);
        const record_id = ir.InstructionId.fromIndex(4);
        const get_id = ir.InstructionId.fromIndex(5);
        const read_after_id = ir.InstructionId.fromIndex(6);
        const exported_worker = ir.ValueId.fromIndex(0);
        const next_callback = ir.ValueId.fromIndex(1);
        const record_callback = ir.ValueId.fromIndex(2);
        const continue_loop = ir.ValueId.fromIndex(3);
        const iteration = ir.ValueId.fromIndex(4);
        const getter = ir.ValueId.fromIndex(5);
        const captured_value = ir.ValueId.fromIndex(6);
        const last_cell = ir.ValueId.fromIndex(7);
        const cell = ir.PlaceId.fromIndex(0);
        const captured_cell = ir.PlaceId.fromIndex(1);
        const capture = ir.CaptureId.fromIndex(0);

        const all_values = [_]ir.Value{
            .{ .id = exported_worker, .function = entry_function, .type = .function, .name_hint = "worker", .origin = .{ .instruction_result = .{ .instruction = export_id, .index = 0 } } },
            .{ .id = next_callback, .function = worker_function, .type = .function, .name_hint = "next_value", .origin = .{ .parameter = 0 } },
            .{ .id = record_callback, .function = worker_function, .type = .function, .name_hint = "record", .origin = .{ .parameter = 1 } },
            .{ .id = continue_loop, .function = worker_function, .type = .boolean, .name_hint = "continue_loop", .origin = .{ .instruction_result = .{ .instruction = next_id, .index = 0 } } },
            .{ .id = iteration, .function = worker_function, .type = .integer, .name_hint = "iteration", .origin = .{ .instruction_result = .{ .instruction = next_id, .index = 1 } } },
            .{ .id = getter, .function = worker_function, .type = .function, .name_hint = "getter", .origin = .{ .instruction_result = .{ .instruction = closure_id, .index = 0 } } },
            .{ .id = captured_value, .function = getter_function, .type = .integer, .name_hint = "captured_value", .origin = .{ .instruction_result = .{ .instruction = get_id, .index = 0 } } },
            .{ .id = last_cell, .function = worker_function, .type = .integer, .name_hint = "last_cell", .origin = .{ .instruction_result = .{ .instruction = read_after_id, .index = 0 } } },
        };
        const places = [_]ir.Place{
            .{ .id = cell, .function = worker_function, .type = .integer, .name_hint = "cell", .origin = .{ .instruction = allocate_id }, .evidence = &.{proof} },
            .{ .id = captured_cell, .function = getter_function, .type = .integer, .name_hint = "captured_cell", .origin = .{ .capture = capture }, .evidence = &.{proof} },
        };
        const captures = [_]ir.Capture{.{
            .id = capture,
            .function = getter_function,
            .kind = .{ .shared_place = captured_cell },
            .evidence = &.{proof},
        }};
        const all_instructions = [_]ir.Instruction{
            .{ .id = export_id, .block = entry_block, .operation = .{ .function_ref = worker_function }, .results = &.{exported_worker}, .effects = .pure, .evidence = &.{proof} },
            .{ .id = next_id, .block = loop_body, .operation = .{ .call = .{ .callee = next_callback, .arguments = &.{}, .result_arity = .{ .fixed = 2 } } }, .results = &.{ continue_loop, iteration }, .effects = .dynamic_call, .evidence = &.{proof} },
            .{ .id = allocate_id, .block = loop_body, .operation = .{ .place_write = .{ .place = cell, .value = iteration } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
            .{ .id = closure_id, .block = loop_body, .operation = .{ .make_closure = .{ .function = getter_function, .bindings = &.{.{ .place = cell }} } }, .results = &.{getter}, .effects = .pure, .evidence = &.{proof} },
            .{ .id = record_id, .block = loop_body, .operation = .{ .call = .{ .callee = record_callback, .arguments = &.{getter}, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call, .evidence = &.{proof} },
            .{ .id = get_id, .block = getter_block, .operation = .{ .place_read = captured_cell }, .results = &.{captured_value}, .effects = .place_read, .evidence = &.{proof} },
            .{ .id = read_after_id, .block = loop_exit, .operation = .{ .place_read = cell }, .results = &.{last_cell}, .effects = .place_read, .evidence = &.{proof} },
        };
        const blocks = [_]ir.Block{
            .{ .id = entry_block, .function = entry_function, .instructions = &.{export_id}, .terminator = .{ .return_values = &.{exported_worker} }, .evidence = &.{proof} },
            .{ .id = worker_entry, .function = worker_function, .terminator = .{ .jump = .{ .target = loop_header } }, .evidence = &.{proof} },
            .{ .id = loop_header, .function = worker_function, .terminator = .{ .jump = .{ .target = loop_body } }, .evidence = &.{proof} },
            .{ .id = loop_body, .function = worker_function, .instructions = &.{ next_id, allocate_id, closure_id, record_id }, .terminator = .{ .branch = .{
                .condition = continue_loop,
                .then_edge = .{ .target = loop_header },
                .else_edge = .{ .target = loop_exit },
            } }, .evidence = &.{proof} },
            .{ .id = loop_exit, .function = worker_function, .instructions = if (read_after) &.{read_after_id} else &.{}, .terminator = .{ .return_values = if (read_after) &.{last_cell} else &.{} }, .evidence = &.{proof} },
            .{ .id = getter_block, .function = getter_function, .instructions = &.{get_id}, .terminator = .{ .return_values = &.{captured_value} }, .evidence = &.{proof} },
        };
        const functions = [_]ir.Function{
            .{ .id = entry_function, .name_hint = "chunk", .blocks = &.{entry_block}, .entry_block = entry_block, .evidence = &.{proof} },
            .{ .id = worker_function, .name_hint = "worker", .parameters = &.{ next_callback, record_callback }, .local_places = &.{cell}, .blocks = &.{ worker_entry, loop_header, loop_body, loop_exit }, .entry_block = worker_entry, .evidence = &.{proof} },
            .{ .id = getter_function, .name_hint = "getter", .lexical_parent = worker_function, .captures = &.{capture}, .blocks = &.{getter_block}, .entry_block = getter_block, .evidence = &.{proof} },
        };
        const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:captured-loop-cell" }};
        const program: ir.Program = .{
            .program_id = "captured-loop-cell",
            .entry_function = entry_function,
            .functions = &functions,
            .blocks = &blocks,
            .instructions = all_instructions[0..if (read_after) all_instructions.len else all_instructions.len - 1],
            .values = all_values[0..if (read_after) all_values.len else all_values.len - 1],
            .places = &places,
            .captures = &captures,
            .evidence = &evidence,
        };
    };
}

test "a closure-captured loop cell read after its loop keeps one cell per pass" {
    const module = capturedLoopCellModule(true);
    const source = try emitAlloc(std.testing.allocator, &module.program);
    defer std.testing.allocator.free(source);
    errdefer std.debug.print("{s}\n", .{source});
    // Each pass's write declares its cell or fills a fresh box; an assignment to one local declared before the loop
    // would hand every recorded closure the last pass's cell.
    var lines = std.mem.splitScalar(u8, source, '\n');
    while (lines.next()) |line| {
        try std.testing.expect(!std.mem.eql(u8, std.mem.trimStart(u8, line, " "), "cell = iteration"));
    }
    try std.testing.expect(std.mem.indexOf(u8, source, "cell = { iteration }") != null);
}

test "a closure-captured loop cell used only inside its loop is declared at its write" {
    const module = capturedLoopCellModule(false);
    const source = try emitAlloc(std.testing.allocator, &module.program);
    defer std.testing.allocator.free(source);
    errdefer std.debug.print("{s}\n", .{source});
    try std.testing.expect(std.mem.indexOf(u8, source, "local __lifter_pc") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local cell = iteration\n") != null);
}

/// A worker whose loop allocates `cell` on every pass (the place's origin is the pass's own write of the value
/// `next_value` returns) and makes the closure that captures it only after that loop, hands the closure to `record`
/// and returns `cell` after its last loop. With `nested` false the allocating loop is the worker's only loop, so the
/// closure is made once, after the last pass. With `nested` true the allocating loop is the inner loop of an outer
/// loop that runs while `record` returns true, so a closure is made in every outer pass, each over that pass's cell.
fn capturedCellAfterLoopModule(comptime nested: bool) type {
    return struct {
        const proof = ir.EvidenceId.fromIndex(0);
        const entry_function = ir.FunctionId.fromIndex(0);
        const worker_function = ir.FunctionId.fromIndex(1);
        const getter_function = ir.FunctionId.fromIndex(2);
        const entry_block = ir.BlockId.fromIndex(0);
        const worker_entry = ir.BlockId.fromIndex(1);
        const loop_header = ir.BlockId.fromIndex(2);
        const loop_body = ir.BlockId.fromIndex(3);
        const after_loop = ir.BlockId.fromIndex(4);
        const worker_exit = ir.BlockId.fromIndex(5);
        const getter_block = ir.BlockId.fromIndex(6);
        const export_id = ir.InstructionId.fromIndex(0);
        const next_id = ir.InstructionId.fromIndex(1);
        const allocate_id = ir.InstructionId.fromIndex(2);
        const closure_id = ir.InstructionId.fromIndex(3);
        const record_id = ir.InstructionId.fromIndex(4);
        const get_id = ir.InstructionId.fromIndex(5);
        const read_after_id = ir.InstructionId.fromIndex(6);
        const exported_worker = ir.ValueId.fromIndex(0);
        const next_callback = ir.ValueId.fromIndex(1);
        const record_callback = ir.ValueId.fromIndex(2);
        const continue_loop = ir.ValueId.fromIndex(3);
        const iteration = ir.ValueId.fromIndex(4);
        const getter = ir.ValueId.fromIndex(5);
        const continue_outer = ir.ValueId.fromIndex(6);
        const captured_value = ir.ValueId.fromIndex(7);
        const last_cell = ir.ValueId.fromIndex(8);
        const cell = ir.PlaceId.fromIndex(0);
        const captured_cell = ir.PlaceId.fromIndex(1);
        const capture = ir.CaptureId.fromIndex(0);

        const values = [_]ir.Value{
            .{ .id = exported_worker, .function = entry_function, .type = .function, .name_hint = "worker", .origin = .{ .instruction_result = .{ .instruction = export_id, .index = 0 } } },
            .{ .id = next_callback, .function = worker_function, .type = .function, .name_hint = "next_value", .origin = .{ .parameter = 0 } },
            .{ .id = record_callback, .function = worker_function, .type = .function, .name_hint = "record", .origin = .{ .parameter = 1 } },
            .{ .id = continue_loop, .function = worker_function, .type = .boolean, .name_hint = "continue_loop", .origin = .{ .instruction_result = .{ .instruction = next_id, .index = 0 } } },
            .{ .id = iteration, .function = worker_function, .type = .integer, .name_hint = "iteration", .origin = .{ .instruction_result = .{ .instruction = next_id, .index = 1 } } },
            .{ .id = getter, .function = worker_function, .type = .function, .name_hint = "getter", .origin = .{ .instruction_result = .{ .instruction = closure_id, .index = 0 } } },
            .{ .id = continue_outer, .function = worker_function, .type = .boolean, .name_hint = "continue_outer", .origin = .{ .instruction_result = .{ .instruction = record_id, .index = 0 } } },
            .{ .id = captured_value, .function = getter_function, .type = .integer, .name_hint = "captured_value", .origin = .{ .instruction_result = .{ .instruction = get_id, .index = 0 } } },
            .{ .id = last_cell, .function = worker_function, .type = .integer, .name_hint = "last_cell", .origin = .{ .instruction_result = .{ .instruction = read_after_id, .index = 0 } } },
        };
        const places = [_]ir.Place{
            .{ .id = cell, .function = worker_function, .type = .integer, .name_hint = "cell", .origin = .{ .instruction = allocate_id }, .evidence = &.{proof} },
            .{ .id = captured_cell, .function = getter_function, .type = .integer, .name_hint = "captured_cell", .origin = .{ .capture = capture }, .evidence = &.{proof} },
        };
        const captures = [_]ir.Capture{.{
            .id = capture,
            .function = getter_function,
            .kind = .{ .shared_place = captured_cell },
            .evidence = &.{proof},
        }};
        const instructions = [_]ir.Instruction{
            .{ .id = export_id, .block = entry_block, .operation = .{ .function_ref = worker_function }, .results = &.{exported_worker}, .effects = .pure, .evidence = &.{proof} },
            .{ .id = next_id, .block = loop_body, .operation = .{ .call = .{ .callee = next_callback, .arguments = &.{}, .result_arity = .{ .fixed = 2 } } }, .results = &.{ continue_loop, iteration }, .effects = .dynamic_call, .evidence = &.{proof} },
            .{ .id = allocate_id, .block = loop_body, .operation = .{ .place_write = .{ .place = cell, .value = iteration } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
            .{ .id = closure_id, .block = after_loop, .operation = .{ .make_closure = .{ .function = getter_function, .bindings = &.{.{ .place = cell }} } }, .results = &.{getter}, .effects = .pure, .evidence = &.{proof} },
            .{ .id = record_id, .block = after_loop, .operation = .{ .call = .{ .callee = record_callback, .arguments = &.{getter}, .result_arity = .{ .fixed = 1 } } }, .results = &.{continue_outer}, .effects = .dynamic_call, .evidence = &.{proof} },
            .{ .id = get_id, .block = getter_block, .operation = .{ .place_read = captured_cell }, .results = &.{captured_value}, .effects = .place_read, .evidence = &.{proof} },
            .{ .id = read_after_id, .block = worker_exit, .operation = .{ .place_read = cell }, .results = &.{last_cell}, .effects = .place_read, .evidence = &.{proof} },
        };
        // The allocating loop: the body loops to itself as the inner loop of an outer loop headed by `loop_header`,
        // or back to `loop_header` as the worker's only loop.
        const loop_back = if (nested) loop_body else loop_header;
        const after_terminator: ir.Terminator = if (nested) .{ .branch = .{
            .condition = continue_outer,
            .then_edge = .{ .target = loop_header },
            .else_edge = .{ .target = worker_exit },
        } } else .{ .jump = .{ .target = worker_exit } };
        const blocks = [_]ir.Block{
            .{ .id = entry_block, .function = entry_function, .instructions = &.{export_id}, .terminator = .{ .return_values = &.{exported_worker} }, .evidence = &.{proof} },
            .{ .id = worker_entry, .function = worker_function, .terminator = .{ .jump = .{ .target = loop_header } }, .evidence = &.{proof} },
            .{ .id = loop_header, .function = worker_function, .terminator = .{ .jump = .{ .target = loop_body } }, .evidence = &.{proof} },
            .{ .id = loop_body, .function = worker_function, .instructions = &.{ next_id, allocate_id }, .terminator = .{ .branch = .{
                .condition = continue_loop,
                .then_edge = .{ .target = loop_back },
                .else_edge = .{ .target = after_loop },
            } }, .evidence = &.{proof} },
            .{ .id = after_loop, .function = worker_function, .instructions = &.{ closure_id, record_id }, .terminator = after_terminator, .evidence = &.{proof} },
            .{ .id = worker_exit, .function = worker_function, .instructions = &.{read_after_id}, .terminator = .{ .return_values = &.{last_cell} }, .evidence = &.{proof} },
            .{ .id = getter_block, .function = getter_function, .instructions = &.{get_id}, .terminator = .{ .return_values = &.{captured_value} }, .evidence = &.{proof} },
        };
        const functions = [_]ir.Function{
            .{ .id = entry_function, .name_hint = "chunk", .blocks = &.{entry_block}, .entry_block = entry_block, .evidence = &.{proof} },
            .{ .id = worker_function, .name_hint = "worker", .parameters = &.{ next_callback, record_callback }, .local_places = &.{cell}, .blocks = &.{ worker_entry, loop_header, loop_body, after_loop, worker_exit }, .entry_block = worker_entry, .evidence = &.{proof} },
            .{ .id = getter_function, .name_hint = "getter", .lexical_parent = worker_function, .captures = &.{capture}, .blocks = &.{getter_block}, .entry_block = getter_block, .evidence = &.{proof} },
        };
        const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:captured-cell-after-loop" }};
        const program: ir.Program = .{
            .program_id = "captured-cell-after-loop",
            .entry_function = entry_function,
            .functions = &functions,
            .blocks = &blocks,
            .instructions = &instructions,
            .values = &values,
            .places = &places,
            .captures = &captures,
            .evidence = &evidence,
        };
    };
}

test "a loop cell whose closure is made only after its loop keeps the structured layout" {
    const module = capturedCellAfterLoopModule(false);
    const source = try emitAlloc(std.testing.allocator, &module.program);
    defer std.testing.allocator.free(source);
    errdefer std.debug.print("{s}\n", .{source});
    // The closure is made once, after the last pass, so the one local the loop assigns holds the cell it captures.
    try std.testing.expect(std.mem.indexOf(u8, source, "local __lifter_pc") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "cell = { iteration }") == null);
}

test "a loop cell captured after an inner loop inside an outer loop keeps one cell per pass" {
    const module = capturedCellAfterLoopModule(true);
    const source = try emitAlloc(std.testing.allocator, &module.program);
    defer std.testing.allocator.free(source);
    errdefer std.debug.print("{s}\n", .{source});
    // A closure is made in every outer pass, after the inner loop; an assignment to one local declared before the
    // outer loop would hand every recorded closure the last outer pass's cell.
    var lines = std.mem.splitScalar(u8, source, '\n');
    while (lines.next()) |line| {
        try std.testing.expect(!std.mem.eql(u8, std.mem.trimStart(u8, line, " "), "cell = iteration"));
    }
    try std.testing.expect(std.mem.indexOf(u8, source, "cell = { iteration }") != null);
}

/// A function that writes `state` and returns it, and a block no edge reaches that writes `unused` and returns it:
/// the shape `resolve-ir` leaves when code follows a loop that only `return` leaves. Both places are in the
/// function's `local_places`; the name plan names the places that the instructions of reachable blocks use, so
/// `unused` has no name.
const unreachable_block_place = struct {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const unreached = ir.BlockId.fromIndex(1);
    const initial_id = ir.InstructionId.fromIndex(0);
    const write_id = ir.InstructionId.fromIndex(1);
    const read_id = ir.InstructionId.fromIndex(2);
    const unused_initial_id = ir.InstructionId.fromIndex(3);
    const unused_write_id = ir.InstructionId.fromIndex(4);
    const unused_read_id = ir.InstructionId.fromIndex(5);
    const initial = ir.ValueId.fromIndex(0);
    const result = ir.ValueId.fromIndex(1);
    const unused_initial = ir.ValueId.fromIndex(2);
    const unused_result = ir.ValueId.fromIndex(3);
    const state = ir.PlaceId.fromIndex(0);
    const unused = ir.PlaceId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = initial, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = initial_id, .index = 0 } } },
        .{ .id = result, .function = function_id, .type = .integer, .name_hint = "result", .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } } },
        .{ .id = unused_initial, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = unused_initial_id, .index = 0 } } },
        .{ .id = unused_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = unused_read_id, .index = 0 } } },
    };
    const places = [_]ir.Place{
        .{ .id = state, .function = function_id, .type = .integer, .name_hint = "state", .origin = .{ .local = 0 }, .evidence = &.{proof} },
        .{ .id = unused, .function = function_id, .type = .integer, .name_hint = "unused", .origin = .{ .local = 1 }, .evidence = &.{proof} },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = initial_id, .block = entry, .operation = .{ .constant = .{ .integer = "7" } }, .results = &.{initial}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = write_id, .block = entry, .operation = .{ .place_write = .{ .place = state, .value = initial } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
        .{ .id = read_id, .block = entry, .operation = .{ .place_read = state }, .results = &.{result}, .effects = .place_read, .evidence = &.{proof} },
        .{ .id = unused_initial_id, .block = unreached, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{unused_initial}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = unused_write_id, .block = unreached, .operation = .{ .place_write = .{ .place = unused, .value = unused_initial } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
        .{ .id = unused_read_id, .block = unreached, .operation = .{ .place_read = unused }, .results = &.{unused_result}, .effects = .place_read, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{ initial_id, write_id, read_id }, .terminator = .{ .return_values = &.{result} }, .evidence = &.{proof} },
        .{ .id = unreached, .function = function_id, .instructions = &.{ unused_initial_id, unused_write_id, unused_read_id }, .terminator = .{ .return_values = &.{unused_result} }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &.{ entry, unreached }, .entry_block = entry, .local_places = &.{ state, unused }, .evidence = &.{proof} }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:unreachable-block-place" }};
    const program: ir.Program = .{
        .program_id = "unreachable-block-place",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
        .evidence = &evidence,
    };
};

test "the dispatcher layout declares no place that only an unreachable block uses" {
    const source = try lifter.emit_luau.emitAllocForTargetWithOptions(
        std.testing.allocator,
        &unreachable_block_place.program,
        .standard_luau,
        .{ .force_dispatcher = true },
    );
    defer std.testing.allocator.free(source);
    errdefer std.debug.print("{s}\n", .{source});
    try std.testing.expect(std.mem.indexOf(u8, source, "local __lifter_pc") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "state") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "unused") == null);
}

/// A worker of three callbacks whose `repeat` loop takes the pass's value from `next_value`, hands `record` a closure
/// that returns it and the value itself (two reads, so the value is a local declared at its instruction), and holds
/// `filler` pure constants nothing reads (each a candidate value of the value-storage count; the dead-code plan drops
/// them from the text); the latch leaves the loop when `keep_going` returns true. Past 120 candidate values the
/// standard target keeps the worker's values in its storage table.
fn storageLoopClosureModule(comptime filler: usize) type {
    return struct {
        const proof = ir.EvidenceId.fromIndex(0);
        const chunk_function = ir.FunctionId.fromIndex(0);
        const worker_function = ir.FunctionId.fromIndex(1);
        const getter_function = ir.FunctionId.fromIndex(2);
        const capture = ir.CaptureId.fromIndex(0);
        const block = ir.BlockId.fromIndex;
        const instruction = ir.InstructionId.fromIndex;
        const value = ir.ValueId.fromIndex;
        // Instructions: 0 the export, 1 next_value(), 2 the closure, 3 record(getter, iteration), 4 .. 3 + filler the
        // constants, keep_going() in the latch. Values: 0 the export, 1-3 the parameters, 4 iteration, 5 getter, 6 keep,
        // 7 the getter's captured value, 8 .. 7 + filler the constants.
        const keep_id = instruction(4 + filler);

        const values = list: {
            @setEvalBranchQuota(20_000);
            var all: [8 + filler]ir.Value = undefined;
            all[0] = .{ .id = value(0), .function = chunk_function, .type = .function, .name_hint = "worker", .origin = .{ .instruction_result = .{ .instruction = instruction(0), .index = 0 } } };
            all[1] = .{ .id = value(1), .function = worker_function, .type = .function, .name_hint = "next_value", .origin = .{ .parameter = 0 } };
            all[2] = .{ .id = value(2), .function = worker_function, .type = .function, .name_hint = "record", .origin = .{ .parameter = 1 } };
            all[3] = .{ .id = value(3), .function = worker_function, .type = .function, .name_hint = "keep_going", .origin = .{ .parameter = 2 } };
            all[4] = .{ .id = value(4), .function = worker_function, .type = .integer, .name_hint = "iteration", .origin = .{ .instruction_result = .{ .instruction = instruction(1), .index = 0 } } };
            all[5] = .{ .id = value(5), .function = worker_function, .type = .function, .name_hint = "getter", .origin = .{ .instruction_result = .{ .instruction = instruction(2), .index = 0 } } };
            all[6] = .{ .id = value(6), .function = worker_function, .type = .boolean, .name_hint = "keep", .origin = .{ .instruction_result = .{ .instruction = keep_id, .index = 0 } } };
            all[7] = .{ .id = value(7), .function = getter_function, .type = .integer, .name_hint = "captured_iteration", .origin = .{ .capture = capture } };
            for (0..filler) |k| all[8 + k] = .{ .id = value(8 + k), .function = worker_function, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = instruction(4 + k), .index = 0 } } };
            break :list all;
        };
        const instructions = list: {
            @setEvalBranchQuota(20_000);
            var all: [5 + filler]ir.Instruction = undefined;
            all[0] = .{ .id = instruction(0), .block = block(0), .operation = .{ .function_ref = worker_function }, .results = &.{value(0)}, .effects = .pure, .evidence = &.{proof} };
            all[1] = .{ .id = instruction(1), .block = block(2), .operation = .{ .call = .{ .callee = value(1), .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{value(4)}, .effects = .dynamic_call, .evidence = &.{proof} };
            all[2] = .{ .id = instruction(2), .block = block(2), .operation = .{ .make_closure = .{ .function = getter_function, .bindings = &.{.{ .value = value(4) }} } }, .results = &.{value(5)}, .effects = .pure, .evidence = &.{proof} };
            all[3] = .{ .id = instruction(3), .block = block(2), .operation = .{ .call = .{ .callee = value(2), .arguments = &.{ value(5), value(4) }, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call, .evidence = &.{proof} };
            for (0..filler) |k| all[4 + k] = .{ .id = instruction(4 + k), .block = block(2), .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{value(8 + k)}, .effects = .pure, .evidence = &.{proof} };
            all[4 + filler] = .{ .id = keep_id, .block = block(3), .operation = .{ .call = .{ .callee = value(3), .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{value(6)}, .effects = .dynamic_call, .evidence = &.{proof} };
            break :list all;
        };
        const body_instructions = list: {
            var ids: [3 + filler]ir.InstructionId = undefined;
            for (&ids, 0..) |*id, k| id.* = instruction(1 + k);
            break :list ids;
        };
        const blocks = [_]ir.Block{
            .{ .id = block(0), .function = chunk_function, .instructions = &.{instruction(0)}, .terminator = .{ .return_values = &.{value(0)} }, .evidence = &.{proof} },
            .{ .id = block(1), .function = worker_function, .terminator = .{ .jump = .{ .target = block(2) } }, .evidence = &.{proof} },
            .{ .id = block(2), .function = worker_function, .instructions = &body_instructions, .terminator = .{ .jump = .{ .target = block(3) } }, .evidence = &.{proof} },
            .{ .id = block(3), .function = worker_function, .instructions = &.{keep_id}, .terminator = .{ .branch = .{ .condition = value(6), .then_edge = .{ .target = block(4) }, .else_edge = .{ .target = block(2) } } }, .evidence = &.{proof} },
            .{ .id = block(4), .function = worker_function, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
            .{ .id = block(5), .function = getter_function, .terminator = .{ .return_values = &.{value(7)} }, .evidence = &.{proof} },
        };
        const functions = [_]ir.Function{
            .{ .id = chunk_function, .name_hint = "chunk", .blocks = &.{block(0)}, .entry_block = block(0), .evidence = &.{proof} },
            .{ .id = worker_function, .name_hint = "worker", .parameters = &.{ value(1), value(2), value(3) }, .blocks = &.{ block(1), block(2), block(3), block(4) }, .entry_block = block(1), .evidence = &.{proof} },
            .{ .id = getter_function, .name_hint = "getter", .lexical_parent = worker_function, .captures = &.{capture}, .blocks = &.{block(5)}, .entry_block = block(5), .evidence = &.{proof} },
        };
        const captures = [_]ir.Capture{.{ .id = capture, .function = getter_function, .kind = .{ .immutable_value = value(7) }, .evidence = &.{proof} }};
        const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:storage-loop-closure" }};
        const program: ir.Program = .{
            .program_id = "storage-loop-closure",
            .entry_function = chunk_function,
            .functions = &functions,
            .blocks = &blocks,
            .instructions = &instructions,
            .values = &values,
            .captures = &captures,
            .evidence = &evidence,
        };
    };
}

test "a closure made in a pass of a value-storage loop reads that pass's value, not its storage slot" {
    const module = storageLoopClosureModule(120);
    const source = try emitAlloc(std.testing.allocator, &module.program);
    defer std.testing.allocator.free(source);
    errdefer std.debug.print("{s}\n", .{source});
    // Over 120 candidate values the worker's values live in its storage table; every pass writes the slot of
    // `iteration` again, so a closure that read that slot when it is called would return the last pass's value.
    try std.testing.expect(std.mem.indexOf(u8, source, "local __lifter_value_storage = {}") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local __lifter_pc") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "return __lifter_value_storage[") == null);
}

test "a closure made in a pass of a loop without value storage reads the pass's local" {
    const module = storageLoopClosureModule(8);
    const source = try emitAlloc(std.testing.allocator, &module.program);
    defer std.testing.allocator.free(source);
    errdefer std.debug.print("{s}\n", .{source});
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_value_storage") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local __lifter_pc") == null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local iteration = next_value()\n") != null);
}

/// A worker of two callbacks that takes `scale` from `make_scale`, makes `inner` (a function that returns `scale`) and
/// hands `record` both (two reads, so `scale` is a local declared at its instruction). The worker holds
/// `outer_filler` and `inner` holds `inner_filler` pure constants nothing reads (candidate values of the
/// value-storage count, dropped from the text): past 120 each function gets a storage table.
fn nestedStorageModule(comptime outer_filler: usize, comptime inner_filler: usize) type {
    return struct {
        const proof = ir.EvidenceId.fromIndex(0);
        const chunk_function = ir.FunctionId.fromIndex(0);
        const worker_function = ir.FunctionId.fromIndex(1);
        const inner_function = ir.FunctionId.fromIndex(2);
        const capture = ir.CaptureId.fromIndex(0);
        const block = ir.BlockId.fromIndex;
        const instruction = ir.InstructionId.fromIndex;
        const value = ir.ValueId.fromIndex;
        // Instructions: 0 the export, 1 make_scale(), 2 the closure, 3 record(inner, scale), 4 .. 3 + outer_filler the
        // worker's constants, then inner_filler constants in `inner`. Values: 0 the export, 1-2 the parameters,
        // 3 scale, 4 inner, 5 inner's captured scale, then the worker's and inner's constants.
        const values = list: {
            @setEvalBranchQuota(40_000);
            var all: [6 + outer_filler + inner_filler]ir.Value = undefined;
            all[0] = .{ .id = value(0), .function = chunk_function, .type = .function, .name_hint = "worker", .origin = .{ .instruction_result = .{ .instruction = instruction(0), .index = 0 } } };
            all[1] = .{ .id = value(1), .function = worker_function, .type = .function, .name_hint = "make_scale", .origin = .{ .parameter = 0 } };
            all[2] = .{ .id = value(2), .function = worker_function, .type = .function, .name_hint = "record", .origin = .{ .parameter = 1 } };
            all[3] = .{ .id = value(3), .function = worker_function, .type = .integer, .name_hint = "scale", .origin = .{ .instruction_result = .{ .instruction = instruction(1), .index = 0 } } };
            all[4] = .{ .id = value(4), .function = worker_function, .type = .function, .name_hint = "inner", .origin = .{ .instruction_result = .{ .instruction = instruction(2), .index = 0 } } };
            all[5] = .{ .id = value(5), .function = inner_function, .type = .integer, .name_hint = "captured_scale", .origin = .{ .capture = capture } };
            for (0..outer_filler) |k| all[6 + k] = .{ .id = value(6 + k), .function = worker_function, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = instruction(4 + k), .index = 0 } } };
            for (0..inner_filler) |k| all[6 + outer_filler + k] = .{ .id = value(6 + outer_filler + k), .function = inner_function, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = instruction(4 + outer_filler + k), .index = 0 } } };
            break :list all;
        };
        const instructions = list: {
            @setEvalBranchQuota(40_000);
            var all: [4 + outer_filler + inner_filler]ir.Instruction = undefined;
            all[0] = .{ .id = instruction(0), .block = block(0), .operation = .{ .function_ref = worker_function }, .results = &.{value(0)}, .effects = .pure, .evidence = &.{proof} };
            all[1] = .{ .id = instruction(1), .block = block(1), .operation = .{ .call = .{ .callee = value(1), .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{value(3)}, .effects = .dynamic_call, .evidence = &.{proof} };
            all[2] = .{ .id = instruction(2), .block = block(1), .operation = .{ .make_closure = .{ .function = inner_function, .bindings = &.{.{ .value = value(3) }} } }, .results = &.{value(4)}, .effects = .pure, .evidence = &.{proof} };
            all[3] = .{ .id = instruction(3), .block = block(1), .operation = .{ .call = .{ .callee = value(2), .arguments = &.{ value(4), value(3) }, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call, .evidence = &.{proof} };
            for (0..outer_filler) |k| all[4 + k] = .{ .id = instruction(4 + k), .block = block(1), .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{value(6 + k)}, .effects = .pure, .evidence = &.{proof} };
            for (0..inner_filler) |k| all[4 + outer_filler + k] = .{ .id = instruction(4 + outer_filler + k), .block = block(2), .operation = .{ .constant = .{ .integer = "2" } }, .results = &.{value(6 + outer_filler + k)}, .effects = .pure, .evidence = &.{proof} };
            break :list all;
        };
        const worker_instructions = list: {
            var ids: [3 + outer_filler]ir.InstructionId = undefined;
            for (&ids, 0..) |*id, k| id.* = instruction(1 + k);
            break :list ids;
        };
        const inner_instructions = list: {
            var ids: [inner_filler]ir.InstructionId = undefined;
            for (&ids, 0..) |*id, k| id.* = instruction(4 + outer_filler + k);
            break :list ids;
        };
        const blocks = [_]ir.Block{
            .{ .id = block(0), .function = chunk_function, .instructions = &.{instruction(0)}, .terminator = .{ .return_values = &.{value(0)} }, .evidence = &.{proof} },
            .{ .id = block(1), .function = worker_function, .instructions = &worker_instructions, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
            .{ .id = block(2), .function = inner_function, .instructions = &inner_instructions, .terminator = .{ .return_values = &.{value(5)} }, .evidence = &.{proof} },
        };
        const functions = [_]ir.Function{
            .{ .id = chunk_function, .name_hint = "chunk", .blocks = &.{block(0)}, .entry_block = block(0), .evidence = &.{proof} },
            .{ .id = worker_function, .name_hint = "worker", .parameters = &.{ value(1), value(2) }, .blocks = &.{block(1)}, .entry_block = block(1), .evidence = &.{proof} },
            .{ .id = inner_function, .name_hint = "inner", .lexical_parent = worker_function, .captures = &.{capture}, .blocks = &.{block(2)}, .entry_block = block(2), .evidence = &.{proof} },
        };
        const captures = [_]ir.Capture{.{ .id = capture, .function = inner_function, .kind = .{ .immutable_value = value(5) }, .evidence = &.{proof} }};
        const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:nested-storage" }};
        const program: ir.Program = .{
            .program_id = "nested-storage",
            .entry_function = chunk_function,
            .functions = &functions,
            .blocks = &blocks,
            .instructions = &instructions,
            .values = &values,
            .captures = &captures,
            .evidence = &evidence,
        };
    };
}

test "a function nested in a value-storage function reads a captured value through no table it declares itself" {
    const module = nestedStorageModule(121, 121);
    const source = try emitAlloc(std.testing.allocator, &module.program);
    defer std.testing.allocator.free(source);
    errdefer std.debug.print("{s}\n", .{source});
    // Both functions hold value storage, so each declares a table. Inside `inner`, `scale` (value 3) must not be read
    // as slot 3 of the table `inner` declared itself: that table is empty, and the read would be nil. The worker's own
    // reads of its slot 3 after `inner` are right, so only `inner`'s body is searched: from its header to the first
    // `end` at the header line's indentation.
    const outer_declaration = std.mem.indexOf(u8, source, "local __lifter_value_storage") orelse return error.TestUnexpectedResult;
    const inner_header = std.mem.indexOfPos(u8, source, outer_declaration, "function()\n") orelse return error.TestUnexpectedResult;
    const header_line = if (std.mem.lastIndexOfScalar(u8, source[0..inner_header], '\n')) |newline| newline + 1 else 0;
    var indent_len: usize = 0;
    while (source[header_line + indent_len] == ' ') indent_len += 1;
    const closing = try std.fmt.allocPrint(std.testing.allocator, "\n{s}end", .{source[header_line .. header_line + indent_len]});
    defer std.testing.allocator.free(closing);
    const inner_end = std.mem.indexOfPos(u8, source, inner_header, closing) orelse return error.TestUnexpectedResult;
    const inner_body = source[inner_header..inner_end];
    const inner_declaration = std.mem.indexOf(u8, inner_body, "local __lifter_value_storage") orelse return error.TestUnexpectedResult;
    const name_start = inner_declaration + "local ".len;
    const name_end = std.mem.indexOfPos(u8, inner_body, name_start, " = {}") orelse return error.TestUnexpectedResult;
    const slot = try std.fmt.allocPrint(std.testing.allocator, "{s}[3]", .{inner_body[name_start..name_end]});
    defer std.testing.allocator.free(slot);
    try std.testing.expect(std.mem.indexOfPos(u8, inner_body, name_end, slot) == null);
}

test "a function nested in a value-storage function without storage of its own declares no table" {
    const module = nestedStorageModule(121, 8);
    const source = try emitAlloc(std.testing.allocator, &module.program);
    defer std.testing.allocator.free(source);
    errdefer std.debug.print("{s}\n", .{source});
    const outer_declaration = std.mem.indexOf(u8, source, "local __lifter_value_storage") orelse return error.TestUnexpectedResult;
    try std.testing.expect(std.mem.indexOfPos(u8, source, outer_declaration + 1, "local __lifter_value_storage") == null);
}

/// Where a closure's creating statement writes the closure, in `creatingStatementModule`.
const CreatingStatementForm = enum { value, place, table, key };

/// A worker `worker(seed, t, k)` that calls `seed` once and makes a closure that returns the call's result. The result
/// has one use, the closure's capture, so `emitClosure` writes it as a copy, `local <captured> = seed()`, inside the
/// `do` block that also holds the statement creating the closure; that statement's destination carries the result's
/// name hint: `.value` the closure's own result, called right after (`local f = seed()`, `local f = function() return
/// f end`, `return f()`); `.place` a local the worker writes and reads (`local x = function() return x end`, `return
/// x()`); `.table` the parameter `t` as the store's table (`t.get = function() return t end`, the result hinted `t`);
/// `.key` the parameter `k` as the store's key (`t[k] = function() return k end`, the result hinted `k`).
fn creatingStatementModule(comptime form: CreatingStatementForm) type {
    return struct {
        const proof = ir.EvidenceId.fromIndex(0);
        const chunk_function = ir.FunctionId.fromIndex(0);
        const worker_function = ir.FunctionId.fromIndex(1);
        const getter_function = ir.FunctionId.fromIndex(2);
        const capture = ir.CaptureId.fromIndex(0);
        const local_place = ir.PlaceId.fromIndex(0);
        const block = ir.BlockId.fromIndex;
        const instruction = ir.InstructionId.fromIndex;
        const value = ir.ValueId.fromIndex;
        const hint = switch (form) {
            .value => "f",
            .place => "x",
            .table => "t",
            .key => "k",
        };
        // Values: 0 the export, 1-3 the parameters `seed`, `t` and `k`, 4 the getter's captured value, 5 `seed()`,
        // 6 the closure, then `.value` 7 the closure's call, `.place` 7 the local's read and 8 its call, `.table` 7
        // the key "get". Instructions: 0 the export, 1 `seed()`, 2 the closure, then the form's.
        const head_values = [_]ir.Value{
            .{ .id = value(0), .function = chunk_function, .type = .function, .name_hint = "worker", .origin = .{ .instruction_result = .{ .instruction = instruction(0), .index = 0 } } },
            .{ .id = value(1), .function = worker_function, .type = .function, .name_hint = "seed", .origin = .{ .parameter = 0 } },
            .{ .id = value(2), .function = worker_function, .type = .dynamic, .name_hint = "t", .origin = .{ .parameter = 1 } },
            .{ .id = value(3), .function = worker_function, .type = .dynamic, .name_hint = "k", .origin = .{ .parameter = 2 } },
            .{ .id = value(4), .function = getter_function, .type = .dynamic, .name_hint = hint, .origin = .{ .capture = capture } },
            .{ .id = value(5), .function = worker_function, .type = .dynamic, .name_hint = hint, .origin = .{ .instruction_result = .{ .instruction = instruction(1), .index = 0 } } },
            .{ .id = value(6), .function = worker_function, .type = .function, .name_hint = hint, .origin = .{ .instruction_result = .{ .instruction = instruction(2), .index = 0 } } },
        };
        const values: []const ir.Value = switch (form) {
            .value => &(head_values ++ [_]ir.Value{
                .{ .id = value(7), .function = worker_function, .type = .dynamic, .name_hint = "result", .origin = .{ .instruction_result = .{ .instruction = instruction(3), .index = 0 } } },
            }),
            .place => &(head_values ++ [_]ir.Value{
                .{ .id = value(7), .function = worker_function, .type = .function, .name_hint = "x", .origin = .{ .instruction_result = .{ .instruction = instruction(4), .index = 0 } } },
                .{ .id = value(8), .function = worker_function, .type = .dynamic, .name_hint = "result", .origin = .{ .instruction_result = .{ .instruction = instruction(5), .index = 0 } } },
            }),
            .table => &(head_values ++ [_]ir.Value{
                .{ .id = value(7), .function = worker_function, .type = .string, .name_hint = "field_key", .origin = .{ .instruction_result = .{ .instruction = instruction(3), .index = 0 } } },
            }),
            .key => &head_values,
        };
        const head_instructions = [_]ir.Instruction{
            .{ .id = instruction(0), .block = block(0), .operation = .{ .function_ref = worker_function }, .results = &.{value(0)}, .effects = .pure, .evidence = &.{proof} },
            .{ .id = instruction(1), .block = block(1), .operation = .{ .call = .{ .callee = value(1), .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{value(5)}, .effects = .dynamic_call, .evidence = &.{proof} },
            .{ .id = instruction(2), .block = block(1), .operation = .{ .make_closure = .{ .function = getter_function, .bindings = &.{.{ .value = value(5) }} } }, .results = &.{value(6)}, .effects = .pure, .evidence = &.{proof} },
        };
        const instructions: []const ir.Instruction = switch (form) {
            .value => &(head_instructions ++ [_]ir.Instruction{
                .{ .id = instruction(3), .block = block(1), .operation = .{ .call = .{ .callee = value(6), .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{value(7)}, .effects = .dynamic_call, .evidence = &.{proof} },
            }),
            .place => &(head_instructions ++ [_]ir.Instruction{
                .{ .id = instruction(3), .block = block(1), .operation = .{ .place_write = .{ .place = local_place, .value = value(6) } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
                .{ .id = instruction(4), .block = block(1), .operation = .{ .place_read = local_place }, .results = &.{value(7)}, .effects = .place_read, .evidence = &.{proof} },
                .{ .id = instruction(5), .block = block(1), .operation = .{ .call = .{ .callee = value(7), .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{value(8)}, .effects = .dynamic_call, .evidence = &.{proof} },
            }),
            .table => &(head_instructions ++ [_]ir.Instruction{
                .{ .id = instruction(3), .block = block(1), .operation = .{ .constant = .{ .string = "get" } }, .results = &.{value(7)}, .effects = .pure, .evidence = &.{proof} },
                .{ .id = instruction(4), .block = block(1), .operation = .{ .table_set = .{ .table = value(2), .key = value(7), .value = value(6) } }, .results = &.{}, .effects = .semantic_table_write, .evidence = &.{proof} },
            }),
            .key => &(head_instructions ++ [_]ir.Instruction{
                .{ .id = instruction(3), .block = block(1), .operation = .{ .table_set = .{ .table = value(2), .key = value(3), .value = value(6) } }, .results = &.{}, .effects = .semantic_table_write, .evidence = &.{proof} },
            }),
        };
        const worker_instructions: []const ir.InstructionId = switch (form) {
            .value => &.{ instruction(1), instruction(2), instruction(3) },
            .place => &.{ instruction(1), instruction(2), instruction(3), instruction(4), instruction(5) },
            .table => &.{ instruction(1), instruction(2), instruction(3), instruction(4) },
            .key => &.{ instruction(1), instruction(2), instruction(3) },
        };
        const worker_returns: []const ir.ValueId = switch (form) {
            .value => &.{value(7)},
            .place => &.{value(8)},
            .table, .key => &.{},
        };
        const blocks = [_]ir.Block{
            .{ .id = block(0), .function = chunk_function, .instructions = &.{instruction(0)}, .terminator = .{ .return_values = &.{value(0)} }, .evidence = &.{proof} },
            .{ .id = block(1), .function = worker_function, .instructions = worker_instructions, .terminator = .{ .return_values = worker_returns }, .evidence = &.{proof} },
            .{ .id = block(2), .function = getter_function, .terminator = .{ .return_values = &.{value(4)} }, .evidence = &.{proof} },
        };
        const places: []const ir.Place = switch (form) {
            .place => &.{.{ .id = local_place, .function = worker_function, .type = .function, .name_hint = "x", .origin = .{ .local = 0 }, .evidence = &.{proof} }},
            .value, .table, .key => &.{},
        };
        const functions = [_]ir.Function{
            .{ .id = chunk_function, .name_hint = "chunk", .blocks = &.{block(0)}, .entry_block = block(0), .evidence = &.{proof} },
            .{ .id = worker_function, .name_hint = "worker", .parameters = &.{ value(1), value(2), value(3) }, .blocks = &.{block(1)}, .entry_block = block(1), .local_places = if (form == .place) &.{local_place} else &.{}, .evidence = &.{proof} },
            .{ .id = getter_function, .name_hint = "getter", .lexical_parent = worker_function, .captures = &.{capture}, .blocks = &.{block(2)}, .entry_block = block(2), .evidence = &.{proof} },
        };
        const captures = [_]ir.Capture{.{ .id = capture, .function = getter_function, .kind = .{ .immutable_value = value(4) }, .evidence = &.{proof} }};
        const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:creating-statement" }};
        const program: ir.Program = .{
            .program_id = "creating-statement",
            .entry_function = chunk_function,
            .functions = &functions,
            .blocks = &blocks,
            .instructions = instructions,
            .values = values,
            .places = places,
            .captures = &captures,
            .evidence = &evidence,
        };
    };
}

test "a closure's copy is named apart from the result its creating statement assigns" {
    const module = creatingStatementModule(.value);
    const source = try emitAlloc(std.testing.allocator, &module.program);
    defer std.testing.allocator.free(source);
    errdefer std.debug.print("{s}\n", .{source});
    // The closure's result `f_2` is declared above the copy's block and assigned inside it; a copy named `f_2` would
    // take the assignment, and `f_2()` after the block would call nil.
    try std.testing.expect(std.mem.indexOf(u8, source, "f_2 = function()") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local f_2 = ") == null);
}

test "a closure's copy is named apart from the local its creating statement assigns" {
    const module = creatingStatementModule(.place);
    const source = try emitAlloc(std.testing.allocator, &module.program);
    defer std.testing.allocator.free(source);
    errdefer std.debug.print("{s}\n", .{source});
    try std.testing.expect(std.mem.indexOf(u8, source, "x = function()") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local x = ") == null);
}

test "a closure's copy is named apart from the table its creating statement stores into" {
    const module = creatingStatementModule(.table);
    const source = try emitAlloc(std.testing.allocator, &module.program);
    defer std.testing.allocator.free(source);
    errdefer std.debug.print("{s}\n", .{source});
    try std.testing.expect(std.mem.indexOf(u8, source, "t.get = function()") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local t = ") == null);
}

test "a closure's copy is named apart from the key its creating statement stores under" {
    const module = creatingStatementModule(.key);
    const source = try emitAlloc(std.testing.allocator, &module.program);
    defer std.testing.allocator.free(source);
    errdefer std.debug.print("{s}\n", .{source});
    try std.testing.expect(std.mem.indexOf(u8, source, "t[k] = function()") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local k = ") == null);
}
