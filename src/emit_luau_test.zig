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
