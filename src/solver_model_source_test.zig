const std = @import("std");
const ir = @import("ir.zig");
const solver_equivalence = @import("solver_equivalence.zig");
const solver_model = @import("solver_model.zig");

const dynamicValueDescriptor = solver_equivalence.dynamicValueDescriptor;
const exactPrimitiveBooleanResult = solver_equivalence.exactPrimitiveBooleanResult;
const exactPrimitiveEqualityResult = solver_equivalence.exactPrimitiveEqualityResult;

test "exact Boolean source results preserve static gates copies and operation effects" {
    const false_value = ir.ValueId.fromIndex(0);
    const true_value = ir.ValueId.fromIndex(1);
    const copied_false = ir.ValueId.fromIndex(2);
    const unknown_boolean = ir.ValueId.fromIndex(3);
    const text = ir.ValueId.fromIndex(4);
    const dynamic_false = ir.ValueId.fromIndex(5);
    const not_copy = ir.ValueId.fromIndex(6);
    const not_text = ir.ValueId.fromIndex(7);
    const not_dynamic = ir.ValueId.fromIndex(8);
    const effectful_not = ir.ValueId.fromIndex(9);
    const false_and_unknown = ir.ValueId.fromIndex(10);
    const unknown_and_true = ir.ValueId.fromIndex(11);
    const true_or_unknown = ir.ValueId.fromIndex(12);
    const dynamic_and_true = ir.ValueId.fromIndex(13);
    const values = [_]ir.Value{
        .{ .id = false_value, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = true_value, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = copied_false, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = unknown_boolean, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = text, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .parameter = 1 } },
        .{ .id = dynamic_false, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = not_copy, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = not_text, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
        .{ .id = not_dynamic, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(6), .index = 0 } } },
        .{ .id = effectful_not, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(7), .index = 0 } } },
        .{ .id = false_and_unknown, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(8), .index = 0 } } },
        .{ .id = unknown_and_true, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(9), .index = 0 } } },
        .{ .id = true_or_unknown, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(10), .index = 0 } } },
        .{ .id = dynamic_and_true, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(11), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .boolean = true } }, .results = &.{true_value}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .copy = false_value }, .results = &.{copied_false}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .boolean = false } }, .results = &.{dynamic_false}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .logical_not, .operand = copied_false } }, .results = &.{not_copy}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(5), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .logical_not, .operand = text } }, .results = &.{not_text}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(6), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .logical_not, .operand = dynamic_false } }, .results = &.{not_dynamic}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(7), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .logical_not, .operand = false_value } }, .results = &.{effectful_not}, .effects = .dynamic_call },
        .{ .id = ir.InstructionId.fromIndex(8), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .logical_and, .left = false_value, .right = unknown_boolean } }, .results = &.{false_and_unknown}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(9), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .logical_and, .left = unknown_boolean, .right = true_value } }, .results = &.{unknown_and_true}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(10), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .logical_or, .left = true_value, .right = unknown_boolean } }, .results = &.{true_or_unknown}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(11), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .logical_and, .left = dynamic_false, .right = true_value } }, .results = &.{dynamic_and_true}, .effects = .pure },
    };
    const program: ir.Program = .{
        .program_id = "exact-boolean-source-results",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };

    try std.testing.expectEqual(true, exactPrimitiveBooleanResult(&program, .{ .unary = instructions[4].operation.unary }).?);
    try std.testing.expectEqual(false, exactPrimitiveBooleanResult(&program, .{ .unary = instructions[5].operation.unary }).?);
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveBooleanResult(&program, .{ .unary = instructions[6].operation.unary }));
    try std.testing.expectEqual(false, exactPrimitiveBooleanResult(&program, .{ .binary = instructions[8].operation.binary }).?);
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveBooleanResult(&program, .{ .binary = instructions[9].operation.binary }));
    try std.testing.expectEqual(true, exactPrimitiveBooleanResult(&program, .{ .binary = instructions[10].operation.binary }).?);
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveBooleanResult(&program, .{ .binary = instructions[11].operation.binary }));

    try std.testing.expectEqual(true, dynamicValueDescriptor(&program, not_copy).?.exact_boolean.?);
    try std.testing.expectEqual(false, dynamicValueDescriptor(&program, not_text).?.exact_boolean.?);
    try std.testing.expect(dynamicValueDescriptor(&program, not_dynamic).?.exact_boolean == null);
    try std.testing.expect(dynamicValueDescriptor(&program, effectful_not).?.exact_boolean == null);
    try std.testing.expectEqual(false, dynamicValueDescriptor(&program, false_and_unknown).?.exact_boolean.?);
    try std.testing.expect(dynamicValueDescriptor(&program, unknown_and_true).?.exact_boolean == null);
    try std.testing.expectEqual(true, dynamicValueDescriptor(&program, true_or_unknown).?.exact_boolean.?);
    try std.testing.expect(dynamicValueDescriptor(&program, dynamic_and_true).?.exact_boolean == null);

    var dynamic_result_values = values;
    dynamic_result_values[not_copy.index()].type = .dynamic;
    var dynamic_result_program = program;
    dynamic_result_program.values = &dynamic_result_values;
    try std.testing.expectEqual(true, dynamicValueDescriptor(&dynamic_result_program, not_copy).?.exact_boolean.?);
}

test "exact primitive equality preserves scalar and reference identity" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const nil_a = ir.ValueId.fromIndex(0);
    const nil_b = ir.ValueId.fromIndex(1);
    const false_value = ir.ValueId.fromIndex(2);
    const true_value = ir.ValueId.fromIndex(3);
    const integer_seven = ir.ValueId.fromIndex(4);
    const number_seven = ir.ValueId.fromIndex(5);
    const fraction = ir.ValueId.fromIndex(6);
    const positive_zero = ir.ValueId.fromIndex(7);
    const negative_zero = ir.ValueId.fromIndex(8);
    const positive_infinity = ir.ValueId.fromIndex(9);
    const negative_infinity = ir.ValueId.fromIndex(10);
    const not_a_number = ir.ValueId.fromIndex(11);
    const string_left = ir.ValueId.fromIndex(12);
    const string_right = ir.ValueId.fromIndex(13);
    const concatenated = ir.ValueId.fromIndex(14);
    const equal_string = ir.ValueId.fromIndex(15);
    const distinct_string = ir.ValueId.fromIndex(16);
    const string_copy = ir.ValueId.fromIndex(17);
    const unknown_string_a = ir.ValueId.fromIndex(18);
    const unknown_string_b = ir.ValueId.fromIndex(19);
    const unknown_number = ir.ValueId.fromIndex(20);
    const unknown_boolean_a = ir.ValueId.fromIndex(21);
    const unknown_boolean_b = ir.ValueId.fromIndex(22);
    const table_value = ir.ValueId.fromIndex(23);
    const userdata_value = ir.ValueId.fromIndex(24);
    const effectful_false = ir.ValueId.fromIndex(25);
    const exact_result = ir.ValueId.fromIndex(26);
    const effectful_result = ir.ValueId.fromIndex(27);
    const values = [_]ir.Value{
        .{ .id = nil_a, .function = function_id, .type = .{ .kind = .nil_value }, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = nil_b, .function = function_id, .type = .{ .kind = .nil_value }, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = true_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = integer_seven, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = number_seven, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
        .{ .id = fraction, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(6), .index = 0 } } },
        .{ .id = positive_zero, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(7), .index = 0 } } },
        .{ .id = negative_zero, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(8), .index = 0 } } },
        .{ .id = positive_infinity, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(9), .index = 0 } } },
        .{ .id = negative_infinity, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(10), .index = 0 } } },
        .{ .id = not_a_number, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(11), .index = 0 } } },
        .{ .id = string_left, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(12), .index = 0 } } },
        .{ .id = string_right, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(13), .index = 0 } } },
        .{ .id = concatenated, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(14), .index = 0 } } },
        .{ .id = equal_string, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(15), .index = 0 } } },
        .{ .id = distinct_string, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(16), .index = 0 } } },
        .{ .id = string_copy, .function = function_id, .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(17), .index = 0 } } },
        .{ .id = unknown_string_a, .function = function_id, .type = .string, .origin = .{ .parameter = 0 } },
        .{ .id = unknown_string_b, .function = function_id, .type = .string, .origin = .{ .parameter = 1 } },
        .{ .id = unknown_number, .function = function_id, .type = .number, .origin = .{ .parameter = 2 } },
        .{ .id = unknown_boolean_a, .function = function_id, .type = .boolean, .origin = .{ .parameter = 3 } },
        .{ .id = unknown_boolean_b, .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } },
        .{ .id = table_value, .function = function_id, .type = .{ .kind = .table }, .origin = .{ .parameter = 5 } },
        .{ .id = userdata_value, .function = function_id, .type = .{ .kind = .userdata }, .origin = .{ .parameter = 6 } },
        .{ .id = effectful_false, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(18), .index = 0 } } },
        .{ .id = exact_result, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(19), .index = 0 } } },
        .{ .id = effectful_result, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(20), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = block_id, .operation = .{ .constant = .{ .nil_value = {} } }, .results = &.{nil_a}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = block_id, .operation = .{ .constant = .{ .nil_value = {} } }, .results = &.{nil_b}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = block_id, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = block_id, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{true_value}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = block_id, .operation = .{ .constant = .{ .integer = "7" } }, .results = &.{integer_seven}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(5), .block = block_id, .operation = .{ .constant = .{ .number = 7.0 } }, .results = &.{number_seven}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(6), .block = block_id, .operation = .{ .constant = .{ .number = 7.5 } }, .results = &.{fraction}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(7), .block = block_id, .operation = .{ .constant = .{ .number = 0.0 } }, .results = &.{positive_zero}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(8), .block = block_id, .operation = .{ .constant = .{ .number = -0.0 } }, .results = &.{negative_zero}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(9), .block = block_id, .operation = .{ .constant = .{ .special_number = .positive_infinity } }, .results = &.{positive_infinity}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(10), .block = block_id, .operation = .{ .constant = .{ .special_number = .negative_infinity } }, .results = &.{negative_infinity}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(11), .block = block_id, .operation = .{ .constant = .{ .special_number = .nan } }, .results = &.{not_a_number}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(12), .block = block_id, .operation = .{ .constant = .{ .string = "ab" } }, .results = &.{string_left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(13), .block = block_id, .operation = .{ .constant = .{ .string = "cd" } }, .results = &.{string_right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(14), .block = block_id, .operation = .{ .binary = .{ .operator = .concat, .left = string_left, .right = string_right } }, .results = &.{concatenated}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(15), .block = block_id, .operation = .{ .constant = .{ .string = "abcd" } }, .results = &.{equal_string}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(16), .block = block_id, .operation = .{ .constant = .{ .string = "abce" } }, .results = &.{distinct_string}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(17), .block = block_id, .operation = .{ .copy = concatenated }, .results = &.{string_copy}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(18), .block = block_id, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{effectful_false}, .effects = .dynamic_call },
        .{ .id = ir.InstructionId.fromIndex(19), .block = block_id, .operation = .{ .binary = .{ .operator = .equal, .left = concatenated, .right = equal_string } }, .results = &.{exact_result}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(20), .block = block_id, .operation = .{ .binary = .{ .operator = .equal, .left = concatenated, .right = equal_string } }, .results = &.{effectful_result}, .effects = .dynamic_call },
    };
    const program: ir.Program = .{
        .program_id = "exact-primitive-equality",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };
    const Case = struct { left: ir.ValueId, right: ir.ValueId, equal: ?bool };
    for ([_]Case{
        .{ .left = nil_a, .right = nil_b, .equal = true },
        .{ .left = false_value, .right = true_value, .equal = false },
        .{ .left = integer_seven, .right = number_seven, .equal = true },
        .{ .left = integer_seven, .right = fraction, .equal = false },
        .{ .left = positive_zero, .right = negative_zero, .equal = true },
        .{ .left = positive_infinity, .right = positive_infinity, .equal = true },
        .{ .left = positive_infinity, .right = negative_infinity, .equal = false },
        .{ .left = not_a_number, .right = not_a_number, .equal = false },
        .{ .left = concatenated, .right = equal_string, .equal = true },
        .{ .left = concatenated, .right = distinct_string, .equal = false },
        .{ .left = concatenated, .right = string_copy, .equal = true },
        .{ .left = unknown_string_a, .right = unknown_string_b, .equal = null },
        .{ .left = unknown_number, .right = unknown_number, .equal = null },
        .{ .left = unknown_boolean_a, .right = unknown_boolean_b, .equal = null },
        .{ .left = unknown_boolean_a, .right = unknown_string_a, .equal = false },
        .{ .left = effectful_false, .right = true_value, .equal = null },
        .{ .left = table_value, .right = table_value, .equal = null },
        .{ .left = userdata_value, .right = userdata_value, .equal = null },
    }) |case| {
        try std.testing.expectEqual(case.equal, exactPrimitiveEqualityResult(&program, .equal, case.left, case.right));
        const expected_not_equal: ?bool = if (case.equal) |equal| !equal else null;
        try std.testing.expectEqual(expected_not_equal, exactPrimitiveEqualityResult(&program, .not_equal, case.left, case.right));
    }

    try std.testing.expectEqual(true, dynamicValueDescriptor(&program, exact_result).?.exact_boolean.?);
    try std.testing.expect(dynamicValueDescriptor(&program, effectful_result).?.exact_boolean == null);

    const replay_terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .value = exact_result } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
    };
    var replay_program = program;
    replay_program.solver_terms = &replay_terms;
    const replay_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    const exact_binding = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .boolean = true } }};
    const forged_binding = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .boolean = false } }};
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &replay_program, replay_query, &exact_binding));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &replay_program, replay_query, &forged_binding));

    var dynamic_result_values = values;
    dynamic_result_values[exact_result.index()].type = .dynamic;
    var dynamic_result_program = program;
    dynamic_result_program.values = &dynamic_result_values;
    try std.testing.expectEqual(true, dynamicValueDescriptor(&dynamic_result_program, exact_result).?.exact_boolean.?);

    const references = @import("fixtures.zig").function_reference_module;
    try std.testing.expectEqual(true, exactPrimitiveEqualityResult(&references.program, .equal, references.v_left_a, references.v_left_b).?);
    try std.testing.expectEqual(true, exactPrimitiveEqualityResult(&references.program, .equal, references.v_left_a, references.v_left_copy).?);
    try std.testing.expectEqual(false, exactPrimitiveEqualityResult(&references.program, .equal, references.v_left_a, references.v_right).?);

    const fresh = @import("fixtures.zig").fresh_reference_module;
    try std.testing.expectEqual(true, exactPrimitiveEqualityResult(&fresh.program, .equal, fresh.v_thread_a, fresh.v_thread_a).?);
    try std.testing.expectEqual(false, exactPrimitiveEqualityResult(&fresh.program, .equal, fresh.v_thread_a, fresh.v_thread_b).?);
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveEqualityResult(&fresh.program, .equal, fresh.v_table_a, fresh.v_table_copy));

    var copied_thread_instructions = fresh.instructions;
    copied_thread_instructions[fresh.i_thread_b.index()].operation = .{ .copy = fresh.v_thread_a };
    copied_thread_instructions[fresh.i_thread_b.index()].effects = .pure;
    var copied_thread_program = fresh.program;
    copied_thread_program.instructions = &copied_thread_instructions;
    try std.testing.expectEqual(true, exactPrimitiveEqualityResult(&copied_thread_program, .equal, fresh.v_thread_a, fresh.v_thread_b).?);
}

test "model replay checks exact normalized runtime values" {
    const fixture = @import("fixtures.zig").automatic_promotion_module;
    const sort: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 32 };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = sort, .operation = .{ .value = fixture.v_left } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = sort, .operation = .{ .bit_vector_literal = .{ .value = "6", .bit_width = 32 } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    const exact = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .bit_vector = .{ .value = "6", .bit_width = 32 } } }};
    const changed = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .bit_vector = .{ .value = "7", .bit_width = 32 } } }};
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, query, &exact));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, query, &changed));
}

test "model replay reads IR integers with Luau rounding" {
    const two53 = ir.ValueId.fromIndex(0);
    const one = ir.ValueId.fromIndex(1);
    const wide = ir.ValueId.fromIndex(2);
    const four503 = ir.ValueId.fromIndex(3);
    const sum = ir.ValueId.fromIndex(4);
    const sum2 = ir.ValueId.fromIndex(5);
    const wide64 = ir.ValueId.fromIndex(6);
    const two53_64 = ir.ValueId.fromIndex(7);
    const unsigned64: ir.ValueType = .{ .kind = .integer, .bit_width = 64, .signed = false };
    const values = [_]ir.Value{
        .{ .id = two53, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = one, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = wide, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = four503, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = sum, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = sum2, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
        .{ .id = wide64, .function = ir.FunctionId.fromIndex(0), .type = unsigned64, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(6), .index = 0 } } },
        .{ .id = two53_64, .function = ir.FunctionId.fromIndex(0), .type = unsigned64, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(7), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "9007199254740992" } }, .results = &.{two53}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{one}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "9007199254740993" } }, .results = &.{wide}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "4503599627370496" } }, .results = &.{four503}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .add, .left = two53, .right = one } }, .results = &.{sum}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(5), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .add, .left = four503, .right = one } }, .results = &.{sum2}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(6), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "9007199254740993" } }, .results = &.{wide64}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(7), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "9007199254740992" } }, .results = &.{two53_64}, .effects = .pure },
    };
    const integer: ir.SolverSort = .{ .kind = .integer };
    const boolean: ir.SolverSort = .{ .kind = .boolean };
    const bit_vector64: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 64 };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = integer, .operation = .{ .value = two53 } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = integer, .operation = .{ .value = sum } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = boolean, .operation = .{ .binary = .{ .operator = .less, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = integer, .operation = .{ .value = wide } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = boolean, .operation = .{ .binary = .{ .operator = .not_equal, .left = ir.SolverTermId.fromIndex(3), .right = ir.SolverTermId.fromIndex(0) } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = bit_vector64, .operation = .{ .value = wide64 } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = bit_vector64, .operation = .{ .value = two53_64 } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = boolean, .operation = .{ .binary = .{ .operator = .not_equal, .left = ir.SolverTermId.fromIndex(5), .right = ir.SolverTermId.fromIndex(6) } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = integer, .operation = .{ .value = four503 } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = integer, .operation = .{ .value = sum2 } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = boolean, .operation = .{ .binary = .{ .operator = .less, .left = ir.SolverTermId.fromIndex(8), .right = ir.SolverTermId.fromIndex(9) } } },
    };
    const program: ir.Program = .{
        .program_id = "model-replay-luau-integer-rounding",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };
    const sum_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    const wide_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(1), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(4) };
    const bit_vector_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(2), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(7) };
    const control_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(3), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(10) };

    try std.testing.expect((try solver_model.replayAlloc(std.testing.allocator, &program, sum_query, &.{})) != solver_model.Replay.satisfied);
    try std.testing.expect((try solver_model.replayAlloc(std.testing.allocator, &program, wide_query, &.{})) != solver_model.Replay.satisfied);
    try std.testing.expect((try solver_model.replayAlloc(std.testing.allocator, &program, bit_vector_query, &.{})) != solver_model.Replay.satisfied);
    try std.testing.expect((try solver_model.replayAlloc(std.testing.allocator, &program, control_query, &.{})) == solver_model.Replay.satisfied);
}

test "model replay authenticates exact concatenated string length" {
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const concatenated = ir.ValueId.fromIndex(2);
    const length = ir.ValueId.fromIndex(3);
    const values = [_]ir.Value{
        .{ .id = left, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = right, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = concatenated, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = length, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "ab" } }, .results = &.{left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "cd" } }, .results = &.{right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .concat, .left = left, .right = right } }, .results = &.{concatenated}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .length, .operand = concatenated } }, .results = &.{length}, .effects = .pure },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = length } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "4" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
    };
    const program: ir.Program = .{
        .program_id = "model-replay-string-length",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    const exact = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .integer = "4" } }};
    const forged = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .integer = "5" } }};
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, query, &exact));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, query, &forged));

    switch (dynamicValueDescriptor(&program, length).?.exact_number.?) {
        .number => |value| try std.testing.expectEqual(@as(f64, 4.0), value),
        .integer => try std.testing.expect(false),
    }
    var effectful_instructions = instructions;
    effectful_instructions[2].effects = .dynamic_call;
    var effectful_program = program;
    effectful_program.instructions = &effectful_instructions;
    try std.testing.expect(dynamicValueDescriptor(&effectful_program, length).?.exact_number == null);
}

test "model replay authenticates exact numeric ordering" {
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const ordered = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = left, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = right, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = ordered, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = -0.0 } }, .results = &.{left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 0.0 } }, .results = &.{right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .less_equal, .left = left, .right = right } }, .results = &.{ordered}, .effects = .pure },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .value = ordered } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
    };
    const program: ir.Program = .{
        .program_id = "model-replay-number-ordering",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    const exact = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .boolean = true } }};
    const forged = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .boolean = false } }};
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, query, &exact));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, query, &forged));
}

test "model replay authenticates exact concatenated string ordering" {
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const concatenated = ir.ValueId.fromIndex(2);
    const upper = ir.ValueId.fromIndex(3);
    const ordered = ir.ValueId.fromIndex(4);
    const values = [_]ir.Value{
        .{ .id = left, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = right, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = concatenated, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = upper, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = ordered, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "ab" } }, .results = &.{left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "cd" } }, .results = &.{right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .concat, .left = left, .right = right } }, .results = &.{concatenated}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "abce" } }, .results = &.{upper}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .less, .left = concatenated, .right = upper } }, .results = &.{ordered}, .effects = .pure },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .value = ordered } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
    };
    const program: ir.Program = .{
        .program_id = "model-replay-string-ordering",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    const exact = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .boolean = true } }};
    const forged = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .boolean = false } }};
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, query, &exact));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, query, &forged));
}

test "model replay authenticates exact logical not over static truthiness" {
    const text = ir.ValueId.fromIndex(0);
    const negated = ir.ValueId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = text, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .parameter = 0 } },
        .{ .id = negated, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = ir.InstructionId.fromIndex(0),
        .block = ir.BlockId.fromIndex(0),
        .operation = .{ .unary = .{ .operator = .logical_not, .operand = text } },
        .results = &.{negated},
        .effects = .pure,
    }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .value = negated } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = false } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
    };
    const program: ir.Program = .{
        .program_id = "model-replay-static-truthiness-not",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    const exact = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .boolean = false } }};
    const forged = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .boolean = true } }};
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, query, &exact));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, query, &forged));
}

test "dynamic model coherence authenticates concatenated string identity" {
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const concatenated = ir.ValueId.fromIndex(2);
    const equal_literal = ir.ValueId.fromIndex(3);
    const distinct_literal = ir.ValueId.fromIndex(4);
    const copied = ir.ValueId.fromIndex(5);
    const values = [_]ir.Value{
        .{ .id = left, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = right, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = concatenated, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = equal_literal, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = distinct_literal, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = copied, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "ab" } }, .results = &.{left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "cd" } }, .results = &.{right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .concat, .left = left, .right = right } }, .results = &.{concatenated}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "abcd" } }, .results = &.{equal_literal}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "abce" } }, .results = &.{distinct_literal}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(5), .block = ir.BlockId.fromIndex(0), .operation = .{ .copy = concatenated }, .results = &.{copied}, .effects = .pure },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = concatenated } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = equal_literal } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = distinct_literal } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = copied } },
    };
    const program: ir.Program = .{
        .program_id = "model-coherence-string-concatenation",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };
    const separated_equal = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 1 } },
    };
    const joined_equal = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 0 } },
    };
    const collapsed_distinct = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 0 } },
    };
    const separated_distinct = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 1 } },
    };
    const separated_copy = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(3), .value = .{ .dynamic_identity = 1 } },
    };
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &separated_equal));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.coherent, solver_model.dynamicBindingsCoherence(&program, &joined_equal));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &collapsed_distinct));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.coherent, solver_model.dynamicBindingsCoherence(&program, &separated_distinct));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &separated_copy));
}

test "dynamic model coherence authenticates exact numeric identities" {
    const positive_a = ir.ValueId.fromIndex(0);
    const positive_b = ir.ValueId.fromIndex(1);
    const negative = ir.ValueId.fromIndex(2);
    const negated_positive = ir.ValueId.fromIndex(3);
    const doubled_positive = ir.ValueId.fromIndex(4);
    const finite_positive = ir.ValueId.fromIndex(5);
    const negative_zero = ir.ValueId.fromIndex(6);
    const divided_by_negative_zero = ir.ValueId.fromIndex(7);
    const floor_left = ir.ValueId.fromIndex(8);
    const floor_right = ir.ValueId.fromIndex(9);
    const floor_result = ir.ValueId.fromIndex(10);
    const floor_expected = ir.ValueId.fromIndex(11);
    const modulo_result = ir.ValueId.fromIndex(12);
    const modulo_expected = ir.ValueId.fromIndex(13);
    const power_result = ir.ValueId.fromIndex(14);
    const power_expected = ir.ValueId.fromIndex(15);
    const values = [_]ir.Value{
        .{ .id = positive_a, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = positive_b, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = negative, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = negated_positive, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = doubled_positive, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = finite_positive, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
        .{ .id = negative_zero, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(6), .index = 0 } } },
        .{ .id = divided_by_negative_zero, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(7), .index = 0 } } },
        .{ .id = floor_left, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(8), .index = 0 } } },
        .{ .id = floor_right, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(9), .index = 0 } } },
        .{ .id = floor_result, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(10), .index = 0 } } },
        .{ .id = floor_expected, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(11), .index = 0 } } },
        .{ .id = modulo_result, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(12), .index = 0 } } },
        .{ .id = modulo_expected, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(13), .index = 0 } } },
        .{ .id = power_result, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(14), .index = 0 } } },
        .{ .id = power_expected, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(15), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .special_number = .positive_infinity } }, .results = &.{positive_a}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .special_number = .positive_infinity } }, .results = &.{positive_b}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .special_number = .negative_infinity } }, .results = &.{negative}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .negate, .operand = positive_a } }, .results = &.{negated_positive}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .add, .left = positive_a, .right = positive_b } }, .results = &.{doubled_positive}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(5), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 1.0 } }, .results = &.{finite_positive}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(6), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = -0.0 } }, .results = &.{negative_zero}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(7), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .divide, .left = finite_positive, .right = negative_zero } }, .results = &.{divided_by_negative_zero}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(8), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = -7.0 } }, .results = &.{floor_left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(9), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 3.0 } }, .results = &.{floor_right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(10), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .floor_divide, .left = floor_left, .right = floor_right } }, .results = &.{floor_result}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(11), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = -3.0 } }, .results = &.{floor_expected}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(12), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .modulo, .left = floor_left, .right = floor_right } }, .results = &.{modulo_result}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(13), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 2.0 } }, .results = &.{modulo_expected}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(14), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .power, .left = modulo_expected, .right = floor_right } }, .results = &.{power_result}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(15), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 8.0 } }, .results = &.{power_expected}, .effects = .pure },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = positive_a } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = positive_b } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = negative } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = negated_positive } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = doubled_positive } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = finite_positive } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = negative_zero } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = divided_by_negative_zero } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = floor_left } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = floor_right } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = floor_result } },
        .{ .id = ir.SolverTermId.fromIndex(11), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = floor_expected } },
        .{ .id = ir.SolverTermId.fromIndex(12), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = modulo_result } },
        .{ .id = ir.SolverTermId.fromIndex(13), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = modulo_expected } },
        .{ .id = ir.SolverTermId.fromIndex(14), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = power_result } },
        .{ .id = ir.SolverTermId.fromIndex(15), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = power_expected } },
    };
    const program: ir.Program = .{
        .program_id = "dynamic-model-numeric-coherence",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };

    const separated_equal = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 1 } },
    };
    const joined_equal = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 0 } },
    };
    const collapsed_opposites = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 0 } },
    };
    const separated_negation = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(3), .value = .{ .dynamic_identity = 1 } },
    };
    const joined_negation = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(3), .value = .{ .dynamic_identity = 0 } },
    };
    const separated_arithmetic = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(4), .value = .{ .dynamic_identity = 1 } },
    };
    const joined_arithmetic = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(4), .value = .{ .dynamic_identity = 0 } },
    };
    const separated_division = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(7), .value = .{ .dynamic_identity = 1 } },
    };
    const joined_division = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(7), .value = .{ .dynamic_identity = 0 } },
    };
    const separated_floor_division = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(10), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(11), .value = .{ .dynamic_identity = 1 } },
    };
    const joined_floor_division = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(10), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(11), .value = .{ .dynamic_identity = 0 } },
    };
    const separated_modulo = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(12), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(13), .value = .{ .dynamic_identity = 1 } },
    };
    const joined_modulo = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(12), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(13), .value = .{ .dynamic_identity = 0 } },
    };
    const separated_power = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(14), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(15), .value = .{ .dynamic_identity = 1 } },
    };
    const joined_power = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(14), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(15), .value = .{ .dynamic_identity = 0 } },
    };
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &separated_equal));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.coherent, solver_model.dynamicBindingsCoherence(&program, &joined_equal));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &collapsed_opposites));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &separated_negation));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.coherent, solver_model.dynamicBindingsCoherence(&program, &joined_negation));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &separated_arithmetic));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.coherent, solver_model.dynamicBindingsCoherence(&program, &joined_arithmetic));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &separated_division));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.coherent, solver_model.dynamicBindingsCoherence(&program, &joined_division));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &separated_floor_division));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.coherent, solver_model.dynamicBindingsCoherence(&program, &joined_floor_division));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &separated_modulo));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.coherent, solver_model.dynamicBindingsCoherence(&program, &joined_modulo));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &separated_power));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.coherent, solver_model.dynamicBindingsCoherence(&program, &joined_power));
}
