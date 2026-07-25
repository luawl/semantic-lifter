const std = @import("std");
const ir = @import("ir.zig");
const equivalence = @import("solver_equivalence.zig");

const DynamicCategory = equivalence.DynamicCategory;
const DynamicNumber = equivalence.DynamicNumber;
const DynamicDescriptor = equivalence.DynamicDescriptor;
const DynamicRelation = equivalence.DynamicRelation;
const termsEquivalent = equivalence.termsEquivalent;
const dynamicDescriptorRelation = equivalence.dynamicDescriptorRelation;
const dynamicValueDescriptor = equivalence.dynamicValueDescriptor;
const dynamicDescriptorIsNaN = equivalence.dynamicDescriptorIsNaN;
const dynamicDescriptorTruthiness = equivalence.dynamicDescriptorTruthiness;
const negateExactNumber = equivalence.negateExactNumber;
const exactFiniteNumberResult = equivalence.exactFiniteNumberResult;
const exactPrimitiveBinaryNumber = equivalence.exactPrimitiveBinaryNumber;
const exactPrimitiveNumberComparison = equivalence.exactPrimitiveNumberComparison;
const exactPrimitiveStringComparison = equivalence.exactPrimitiveStringComparison;
const exactPrimitiveRelationalComparison = equivalence.exactPrimitiveRelationalComparison;
const exactPrimitiveNumericComparison = equivalence.exactPrimitiveNumericComparison;
const exactPrimitiveLogicalNot = equivalence.exactPrimitiveLogicalNot;
const exactPrimitiveBooleanLogic = equivalence.exactPrimitiveBooleanLogic;

test "conditional solver terms compare through all three dependencies" {
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "1" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "2" } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .integer }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(0),
            .then_term = ir.SolverTermId.fromIndex(1),
            .else_term = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "1" } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "2" } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .integer }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(4),
            .then_term = ir.SolverTermId.fromIndex(5),
            .else_term = ir.SolverTermId.fromIndex(6),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "equivalent-if-then-else",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &terms,
    };
    try std.testing.expect(termsEquivalent(&program, ir.SolverTermId.fromIndex(3), ir.SolverTermId.fromIndex(7)));
    terms[6].operation.integer_literal = "3";
    try std.testing.expect(!termsEquivalent(&program, ir.SolverTermId.fromIndex(3), ir.SolverTermId.fromIndex(7)));
}

test "validated value definitions are transparent to term equivalence" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = fixture.v_result } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .value_definition = .{
            .value = fixture.v_result,
            .expression = ir.SolverTermId.fromIndex(0),
        } } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    try std.testing.expect(termsEquivalent(&program, ir.SolverTermId.fromIndex(0), ir.SolverTermId.fromIndex(1)));
    try std.testing.expect(termsEquivalent(&program, ir.SolverTermId.fromIndex(1), ir.SolverTermId.fromIndex(0)));
}

test "dynamic scalar descriptors distinguish exact and unresolved relations" {
    const exact_true: DynamicDescriptor = .{ .category = .boolean, .exact_boolean = true };
    const exact_false: DynamicDescriptor = .{ .category = .boolean, .exact_boolean = false };
    const symbolic_boolean: DynamicDescriptor = .{ .category = .boolean };
    try std.testing.expectEqual(DynamicRelation.equivalent, dynamicDescriptorRelation(exact_true, exact_true));
    try std.testing.expectEqual(DynamicRelation.distinct, dynamicDescriptorRelation(exact_true, exact_false));
    try std.testing.expectEqual(DynamicRelation.unresolved, dynamicDescriptorRelation(exact_true, symbolic_boolean));
    try std.testing.expectEqual(DynamicRelation.distinct, dynamicDescriptorRelation(exact_true, .{ .category = .string }));

    const integer_seven: DynamicDescriptor = .{ .category = .number, .exact_number = .{ .integer = "7" } };
    const number_seven: DynamicDescriptor = .{ .category = .number, .exact_number = .{ .number = 7.0 } };
    const number_fraction: DynamicDescriptor = .{ .category = .number, .exact_number = .{ .number = 7.5 } };
    const large_integer: DynamicDescriptor = .{ .category = .number, .exact_number = .{ .integer = "9007199254740993" } };
    const adjacent_large_integer: DynamicDescriptor = .{ .category = .number, .exact_number = .{ .integer = "9007199254740994" } };
    const large_number: DynamicDescriptor = .{ .category = .number, .exact_number = .{ .number = 9007199254740994.0 } };
    const positive_infinity: DynamicDescriptor = .{ .category = .number, .exact_number = .{ .number = std.math.inf(f64) } };
    const negative_infinity: DynamicDescriptor = .{ .category = .number, .exact_number = .{ .number = -std.math.inf(f64) } };
    const not_a_number: DynamicDescriptor = .{ .category = .number, .exact_number = .{ .number = std.math.nan(f64) } };
    const positive_zero: DynamicDescriptor = .{ .category = .number, .exact_number = .{ .number = 0.0 } };
    const negative_zero: DynamicDescriptor = .{ .category = .number, .exact_number = .{ .number = -0.0 } };
    try std.testing.expectEqual(DynamicRelation.equivalent, dynamicDescriptorRelation(integer_seven, number_seven));
    try std.testing.expectEqual(DynamicRelation.distinct, dynamicDescriptorRelation(integer_seven, number_fraction));
    try std.testing.expectEqual(DynamicRelation.equivalent, dynamicDescriptorRelation(large_integer, large_integer));
    try std.testing.expectEqual(DynamicRelation.unresolved, dynamicDescriptorRelation(large_integer, adjacent_large_integer));
    try std.testing.expectEqual(DynamicRelation.unresolved, dynamicDescriptorRelation(large_integer, number_seven));
    try std.testing.expectEqual(DynamicRelation.unresolved, dynamicDescriptorRelation(large_integer, large_number));
    try std.testing.expectEqual(DynamicRelation.equivalent, dynamicDescriptorRelation(positive_infinity, positive_infinity));
    try std.testing.expectEqual(DynamicRelation.distinct, dynamicDescriptorRelation(positive_infinity, negative_infinity));
    try std.testing.expectEqual(DynamicRelation.distinct, dynamicDescriptorRelation(integer_seven, positive_infinity));
    try std.testing.expectEqual(DynamicRelation.distinct, dynamicDescriptorRelation(positive_infinity, integer_seven));
    try std.testing.expectEqual(DynamicRelation.equivalent, dynamicDescriptorRelation(positive_zero, negative_zero));
    try std.testing.expectEqual(DynamicRelation.unresolved, dynamicDescriptorRelation(not_a_number, not_a_number));
}

test "exact primitive Boolean logic preserves truthiness and decisive unknown identities" {
    const exact_false: DynamicDescriptor = .{ .category = .boolean, .exact_boolean = false };
    const exact_true: DynamicDescriptor = .{ .category = .boolean, .exact_boolean = true };
    const unknown: DynamicDescriptor = .{ .category = .boolean };

    try std.testing.expectEqual(true, exactPrimitiveLogicalNot(.{ .category = .nil_value }).?);
    try std.testing.expectEqual(true, exactPrimitiveLogicalNot(exact_false).?);
    try std.testing.expectEqual(false, exactPrimitiveLogicalNot(exact_true).?);
    try std.testing.expectEqual(false, exactPrimitiveLogicalNot(.{ .category = .string }).?);
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveLogicalNot(unknown));
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveLogicalNot(null));

    try std.testing.expectEqual(false, exactPrimitiveBooleanLogic(.logical_and, exact_false, exact_false).?);
    try std.testing.expectEqual(false, exactPrimitiveBooleanLogic(.logical_and, exact_false, exact_true).?);
    try std.testing.expectEqual(false, exactPrimitiveBooleanLogic(.logical_and, exact_true, exact_false).?);
    try std.testing.expectEqual(true, exactPrimitiveBooleanLogic(.logical_and, exact_true, exact_true).?);
    try std.testing.expectEqual(false, exactPrimitiveBooleanLogic(.logical_and, exact_false, unknown).?);
    try std.testing.expectEqual(false, exactPrimitiveBooleanLogic(.logical_and, unknown, exact_false).?);
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveBooleanLogic(.logical_and, exact_true, unknown));

    try std.testing.expectEqual(false, exactPrimitiveBooleanLogic(.logical_or, exact_false, exact_false).?);
    try std.testing.expectEqual(true, exactPrimitiveBooleanLogic(.logical_or, exact_false, exact_true).?);
    try std.testing.expectEqual(true, exactPrimitiveBooleanLogic(.logical_or, exact_true, exact_false).?);
    try std.testing.expectEqual(true, exactPrimitiveBooleanLogic(.logical_or, exact_true, exact_true).?);
    try std.testing.expectEqual(true, exactPrimitiveBooleanLogic(.logical_or, exact_true, unknown).?);
    try std.testing.expectEqual(true, exactPrimitiveBooleanLogic(.logical_or, unknown, exact_true).?);
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveBooleanLogic(.logical_or, exact_false, unknown));

    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveBooleanLogic(.add, exact_true, exact_true));
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveBooleanLogic(.logical_and, exact_true, .{ .category = .number }));
}

test "exact primitive string comparison follows raw byte order and refuses unknown descriptors" {
    const prefix: DynamicDescriptor = .{ .category = .string, .exact_string = "ab" };
    const longer: DynamicDescriptor = .{ .category = .string, .exact_string = "aba" };
    const nul: DynamicDescriptor = .{ .category = .string, .exact_string = "a\x00" };
    const one: DynamicDescriptor = .{ .category = .string, .exact_string = "a\x01" };
    const utf8: DynamicDescriptor = .{ .category = .string, .exact_string = "\xc3\xa9" };
    const ascii: DynamicDescriptor = .{ .category = .string, .exact_string = "z" };

    try std.testing.expectEqual(true, exactPrimitiveStringComparison(.less, prefix, longer).?);
    try std.testing.expectEqual(true, exactPrimitiveStringComparison(.less_equal, prefix, prefix).?);
    try std.testing.expectEqual(true, exactPrimitiveStringComparison(.greater, one, nul).?);
    try std.testing.expectEqual(true, exactPrimitiveStringComparison(.greater_equal, utf8, ascii).?);
    try std.testing.expectEqual(false, exactPrimitiveStringComparison(.less, utf8, ascii).?);
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveStringComparison(.equal, prefix, longer));
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveStringComparison(.less, prefix, .{ .category = .string }));
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveStringComparison(.less, prefix, .{ .category = .number }));
}

test "exact relational comparison requires static exact-pure strings" {
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const concatenated = ir.ValueId.fromIndex(2);
    const upper = ir.ValueId.fromIndex(3);
    const dynamic_copy = ir.ValueId.fromIndex(4);
    const effectful_concat = ir.ValueId.fromIndex(5);
    const exact_ordered = ir.ValueId.fromIndex(6);
    const dynamic_ordered = ir.ValueId.fromIndex(7);
    const effectful_ordered = ir.ValueId.fromIndex(8);
    const values = [_]ir.Value{
        .{ .id = left, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = right, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = concatenated, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = upper, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = dynamic_copy, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = effectful_concat, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
        .{ .id = exact_ordered, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(6), .index = 0 } } },
        .{ .id = dynamic_ordered, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(7), .index = 0 } } },
        .{ .id = effectful_ordered, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(8), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "ab" } }, .results = &.{left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "cd" } }, .results = &.{right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .concat, .left = left, .right = right } }, .results = &.{concatenated}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "abce" } }, .results = &.{upper}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .copy = concatenated }, .results = &.{dynamic_copy}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(5), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .concat, .left = left, .right = right } }, .results = &.{effectful_concat}, .effects = .dynamic_call },
        .{ .id = ir.InstructionId.fromIndex(6), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .less, .left = concatenated, .right = upper } }, .results = &.{exact_ordered}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(7), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .less, .left = dynamic_copy, .right = upper } }, .results = &.{dynamic_ordered}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(8), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .less, .left = concatenated, .right = upper } }, .results = &.{effectful_ordered}, .effects = .dynamic_call },
    };
    const program: ir.Program = .{
        .program_id = "exact-string-relational-comparison",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };

    try std.testing.expectEqual(true, exactPrimitiveRelationalComparison(&program, .less, concatenated, upper).?);
    try std.testing.expectEqual(true, exactPrimitiveRelationalComparison(&program, .greater, upper, concatenated).?);
    try std.testing.expectEqual(true, exactPrimitiveRelationalComparison(&program, .less_equal, concatenated, concatenated).?);
    try std.testing.expectEqual(false, exactPrimitiveRelationalComparison(&program, .greater_equal, concatenated, upper).?);
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveNumericComparison(&program, .less, concatenated, upper));
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveRelationalComparison(&program, .equal, concatenated, upper));
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveRelationalComparison(&program, .less, dynamic_copy, upper));
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveRelationalComparison(&program, .less, effectful_concat, upper));
    try std.testing.expectEqual(true, dynamicValueDescriptor(&program, exact_ordered).?.exact_boolean.?);
    try std.testing.expect(dynamicValueDescriptor(&program, dynamic_ordered).?.exact_boolean == null);
    try std.testing.expect(dynamicValueDescriptor(&program, effectful_ordered).?.exact_boolean == null);
}

test "dynamic descriptors retain typed numeric constants" {
    const static_number = ir.ValueId.fromIndex(0);
    const copied_number = ir.ValueId.fromIndex(1);
    const static_integer = ir.ValueId.fromIndex(2);
    const copied_integer = ir.ValueId.fromIndex(3);
    const values = [_]ir.Value{
        .{ .id = static_number, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = copied_number, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = static_integer, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = copied_integer, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 7.0 } }, .results = &.{static_number}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .copy = static_number }, .results = &.{copied_number}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "7" } }, .results = &.{static_integer}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .copy = static_integer }, .results = &.{copied_integer}, .effects = .pure },
    };
    const program: ir.Program = .{
        .program_id = "dynamic-typed-numeric-descriptors",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };

    const number_descriptor = dynamicValueDescriptor(&program, copied_number).?;
    const integer_descriptor = dynamicValueDescriptor(&program, copied_integer).?;
    try std.testing.expectEqual(DynamicCategory.number, number_descriptor.category);
    try std.testing.expectEqual(DynamicCategory.number, integer_descriptor.category);
    try std.testing.expectEqual(DynamicRelation.equivalent, dynamicDescriptorRelation(number_descriptor, integer_descriptor));
}

test "dynamic descriptors preserve exact primitive numeric negation" {
    const positive_infinity = ir.ValueId.fromIndex(0);
    const negated_infinity = ir.ValueId.fromIndex(1);
    const negative_infinity = ir.ValueId.fromIndex(2);
    const not_a_number = ir.ValueId.fromIndex(3);
    const negated_nan = ir.ValueId.fromIndex(4);
    const positive_zero = ir.ValueId.fromIndex(5);
    const negative_zero = ir.ValueId.fromIndex(6);
    const effectful_negation = ir.ValueId.fromIndex(7);
    const values = [_]ir.Value{
        .{ .id = positive_infinity, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = negated_infinity, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = negative_infinity, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = not_a_number, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = negated_nan, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = positive_zero, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
        .{ .id = negative_zero, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(6), .index = 0 } } },
        .{ .id = effectful_negation, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(7), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .special_number = .positive_infinity } }, .results = &.{positive_infinity}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .negate, .operand = positive_infinity } }, .results = &.{negated_infinity}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .special_number = .negative_infinity } }, .results = &.{negative_infinity}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .special_number = .nan } }, .results = &.{not_a_number}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .negate, .operand = not_a_number } }, .results = &.{negated_nan}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(5), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 0.0 } }, .results = &.{positive_zero}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(6), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .negate, .operand = positive_zero } }, .results = &.{negative_zero}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(7), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .negate, .operand = positive_infinity } }, .results = &.{effectful_negation}, .effects = .dynamic_call },
    };
    const program: ir.Program = .{
        .program_id = "dynamic-exact-numeric-negation",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };

    const negated_infinity_descriptor = dynamicValueDescriptor(&program, negated_infinity).?;
    const negative_infinity_descriptor = dynamicValueDescriptor(&program, negative_infinity).?;
    try std.testing.expectEqual(DynamicRelation.equivalent, dynamicDescriptorRelation(negated_infinity_descriptor, negative_infinity_descriptor));
    try std.testing.expectEqual(true, dynamicDescriptorIsNaN(dynamicValueDescriptor(&program, negated_nan).?).?);
    const negative_zero_number = dynamicValueDescriptor(&program, negative_zero).?.exact_number.?.number;
    try std.testing.expect(negative_zero_number == 0.0 and std.math.signbit(negative_zero_number));
    try std.testing.expect(dynamicValueDescriptor(&program, effectful_negation).?.exact_number == null);

    try std.testing.expectEqual(DynamicRelation.equivalent, dynamicDescriptorRelation(
        .{ .category = .number, .exact_number = negateExactNumber(.{ .integer = "7" }) },
        .{ .category = .number, .exact_number = .{ .number = -7.0 } },
    ));
    try std.testing.expectEqual(@as(?DynamicNumber, null), negateExactNumber(.{ .integer = "9007199254740993" }));
}

test "dynamic descriptors preserve exact primitive number arithmetic" {
    const positive_infinity = ir.ValueId.fromIndex(0);
    const negative_infinity = ir.ValueId.fromIndex(1);
    const cancelled_infinity = ir.ValueId.fromIndex(2);
    const zero = ir.ValueId.fromIndex(3);
    const zero_times_infinity = ir.ValueId.fromIndex(4);
    const finite_left = ir.ValueId.fromIndex(5);
    const finite_right = ir.ValueId.fromIndex(6);
    const finite_sum = ir.ValueId.fromIndex(7);
    const finite_expected = ir.ValueId.fromIndex(8);
    const negative_zero = ir.ValueId.fromIndex(9);
    const signed_product = ir.ValueId.fromIndex(10);
    const division_by_negative_zero = ir.ValueId.fromIndex(11);
    const values = [_]ir.Value{
        .{ .id = positive_infinity, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = negative_infinity, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = cancelled_infinity, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = zero, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = zero_times_infinity, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = finite_left, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
        .{ .id = finite_right, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(6), .index = 0 } } },
        .{ .id = finite_sum, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(7), .index = 0 } } },
        .{ .id = finite_expected, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(8), .index = 0 } } },
        .{ .id = negative_zero, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(9), .index = 0 } } },
        .{ .id = signed_product, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(10), .index = 0 } } },
        .{ .id = division_by_negative_zero, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(11), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .special_number = .positive_infinity } }, .results = &.{positive_infinity}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .special_number = .negative_infinity } }, .results = &.{negative_infinity}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .add, .left = positive_infinity, .right = negative_infinity } }, .results = &.{cancelled_infinity}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 0.0 } }, .results = &.{zero}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .multiply, .left = zero, .right = positive_infinity } }, .results = &.{zero_times_infinity}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(5), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 1.5 } }, .results = &.{finite_left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(6), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 2.25 } }, .results = &.{finite_right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(7), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .add, .left = finite_left, .right = finite_right } }, .results = &.{finite_sum}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(8), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 3.75 } }, .results = &.{finite_expected}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(9), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = -0.0 } }, .results = &.{negative_zero}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(10), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .multiply, .left = negative_zero, .right = finite_right } }, .results = &.{signed_product}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(11), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .divide, .left = finite_left, .right = negative_zero } }, .results = &.{division_by_negative_zero}, .effects = .pure },
    };
    const program: ir.Program = .{
        .program_id = "dynamic-exact-number-arithmetic",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };

    try std.testing.expectEqual(true, dynamicDescriptorIsNaN(dynamicValueDescriptor(&program, cancelled_infinity).?).?);
    try std.testing.expectEqual(true, dynamicDescriptorIsNaN(dynamicValueDescriptor(&program, zero_times_infinity).?).?);
    try std.testing.expectEqual(DynamicRelation.equivalent, dynamicDescriptorRelation(
        dynamicValueDescriptor(&program, finite_sum).?,
        dynamicValueDescriptor(&program, finite_expected).?,
    ));
    const signed_product_number = dynamicValueDescriptor(&program, signed_product).?.exact_number.?.number;
    try std.testing.expect(signed_product_number == 0.0 and std.math.signbit(signed_product_number));
    try std.testing.expectEqual(DynamicRelation.equivalent, dynamicDescriptorRelation(
        dynamicValueDescriptor(&program, division_by_negative_zero).?,
        dynamicValueDescriptor(&program, negative_infinity).?,
    ));
    try std.testing.expectEqual(@as(f64, 3.75), exactFiniteNumberResult(&program, finite_sum).?);
    try std.testing.expect(exactFiniteNumberResult(&program, cancelled_infinity) == null);
    try std.testing.expect(exactFiniteNumberResult(&program, division_by_negative_zero) == null);
    const exact_negative_zero = exactFiniteNumberResult(&program, signed_product).?;
    try std.testing.expect(exact_negative_zero == 0.0 and std.math.signbit(exact_negative_zero));

    const finite_subtraction = exactPrimitiveBinaryNumber(
        .subtract,
        dynamicValueDescriptor(&program, finite_left),
        dynamicValueDescriptor(&program, finite_right),
    ).?;
    try std.testing.expectEqual(@as(f64, -0.75), finite_subtraction.number);
    const finite_division = exactPrimitiveBinaryNumber(
        .divide,
        dynamicValueDescriptor(&program, finite_right),
        dynamicValueDescriptor(&program, finite_left),
    ).?;
    try std.testing.expectEqual(@as(f64, 1.5), finite_division.number);
    const zero_divided_by_zero = exactPrimitiveBinaryNumber(
        .divide,
        dynamicValueDescriptor(&program, zero),
        dynamicValueDescriptor(&program, zero),
    ).?;
    try std.testing.expect(std.math.isNan(zero_divided_by_zero.number));

    var floor_instructions = instructions;
    floor_instructions[5].operation.constant = .{ .number = -7.0 };
    floor_instructions[6].operation.constant = .{ .number = 3.0 };
    floor_instructions[7].operation.binary.operator = .floor_divide;
    var floor_program = program;
    floor_program.instructions = &floor_instructions;
    const finite_floor_descriptor = dynamicValueDescriptor(&floor_program, finite_sum).?;
    try std.testing.expectEqual(@as(f64, -3.0), finite_floor_descriptor.exact_number.?.number);
    try std.testing.expect(finite_floor_descriptor.number_excludes_nan);

    var nan_floor_instructions = instructions;
    nan_floor_instructions[2].operation.binary.operator = .floor_divide;
    nan_floor_instructions[2].operation.binary.right = positive_infinity;
    var nan_floor_program = program;
    nan_floor_program.instructions = &nan_floor_instructions;
    const nan_floor_descriptor = dynamicValueDescriptor(&nan_floor_program, cancelled_infinity).?;
    try std.testing.expectEqual(true, dynamicDescriptorIsNaN(nan_floor_descriptor).?);
    try std.testing.expect(!nan_floor_descriptor.number_excludes_nan);

    const floor_divided_by_negative_zero = exactPrimitiveBinaryNumber(
        .floor_divide,
        dynamicValueDescriptor(&program, finite_left),
        dynamicValueDescriptor(&program, negative_zero),
    ).?;
    try std.testing.expectEqual(-std.math.inf(f64), floor_divided_by_negative_zero.number);
    const zero_floor_zero = exactPrimitiveBinaryNumber(
        .floor_divide,
        dynamicValueDescriptor(&program, zero),
        dynamicValueDescriptor(&program, zero),
    ).?;
    try std.testing.expect(std.math.isNan(zero_floor_zero.number));
    const infinity_floor_infinity = exactPrimitiveBinaryNumber(
        .floor_divide,
        dynamicValueDescriptor(&program, positive_infinity),
        dynamicValueDescriptor(&program, positive_infinity),
    ).?;
    try std.testing.expect(std.math.isNan(infinity_floor_infinity.number));
    const finite_floor_negative_infinity = exactPrimitiveBinaryNumber(
        .floor_divide,
        dynamicValueDescriptor(&program, finite_left),
        dynamicValueDescriptor(&program, negative_infinity),
    ).?.number;
    try std.testing.expect(finite_floor_negative_infinity == 0.0 and std.math.signbit(finite_floor_negative_infinity));
    const negative_zero_floor_finite = exactPrimitiveBinaryNumber(
        .floor_divide,
        dynamicValueDescriptor(&program, negative_zero),
        dynamicValueDescriptor(&program, finite_right),
    ).?.number;
    try std.testing.expect(negative_zero_floor_finite == 0.0 and std.math.signbit(negative_zero_floor_finite));

    var effectful_floor_instructions = floor_instructions;
    effectful_floor_instructions[7].effects = .dynamic_call;
    var effectful_floor_program = floor_program;
    effectful_floor_program.instructions = &effectful_floor_instructions;
    try std.testing.expect(dynamicValueDescriptor(&effectful_floor_program, finite_sum).?.exact_number == null);
    try std.testing.expect(exactFiniteNumberResult(&effectful_floor_program, finite_sum) == null);

    var modulo_instructions = floor_instructions;
    modulo_instructions[7].operation.binary.operator = .modulo;
    var modulo_program = program;
    modulo_program.instructions = &modulo_instructions;
    const finite_modulo_descriptor = dynamicValueDescriptor(&modulo_program, finite_sum).?;
    try std.testing.expectEqual(@as(f64, 2.0), finite_modulo_descriptor.exact_number.?.number);
    try std.testing.expect(finite_modulo_descriptor.number_excludes_nan);

    var nan_modulo_instructions = instructions;
    nan_modulo_instructions[2].operation.binary.operator = .modulo;
    nan_modulo_instructions[2].operation.binary.right = positive_infinity;
    var nan_modulo_program = program;
    nan_modulo_program.instructions = &nan_modulo_instructions;
    const nan_modulo_descriptor = dynamicValueDescriptor(&nan_modulo_program, cancelled_infinity).?;
    try std.testing.expectEqual(true, dynamicDescriptorIsNaN(nan_modulo_descriptor).?);
    try std.testing.expect(!nan_modulo_descriptor.number_excludes_nan);

    const positive_by_negative_modulo = exactPrimitiveBinaryNumber(
        .modulo,
        .{ .category = .number, .exact_number = .{ .number = 7.0 } },
        .{ .category = .number, .exact_number = .{ .number = -3.0 } },
    ).?.number;
    try std.testing.expectEqual(@as(f64, -2.0), positive_by_negative_modulo);
    const exact_multiple_modulo = exactPrimitiveBinaryNumber(
        .modulo,
        .{ .category = .number, .exact_number = .{ .number = -6.0 } },
        .{ .category = .number, .exact_number = .{ .number = 3.0 } },
    ).?.number;
    try std.testing.expect(exact_multiple_modulo == 0.0 and !std.math.signbit(exact_multiple_modulo));
    const negative_zero_modulo = exactPrimitiveBinaryNumber(
        .modulo,
        dynamicValueDescriptor(&program, negative_zero),
        dynamicValueDescriptor(&program, finite_right),
    ).?.number;
    try std.testing.expect(negative_zero_modulo == 0.0 and !std.math.signbit(negative_zero_modulo));
    const overflowed_modulo = exactPrimitiveBinaryNumber(
        .modulo,
        .{ .category = .number, .exact_number = .{ .number = 1e308 } },
        .{ .category = .number, .exact_number = .{ .number = 0.1 } },
    ).?.number;
    try std.testing.expectEqual(-std.math.inf(f64), overflowed_modulo);
    const subnormal_modulo = exactPrimitiveBinaryNumber(
        .modulo,
        .{ .category = .number, .exact_number = .{ .number = 5e-324 } },
        .{ .category = .number, .exact_number = .{ .number = 2.0 } },
    ).?.number;
    try std.testing.expectEqual(@as(f64, 5e-324), subnormal_modulo);
    inline for (.{
        exactPrimitiveBinaryNumber(
            .modulo,
            dynamicValueDescriptor(&program, finite_left),
            dynamicValueDescriptor(&program, zero),
        ).?.number,
        exactPrimitiveBinaryNumber(
            .modulo,
            dynamicValueDescriptor(&program, finite_left),
            dynamicValueDescriptor(&program, positive_infinity),
        ).?.number,
        exactPrimitiveBinaryNumber(
            .modulo,
            dynamicValueDescriptor(&program, positive_infinity),
            dynamicValueDescriptor(&program, finite_right),
        ).?.number,
        exactPrimitiveBinaryNumber(
            .modulo,
            dynamicValueDescriptor(&program, cancelled_infinity),
            dynamicValueDescriptor(&program, finite_right),
        ).?.number,
    }) |nan_modulo| try std.testing.expect(std.math.isNan(nan_modulo));

    var effectful_modulo_instructions = modulo_instructions;
    effectful_modulo_instructions[7].effects = .dynamic_call;
    var effectful_modulo_program = modulo_program;
    effectful_modulo_program.instructions = &effectful_modulo_instructions;
    try std.testing.expect(dynamicValueDescriptor(&effectful_modulo_program, finite_sum).?.exact_number == null);

    var power_instructions = instructions;
    power_instructions[5].operation.constant = .{ .number = 2.0 };
    power_instructions[6].operation.constant = .{ .number = 3.0 };
    power_instructions[7].operation.binary.operator = .power;
    var power_program = program;
    power_program.instructions = &power_instructions;
    const finite_power_descriptor = dynamicValueDescriptor(&power_program, finite_sum).?;
    try std.testing.expectEqual(@as(f64, 8.0), finite_power_descriptor.exact_number.?.number);
    try std.testing.expect(finite_power_descriptor.number_excludes_nan);

    var nan_power_instructions = power_instructions;
    nan_power_instructions[5].operation.constant = .{ .number = -2.0 };
    nan_power_instructions[6].operation.constant = .{ .number = 0.5 };
    var nan_power_program = program;
    nan_power_program.instructions = &nan_power_instructions;
    const nan_power_descriptor = dynamicValueDescriptor(&nan_power_program, finite_sum).?;
    try std.testing.expectEqual(true, dynamicDescriptorIsNaN(nan_power_descriptor).?);
    try std.testing.expect(!nan_power_descriptor.number_excludes_nan);

    var unresolved_power_instructions = power_instructions;
    unresolved_power_instructions[5].operation.constant = .{ .number = 2.5 };
    unresolved_power_instructions[6].operation.constant = .{ .number = 1.5 };
    var unresolved_power_program = program;
    unresolved_power_program.instructions = &unresolved_power_instructions;
    const unresolved_power_descriptor = dynamicValueDescriptor(&unresolved_power_program, finite_sum).?;
    try std.testing.expect(unresolved_power_descriptor.exact_number == null);
    try std.testing.expect(!unresolved_power_descriptor.number_excludes_nan);

    const negative_zero_power_negative_odd = exactPrimitiveBinaryNumber(
        .power,
        dynamicValueDescriptor(&program, negative_zero),
        .{ .category = .number, .exact_number = .{ .number = -3.0 } },
    ).?.number;
    try std.testing.expectEqual(-std.math.inf(f64), negative_zero_power_negative_odd);
    const negative_zero_power_negative_even = exactPrimitiveBinaryNumber(
        .power,
        dynamicValueDescriptor(&program, negative_zero),
        .{ .category = .number, .exact_number = .{ .number = -2.0 } },
    ).?.number;
    try std.testing.expectEqual(std.math.inf(f64), negative_zero_power_negative_even);
    const negative_zero_power_odd = exactPrimitiveBinaryNumber(
        .power,
        dynamicValueDescriptor(&program, negative_zero),
        .{ .category = .number, .exact_number = .{ .number = 3.0 } },
    ).?.number;
    try std.testing.expect(negative_zero_power_odd == 0.0 and std.math.signbit(negative_zero_power_odd));
    const negative_zero_power_even = exactPrimitiveBinaryNumber(
        .power,
        dynamicValueDescriptor(&program, negative_zero),
        .{ .category = .number, .exact_number = .{ .number = 2.0 } },
    ).?.number;
    try std.testing.expect(negative_zero_power_even == 0.0 and !std.math.signbit(negative_zero_power_even));
    try std.testing.expectEqual(@as(f64, 1.0), exactPrimitiveBinaryNumber(
        .power,
        dynamicValueDescriptor(&program, cancelled_infinity),
        dynamicValueDescriptor(&program, zero),
    ).?.number);
    try std.testing.expectEqual(@as(f64, 1.0), exactPrimitiveBinaryNumber(
        .power,
        .{ .category = .number, .exact_number = .{ .number = 1.0 } },
        dynamicValueDescriptor(&program, cancelled_infinity),
    ).?.number);
    try std.testing.expectEqual(@as(f64, 1.0), exactPrimitiveBinaryNumber(
        .power,
        .{ .category = .number, .exact_number = .{ .number = -1.0 } },
        dynamicValueDescriptor(&program, positive_infinity),
    ).?.number);
    try std.testing.expectEqual(-std.math.inf(f64), exactPrimitiveBinaryNumber(
        .power,
        dynamicValueDescriptor(&program, negative_infinity),
        .{ .category = .number, .exact_number = .{ .number = 3.0 } },
    ).?.number);
    const negative_infinity_power_negative_odd = exactPrimitiveBinaryNumber(
        .power,
        dynamicValueDescriptor(&program, negative_infinity),
        .{ .category = .number, .exact_number = .{ .number = -3.0 } },
    ).?.number;
    try std.testing.expect(negative_infinity_power_negative_odd == 0.0 and std.math.signbit(negative_infinity_power_negative_odd));
    const infinity_power_negative = exactPrimitiveBinaryNumber(
        .power,
        dynamicValueDescriptor(&program, positive_infinity),
        .{ .category = .number, .exact_number = .{ .number = -1.0 } },
    ).?.number;
    try std.testing.expect(infinity_power_negative == 0.0 and !std.math.signbit(infinity_power_negative));
    try std.testing.expect(std.math.isNan(exactPrimitiveBinaryNumber(
        .power,
        .{ .category = .number, .exact_number = .{ .number = -2.0 } },
        .{ .category = .number, .exact_number = .{ .number = 0.5 } },
    ).?.number));
    try std.testing.expectEqual(@as(f64, 9007199254740992.0), exactPrimitiveBinaryNumber(
        .power,
        .{ .category = .number, .exact_number = .{ .number = 2.0 } },
        .{ .category = .number, .exact_number = .{ .number = 53.0 } },
    ).?.number);
    try std.testing.expectEqual(@as(?DynamicNumber, null), exactPrimitiveBinaryNumber(
        .power,
        .{ .category = .number, .exact_number = .{ .number = 3.0 } },
        .{ .category = .number, .exact_number = .{ .number = 34.0 } },
    ));
    try std.testing.expectEqual(@as(?DynamicNumber, null), exactPrimitiveBinaryNumber(
        .power,
        .{ .category = .number, .exact_number = .{ .number = 2.5 } },
        .{ .category = .number, .exact_number = .{ .number = 1.5 } },
    ));
    try std.testing.expectEqual(@as(?DynamicNumber, null), exactPrimitiveBinaryNumber(
        .power,
        .{ .category = .number, .exact_number = .{ .number = 2.0 } },
        .{ .category = .number, .exact_number = .{ .number = -3.0 } },
    ));

    var effectful_power_instructions = power_instructions;
    effectful_power_instructions[7].effects = .dynamic_call;
    var effectful_power_program = power_program;
    effectful_power_program.instructions = &effectful_power_instructions;
    try std.testing.expect(dynamicValueDescriptor(&effectful_power_program, finite_sum).?.exact_number == null);

    try std.testing.expectEqual(true, exactPrimitiveNumericComparison(&program, .less, finite_left, finite_right).?);
    try std.testing.expectEqual(true, exactPrimitiveNumericComparison(&program, .less, negative_infinity, finite_left).?);
    inline for (.{
        ir.BinaryOperator.less,
        ir.BinaryOperator.less_equal,
        ir.BinaryOperator.greater,
        ir.BinaryOperator.greater_equal,
    }) |operator| {
        try std.testing.expectEqual(false, exactPrimitiveNumericComparison(&program, operator, cancelled_infinity, finite_left).?);
    }
    try std.testing.expectEqual(true, exactPrimitiveNumericComparison(&program, .less_equal, zero, negative_zero).?);
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveNumberComparison(
        .less,
        .{ .category = .number, .exact_number = .{ .integer = "9007199254740993" } },
        dynamicValueDescriptor(&program, finite_left),
    ));
    try std.testing.expectEqual(@as(?bool, null), exactPrimitiveNumberComparison(
        .less,
        .{ .category = .number },
        dynamicValueDescriptor(&program, finite_left),
    ));
    try std.testing.expectEqual(@as(?DynamicNumber, null), exactPrimitiveBinaryNumber(
        .add,
        .{ .category = .number, .exact_number = .{ .integer = "9007199254740993" } },
        dynamicValueDescriptor(&program, finite_left),
    ));
    try std.testing.expectEqual(@as(?DynamicNumber, null), exactPrimitiveBinaryNumber(
        .floor_divide,
        .{ .category = .number, .exact_number = .{ .integer = "9007199254740993" } },
        dynamicValueDescriptor(&program, finite_left),
    ));
    try std.testing.expectEqual(@as(?DynamicNumber, null), exactPrimitiveBinaryNumber(
        .floor_divide,
        .{ .category = .number },
        dynamicValueDescriptor(&program, finite_left),
    ));
    try std.testing.expectEqual(@as(?DynamicNumber, null), exactPrimitiveBinaryNumber(
        .modulo,
        .{ .category = .number, .exact_number = .{ .integer = "9007199254740993" } },
        dynamicValueDescriptor(&program, finite_left),
    ));
    try std.testing.expectEqual(@as(?DynamicNumber, null), exactPrimitiveBinaryNumber(
        .modulo,
        .{ .category = .number },
        dynamicValueDescriptor(&program, finite_left),
    ));
    try std.testing.expectEqual(@as(?DynamicNumber, null), exactPrimitiveBinaryNumber(
        .power,
        .{ .category = .number, .exact_number = .{ .integer = "9007199254740993" } },
        dynamicValueDescriptor(&program, finite_left),
    ));
    try std.testing.expectEqual(@as(?DynamicNumber, null), exactPrimitiveBinaryNumber(
        .power,
        .{ .category = .number },
        dynamicValueDescriptor(&program, finite_left),
    ));

    var integer_values = values;
    integer_values[finite_left.index()].type = .integer;
    integer_values[finite_right.index()].type = .integer;
    integer_values[finite_sum.index()].type = .integer;
    var integer_instructions = instructions;
    integer_instructions[finite_left.index()].operation.constant = .{ .integer = "9007199254740992" };
    integer_instructions[finite_right.index()].operation.constant = .{ .integer = "1" };
    integer_instructions[finite_sum.index()].operation.binary.operator = .floor_divide;
    var integer_program = program;
    integer_program.values = &integer_values;
    integer_program.instructions = &integer_instructions;
    try std.testing.expect(dynamicValueDescriptor(&integer_program, finite_sum).?.exact_number == null);
    integer_instructions[finite_sum.index()].operation.binary.operator = .modulo;
    try std.testing.expect(dynamicValueDescriptor(&integer_program, finite_sum).?.exact_number == null);
}

test "dynamic descriptors preserve fresh table and thread allocation identity" {
    const unknown_table = ir.ValueId.fromIndex(0);
    const table_a = ir.ValueId.fromIndex(1);
    const table_b = ir.ValueId.fromIndex(2);
    const table_copy = ir.ValueId.fromIndex(3);
    const callee = ir.ValueId.fromIndex(4);
    const thread_a = ir.ValueId.fromIndex(5);
    const thread_b = ir.ValueId.fromIndex(6);
    const loop_carried_table = ir.ValueId.fromIndex(7);
    const loop_carried_thread = ir.ValueId.fromIndex(8);
    const values = [_]ir.Value{
        .{ .id = unknown_table, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .table }, .origin = .{ .parameter = 0 } },
        .{ .id = table_a, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = table_b, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .table }, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = table_copy, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = callee, .function = ir.FunctionId.fromIndex(0), .type = .function, .origin = .{ .parameter = 1 } },
        .{ .id = thread_a, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = thread_b, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .thread }, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = loop_carried_table, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .table }, .origin = .{ .block_parameter = .{ .block = ir.BlockId.fromIndex(1), .index = 0 } } },
        .{ .id = loop_carried_thread, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .thread }, .origin = .{ .block_parameter = .{ .block = ir.BlockId.fromIndex(1), .index = 1 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .make_table = {} }, .results = &.{table_a}, .effects = .table_constructor },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .make_table_literal = .{ .fields = &.{} } }, .results = &.{table_b}, .effects = .table_constructor },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .copy = table_a }, .results = &.{table_copy}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .coroutine_create = .{ .callee = callee } }, .results = &.{thread_a}, .effects = .coroutine_create },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .coroutine_create = .{ .callee = callee } }, .results = &.{thread_b}, .effects = .coroutine_create },
    };
    const program: ir.Program = .{
        .program_id = "dynamic-fresh-reference-descriptors",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };

    const unknown_table_descriptor = dynamicValueDescriptor(&program, unknown_table).?;
    const table_a_descriptor = dynamicValueDescriptor(&program, table_a).?;
    const table_b_descriptor = dynamicValueDescriptor(&program, table_b).?;
    const table_copy_descriptor = dynamicValueDescriptor(&program, table_copy).?;
    const thread_a_descriptor = dynamicValueDescriptor(&program, thread_a).?;
    const thread_b_descriptor = dynamicValueDescriptor(&program, thread_b).?;
    const loop_carried_table_descriptor = dynamicValueDescriptor(&program, loop_carried_table).?;
    const loop_carried_thread_descriptor = dynamicValueDescriptor(&program, loop_carried_thread).?;
    try std.testing.expectEqual(DynamicRelation.equivalent, dynamicDescriptorRelation(table_a_descriptor, table_copy_descriptor));
    try std.testing.expectEqual(DynamicRelation.distinct, dynamicDescriptorRelation(table_a_descriptor, table_b_descriptor));
    try std.testing.expectEqual(DynamicRelation.unresolved, dynamicDescriptorRelation(table_a_descriptor, unknown_table_descriptor));
    try std.testing.expectEqual(DynamicRelation.distinct, dynamicDescriptorRelation(thread_a_descriptor, thread_b_descriptor));
    try std.testing.expectEqual(DynamicRelation.unresolved, dynamicDescriptorRelation(table_a_descriptor, loop_carried_table_descriptor));
    try std.testing.expectEqual(DynamicRelation.unresolved, dynamicDescriptorRelation(thread_a_descriptor, loop_carried_thread_descriptor));
    try std.testing.expectEqual(DynamicRelation.distinct, dynamicDescriptorRelation(table_a_descriptor, thread_a_descriptor));

    var tampered_instructions = instructions;
    tampered_instructions[1].results = &.{table_a};
    var tampered = program;
    tampered.instructions = &tampered_instructions;
    const untrusted_table_b = dynamicValueDescriptor(&tampered, table_b).?;
    try std.testing.expect(untrusted_table_b.allocation_site == null);
    try std.testing.expectEqual(DynamicRelation.unresolved, dynamicDescriptorRelation(table_a_descriptor, untrusted_table_b));
}

test "dynamic descriptors preserve canonical function reference identity" {
    const fixture = @import("fixtures.zig").function_reference_module;
    const unknown_function = ir.ValueId.fromIndex(fixture.values.len);
    const values = fixture.values ++ [_]ir.Value{.{
        .id = unknown_function,
        .function = fixture.f_entry,
        .type = .function,
        .origin = .{ .parameter = 0 },
    }};
    var program = fixture.program;
    program.values = &values;

    const left_a = dynamicValueDescriptor(&program, fixture.v_left_a).?;
    const left_b = dynamicValueDescriptor(&program, fixture.v_left_b).?;
    const left_copy = dynamicValueDescriptor(&program, fixture.v_left_copy).?;
    const right = dynamicValueDescriptor(&program, fixture.v_right).?;
    const unknown = dynamicValueDescriptor(&program, unknown_function).?;
    try std.testing.expectEqual(fixture.f_left, left_a.function_reference.?);
    try std.testing.expectEqual(DynamicRelation.equivalent, dynamicDescriptorRelation(left_a, left_b));
    try std.testing.expectEqual(DynamicRelation.equivalent, dynamicDescriptorRelation(left_a, left_copy));
    try std.testing.expectEqual(DynamicRelation.distinct, dynamicDescriptorRelation(left_a, right));
    try std.testing.expectEqual(DynamicRelation.unresolved, dynamicDescriptorRelation(left_a, unknown));

    const closure_fixture = @import("fixtures.zig").immutable_closure_module;
    const constructed_closure = dynamicValueDescriptor(&closure_fixture.program, closure_fixture.v_adder).?;
    try std.testing.expectEqual(DynamicCategory.function_value, constructed_closure.category);
    try std.testing.expect(constructed_closure.function_reference == null);
    try std.testing.expectEqual(DynamicRelation.unresolved, dynamicDescriptorRelation(left_a, constructed_closure));

    var functions = fixture.functions;
    functions[fixture.f_left.index()].lexical_parent = fixture.f_entry;
    var tampered = program;
    tampered.functions = &functions;
    try std.testing.expect(dynamicValueDescriptor(&tampered, fixture.v_left_a) == null);
}

test "dynamic descriptor truthiness follows Lua semantics" {
    try std.testing.expectEqual(false, dynamicDescriptorTruthiness(.{ .category = .nil_value }).?);
    try std.testing.expectEqual(false, dynamicDescriptorTruthiness(.{ .category = .boolean, .exact_boolean = false }).?);
    try std.testing.expectEqual(true, dynamicDescriptorTruthiness(.{ .category = .boolean, .exact_boolean = true }).?);
    try std.testing.expect(dynamicDescriptorTruthiness(.{ .category = .boolean }) == null);
    inline for (.{
        DynamicCategory.number,
        DynamicCategory.string,
        DynamicCategory.table,
        DynamicCategory.function_value,
        DynamicCategory.thread,
        DynamicCategory.userdata,
        DynamicCategory.tuple,
    }) |category| {
        try std.testing.expectEqual(true, dynamicDescriptorTruthiness(.{ .category = category }).?);
    }
}
