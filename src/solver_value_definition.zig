const std = @import("std");
const ir = @import("ir.zig");
const normalized_value = @import("normalized_value.zig");
const numerals = @import("numerals.zig");
const solver = @import("solver.zig");
const solver_equivalence = @import("solver_equivalence.zig");

pub fn valid(program: *const ir.Program, result_sort: ir.SolverSort, definition: ir.SolverValueDefinition) bool {
    if (definition.value.index() >= program.values.len or definition.expression.index() >= program.solver_terms.len) return false;
    if (definition.valid_when) |condition| {
        if (condition.index() >= program.solver_terms.len) return false;
    }
    const value = program.values[definition.value.index()];
    const expression = program.solver_terms[definition.expression.index()];
    if (value.type.kind == .dynamic or
        !sameSort(result_sort, expression.sort) or
        !sortAcceptsValue(result_sort, value.type)) return false;

    const origin = switch (value.origin) {
        .instruction_result => |origin| origin,
        else => return false,
    };
    if (origin.instruction.index() >= program.instructions.len) return false;
    const instruction = program.instructions[origin.instruction.index()];
    if (instruction.id != origin.instruction or
        origin.index >= instruction.results.len or
        instruction.results[origin.index] != definition.value)
    {
        return false;
    }

    if (definition.valid_when == null and
        expression.operation != .value and
        validExactNormalizedDefinition(program, instruction, value.type, expression) and
        solver_equivalence.termRepresentsValue(program, definition.expression, definition.value))
    {
        return true;
    }
    return switch (instruction.operation) {
        .unary => |operation| definition.valid_when == null and
            validTotalBit32Unary(program, operation, instruction.effects, value.type, expression),
        .binary => |operation| (definition.valid_when == null and
            (validPartialIntegerBinary(program, operation, instruction.effects, value.type, expression) or
                validTotalDynamicNumericEquality(program, operation, instruction.effects, value.type, expression))) or
            validTotalBit32Binary(program, operation, instruction.effects, value.type, expression, definition.valid_when) or
            validGuardedDynamicEquality(program, operation, instruction.effects, value.type, expression, definition.valid_when),
        else => false,
    };
}

fn validExactNormalizedDefinition(
    program: *const ir.Program,
    instruction: ir.Instruction,
    result_type: ir.ValueType,
    expression: ir.SolverTerm,
) bool {
    if (!definitionEffectsAreExactPure(instruction.effects)) return false;
    if (exactBit32LiteralMatches(program, instruction, result_type, expression)) return true;
    return switch (instruction.operation) {
        .constant => |literal| switch (literal) {
            .boolean => result_type.kind == .boolean and expression.sort.kind == .boolean,
            .integer => result_type.kind == .integer and expression.sort.kind == .integer,
            .number => result_type.kind == .number and expression.sort.kind == .real,
            .nil_value, .special_number, .string => false,
        },
        .copy => |source| source.index() < program.values.len and
            staticSortAcceptsValue(expression.sort, result_type) and
            staticSortAcceptsValue(expression.sort, program.values[source.index()].type),
        .unary => |operation| validExactUnaryDefinition(program, operation, result_type, expression),
        .binary => |operation| validExactBinaryDefinition(program, operation, result_type, expression),
        else => false,
    };
}

fn exactBit32LiteralMatches(
    program: *const ir.Program,
    instruction: ir.Instruction,
    result_type: ir.ValueType,
    expression: ir.SolverTerm,
) bool {
    if (!isUnsigned32(result_type) or !isUnsignedBitVector32(expression.sort) or instruction.results.len != 1) return false;
    const literal = switch (expression.operation) {
        .bit_vector_literal => |literal| literal,
        else => return false,
    };
    if (literal.bit_width != 32) return false;
    const actual = numerals.parseCanonicalUnsigned(u32, literal.value) orelse return false;
    const expected = solver_equivalence.exactPrimitiveBit32Result(program, instruction.results[0]) orelse return false;
    return actual == expected;
}

fn validExactUnaryDefinition(
    program: *const ir.Program,
    operation: ir.Unary,
    result_type: ir.ValueType,
    expression: ir.SolverTerm,
) bool {
    if (operation.operand.index() >= program.values.len) return false;
    const operand_type = program.values[operation.operand.index()].type;
    return switch (operation.operator) {
        .logical_not => blk: {
            if (solver_equivalence.exactPrimitiveBooleanResult(program, .{ .unary = operation })) |expected| {
                switch (expression.operation) {
                    .boolean_literal => |candidate| break :blk result_type.kind == .boolean and
                        expression.sort.kind == .boolean and candidate == expected,
                    else => {},
                }
            }
            break :blk result_type.kind == .boolean and expression.sort.kind == .boolean;
        },
        .negate => (result_type.kind == .integer and operand_type.kind == .integer and expression.sort.kind == .integer) or
            (result_type.kind == .number and
                (operand_type.kind == .integer or operand_type.kind == .number) and
                expression.sort.kind == .real),
        .length => result_type.kind == .integer and operand_type.kind == .string and
            expression.sort.kind == .integer and exactLengthLiteralMatches(program, operation.operand, expression),
        .bit_not => false,
    };
}

fn exactLengthLiteralMatches(program: *const ir.Program, operand: ir.ValueId, expression: ir.SolverTerm) bool {
    const expected = normalized_value.exactStringLength(program, operand) orelse return false;
    const literal = switch (expression.operation) {
        .integer_literal => |value| value,
        else => return false,
    };
    const actual = std.fmt.parseUnsigned(usize, literal, 10) catch return false;
    return actual == expected;
}

fn validExactBinaryDefinition(
    program: *const ir.Program,
    operation: ir.Binary,
    result_type: ir.ValueType,
    expression: ir.SolverTerm,
) bool {
    if (operation.left.index() >= program.values.len or operation.right.index() >= program.values.len) return false;
    if (result_type.kind == .number and expression.sort.kind == .real) switch (expression.operation) {
        .real_literal => |candidate| {
            const exact = solver_equivalence.exactPrimitiveBinaryNumber(
                operation.operator,
                solver_equivalence.dynamicValueDescriptor(program, operation.left),
                solver_equivalence.dynamicValueDescriptor(program, operation.right),
            ) orelse return false;
            const value = switch (exact) {
                .number => |number| number,
                .integer => return false,
            };
            return std.math.isFinite(value) and numerals.rationalExactlyRepresentsF64(candidate, value);
        },
        else => {},
    };
    if (solver_equivalence.exactPrimitiveBooleanResult(program, .{ .binary = operation })) |expected| {
        switch (expression.operation) {
            .boolean_literal => |candidate| return result_type.kind == .boolean and
                expression.sort.kind == .boolean and candidate == expected,
            else => {},
        }
    }
    const candidate = switch (expression.operation) {
        .binary => |binary| binary,
        else => return false,
    };
    if (candidate.left.index() >= program.solver_terms.len or candidate.right.index() >= program.solver_terms.len) return false;
    const operand_sort = program.solver_terms[candidate.left.index()].sort;
    const right_operand_sort = program.solver_terms[candidate.right.index()].sort;
    const left_kind = program.values[operation.left.index()].type.kind;
    const right_kind = program.values[operation.right.index()].type.kind;
    return switch (operation.operator) {
        .add, .subtract, .multiply => result_type.kind == .integer and
            left_kind == .integer and right_kind == .integer and
            expression.sort.kind == .integer and operand_sort.kind == .integer,
        .equal, .not_equal => result_type.kind == .boolean and expression.sort.kind == .boolean and
            ((left_kind == .boolean and right_kind == .boolean and operand_sort.kind == .boolean) or
                (left_kind == .integer and right_kind == .integer and
                    integerComparisonSortMatches(program, operation, operand_sort)) or
                (operand_sort.kind == .dynamic_value and sameSort(operand_sort, right_operand_sort) and
                    solver_equivalence.dynamicValuesHaveUnguardedPrimitiveEquality(program, operation.left, operation.right))),
        .less, .less_equal, .greater, .greater_equal => result_type.kind == .boolean and
            left_kind == .integer and right_kind == .integer and
            expression.sort.kind == .boolean and integerComparisonSortMatches(program, operation, operand_sort),
        .logical_and, .logical_or => result_type.kind == .boolean and
            left_kind == .boolean and right_kind == .boolean and
            expression.sort.kind == .boolean and operand_sort.kind == .boolean,
        .divide,
        .floor_divide,
        .modulo,
        .power,
        .concat,
        .bit_and,
        .bit_or,
        .bit_xor,
        .shift_left,
        .shift_right,
        => false,
    };
}

fn validTotalDynamicNumericEquality(
    program: *const ir.Program,
    operation: ir.Binary,
    effects: ir.EffectSummary,
    result_type: ir.ValueType,
    expression: ir.SolverTerm,
) bool {
    if (!definitionEffectsAreExactPure(effects) or result_type.kind != .boolean or expression.sort.kind != .boolean) return false;
    if (operation.operator != .equal and operation.operator != .not_equal) return false;
    if (!solver_equivalence.dynamicValuesHavePrimitiveEquality(program, operation.left, operation.right) or
        solver_equivalence.dynamicValuesHaveUnguardedPrimitiveEquality(program, operation.left, operation.right)) return false;

    const total_equal = switch (operation.operator) {
        .equal => expression,
        .not_equal => blk: {
            const operand = switch (expression.operation) {
                .logical_not => |term_id| term_id,
                else => return false,
            };
            if (operand.index() >= program.solver_terms.len) return false;
            break :blk program.solver_terms[operand.index()];
        },
        else => unreachable,
    };
    if (total_equal.sort.kind != .boolean) return false;
    const conjunction = switch (total_equal.operation) {
        .binary => |binary| binary,
        else => return false,
    };
    return conjunction.operator == .logical_and and
        validDynamicEqualityGuard(program, conjunction.left, operation.left, operation.right) and
        rawDynamicEqualityMatches(program, conjunction.right, operation.left, operation.right);
}

fn rawDynamicEqualityMatches(
    program: *const ir.Program,
    term_id: ir.SolverTermId,
    left: ir.ValueId,
    right: ir.ValueId,
) bool {
    if (term_id.index() >= program.solver_terms.len) return false;
    const term = program.solver_terms[term_id.index()];
    if (term.sort.kind != .boolean) return false;
    const equality = switch (term.operation) {
        .binary => |binary| binary,
        else => return false,
    };
    if (equality.operator != .equal or
        equality.left.index() >= program.solver_terms.len or
        equality.right.index() >= program.solver_terms.len) return false;
    const dynamic_sort: ir.SolverSort = .{ .kind = .dynamic_value };
    return sameSort(program.solver_terms[equality.left.index()].sort, dynamic_sort) and
        sameSort(program.solver_terms[equality.right.index()].sort, dynamic_sort) and
        solver_equivalence.termRepresentsValue(program, equality.left, left) and
        solver_equivalence.termRepresentsValue(program, equality.right, right);
}

fn validGuardedDynamicEquality(
    program: *const ir.Program,
    operation: ir.Binary,
    effects: ir.EffectSummary,
    result_type: ir.ValueType,
    expression: ir.SolverTerm,
    valid_when: ?ir.SolverTermId,
) bool {
    if (!definitionEffectsAreExactPure(effects) or result_type.kind != .boolean or expression.sort.kind != .boolean) return false;
    if (operation.operator != .equal and operation.operator != .not_equal) return false;
    if (!solver_equivalence.dynamicValuesHavePrimitiveEquality(program, operation.left, operation.right) or
        solver_equivalence.dynamicValuesHaveUnguardedPrimitiveEquality(program, operation.left, operation.right)) return false;
    const candidate = switch (expression.operation) {
        .binary => |binary| binary,
        else => return false,
    };
    const expected_operator: ir.SolverBinaryOperator = if (operation.operator == .equal) .equal else .not_equal;
    if (candidate.operator != expected_operator or
        candidate.left.index() >= program.solver_terms.len or
        candidate.right.index() >= program.solver_terms.len) return false;
    const dynamic_sort: ir.SolverSort = .{ .kind = .dynamic_value };
    if (!sameSort(program.solver_terms[candidate.left.index()].sort, dynamic_sort) or
        !sameSort(program.solver_terms[candidate.right.index()].sort, dynamic_sort) or
        !solver_equivalence.termRepresentsValue(program, candidate.left, operation.left) or
        !solver_equivalence.termRepresentsValue(program, candidate.right, operation.right)) return false;
    return validDynamicEqualityGuard(program, valid_when orelse return false, operation.left, operation.right);
}

fn validDynamicEqualityGuard(
    program: *const ir.Program,
    guard_id: ir.SolverTermId,
    left: ir.ValueId,
    right: ir.ValueId,
) bool {
    if (guard_id.index() >= program.solver_terms.len) return false;
    const guard = program.solver_terms[guard_id.index()];
    if (guard.sort.kind != .boolean) return false;
    const conjunction = switch (guard.operation) {
        .binary => |binary| binary,
        else => return false,
    };
    if (conjunction.operator != .logical_and) return false;
    return (nonNanGuardMatchesValue(program, conjunction.left, left) and
        nonNanGuardMatchesValue(program, conjunction.right, right)) or
        (nonNanGuardMatchesValue(program, conjunction.left, right) and
            nonNanGuardMatchesValue(program, conjunction.right, left));
}

fn nonNanGuardMatchesValue(program: *const ir.Program, guard_id: ir.SolverTermId, value_id: ir.ValueId) bool {
    if (guard_id.index() >= program.solver_terms.len) return false;
    const guard = program.solver_terms[guard_id.index()];
    if (guard.sort.kind != .boolean) return false;
    const is_nan_id = switch (guard.operation) {
        .logical_not => |operand| operand,
        else => return false,
    };
    if (is_nan_id.index() >= program.solver_terms.len) return false;
    const is_nan = program.solver_terms[is_nan_id.index()];
    if (is_nan.sort.kind != .boolean) return false;
    const dynamic_id = switch (is_nan.operation) {
        .dynamic_number_is_nan => |operand| operand,
        else => return false,
    };
    if (dynamic_id.index() >= program.solver_terms.len or
        program.solver_terms[dynamic_id.index()].sort.kind != .dynamic_value or
        program.solver_terms[dynamic_id.index()].operation != .value) return false;
    return solver_equivalence.termRepresentsValue(program, dynamic_id, value_id);
}

fn integerComparisonSortMatches(program: *const ir.Program, operation: ir.Binary, sort: ir.SolverSort) bool {
    if (sort.kind == .integer) return true;
    if (sort.kind != .bit_vector) return false;
    const left = program.values[operation.left.index()].type;
    const right = program.values[operation.right.index()].type;
    return left.bit_width == sort.bit_width and left.signed == sort.signed and
        right.bit_width == sort.bit_width and right.signed == sort.signed;
}

fn validPartialIntegerBinary(
    program: *const ir.Program,
    binary: ir.Binary,
    effects: ir.EffectSummary,
    result_type: ir.ValueType,
    expression: ir.SolverTerm,
) bool {
    if (binary.left.index() >= program.values.len or binary.right.index() >= program.values.len) return false;
    if (result_type.kind != .integer or
        program.values[binary.left.index()].type.kind != .integer or
        program.values[binary.right.index()].type.kind != .integer or
        expression.sort.kind != .integer or
        !definitionEffectsAreReplayable(effects))
    {
        return false;
    }

    return switch (binary.operator) {
        .floor_divide => switch (expression.operation) {
            .division => |division| division.mode == .integer_floor and
                solver_equivalence.termRepresentsValue(program, division.left, binary.left) and
                solver_equivalence.termRepresentsValue(program, division.right, binary.right),
            else => false,
        },
        .modulo => switch (expression.operation) {
            .remainder => |remainder| remainder.mode == .integer_floor and
                solver_equivalence.termRepresentsValue(program, remainder.left, binary.left) and
                solver_equivalence.termRepresentsValue(program, remainder.right, binary.right),
            else => false,
        },
        else => false,
    };
}

fn validTotalBit32Unary(
    program: *const ir.Program,
    operation: ir.Unary,
    effects: ir.EffectSummary,
    result_type: ir.ValueType,
    expression: ir.SolverTerm,
) bool {
    if (operation.operator != .bit_not or
        operation.mode != .primitive or
        operation.operand.index() >= program.values.len or
        !isUnsigned32(result_type) or
        !isUnsigned32(program.values[operation.operand.index()].type) or
        !isUnsignedBitVector32(expression.sort) or
        !definitionEffectsAreExactPure(effects))
    {
        return false;
    }
    return switch (expression.operation) {
        .bit_vector_not => |operand| solver_equivalence.termRepresentsValue(program, operand, operation.operand),
        else => false,
    };
}

fn validTotalBit32Binary(
    program: *const ir.Program,
    operation: ir.Binary,
    effects: ir.EffectSummary,
    result_type: ir.ValueType,
    expression: ir.SolverTerm,
    valid_when: ?ir.SolverTermId,
) bool {
    const expected_operator: ir.SolverBinaryOperator = switch (operation.operator) {
        .bit_and => .bit_and,
        .bit_or => .bit_or,
        .bit_xor => .bit_xor,
        .shift_left => .shift_left,
        .shift_right => .shift_right,
        else => return false,
    };
    const is_shift = operation.operator == .shift_left or operation.operator == .shift_right;
    if (is_shift != (operation.shift_behavior != null)) return false;
    if (operation.mode != .primitive or
        operation.left.index() >= program.values.len or
        operation.right.index() >= program.values.len or
        !isUnsigned32(result_type) or
        !isUnsigned32(program.values[operation.left.index()].type) or
        !isUnsigned32(program.values[operation.right.index()].type) or
        !isUnsignedBitVector32(expression.sort) or
        !definitionEffectsAreExactPure(effects))
    {
        return false;
    }
    if (is_shift) {
        switch (operation.shift_behavior.?) {
            .zero_saturating => if (valid_when != null) return false,
            .luau_bit32 => if (hasBoundedBit32ShiftCount(program, operation.right)) {
                if (valid_when != null) return false;
            } else {
                const condition = valid_when orelse return false;
                if (!validBit32ShiftGuard(program, condition, operation.right)) return false;
            },
        }
    } else if (valid_when != null) {
        return false;
    }
    return switch (expression.operation) {
        .binary => |candidate| candidate.operator == expected_operator and
            solver_equivalence.termRepresentsValue(program, candidate.left, operation.left) and
            solver_equivalence.termRepresentsValue(program, candidate.right, operation.right),
        else => false,
    };
}

fn validBit32ShiftGuard(program: *const ir.Program, condition_id: ir.SolverTermId, count: ir.ValueId) bool {
    if (condition_id.index() >= program.solver_terms.len) return false;
    const condition = program.solver_terms[condition_id.index()];
    if (condition.sort.kind != .boolean) return false;
    const binary = switch (condition.operation) {
        .binary => |binary| binary,
        else => return false,
    };
    const threshold: []const u8 = switch (binary.operator) {
        .less => "32",
        .less_equal => "31",
        else => return false,
    };
    return solver_equivalence.termRepresentsValue(program, binary.left, count) and
        isUnsignedBitVectorLiteral(program, binary.right, threshold);
}

fn isUnsignedBitVectorLiteral(program: *const ir.Program, term_id: ir.SolverTermId, expected: []const u8) bool {
    if (term_id.index() >= program.solver_terms.len) return false;
    const term = program.solver_terms[term_id.index()];
    if (!isUnsignedBitVector32(term.sort)) return false;
    return switch (term.operation) {
        .bit_vector_literal => |literal| literal.bit_width == 32 and std.mem.eql(u8, literal.value, expected),
        else => false,
    };
}

fn hasBoundedBit32ShiftCount(program: *const ir.Program, value_id: ir.ValueId) bool {
    return switch (solver.evaluateValue(program, value_id)) {
        .integer => |value| value >= 0 and value < 32,
        .bit_vector => |value| value.bit_width == 32 and value.value < 32,
        .boolean, .real, .unknown => false,
    };
}

fn definitionEffectsAreReplayable(effects: ir.EffectSummary) bool {
    return effects.precision != .unknown and
        !effects.reads_memory and
        !effects.writes_memory and
        !effects.may_yield and
        !effects.invokes_unknown_code;
}

fn definitionEffectsAreExactPure(effects: ir.EffectSummary) bool {
    return effects.precision == .exact and
        !effects.reads_memory and
        !effects.writes_memory and
        !effects.may_throw and
        !effects.may_yield and
        !effects.invokes_unknown_code;
}

fn isUnsigned32(value_type: ir.ValueType) bool {
    return value_type.kind == .integer and value_type.bit_width == 32 and !value_type.signed;
}

fn isUnsignedBitVector32(sort: ir.SolverSort) bool {
    return sort.kind == .bit_vector and sort.bit_width == 32 and !sort.signed;
}

fn sortAcceptsValue(sort: ir.SolverSort, value_type: ir.ValueType) bool {
    return switch (value_type.kind) {
        .dynamic => true,
        .boolean => sort.kind == .boolean,
        .integer => sort.kind == .integer or
            (sort.kind == .bit_vector and sort.bit_width == value_type.bit_width and sort.signed == value_type.signed),
        .number => sort.kind == .real,
        .nil_value, .string, .table, .function, .thread, .userdata, .tuple => sort.kind == .dynamic_value,
    };
}

fn staticSortAcceptsValue(sort: ir.SolverSort, value_type: ir.ValueType) bool {
    return value_type.kind != .dynamic and sortAcceptsValue(sort, value_type);
}

fn sameSort(left: ir.SolverSort, right: ir.SolverSort) bool {
    return std.meta.eql(left, right);
}

test "partial integer value definitions replay operation identity and convention" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .modulo,
        .left = fixture.v_sum,
        .right = fixture.v_factor,
    } };
    const integer: ir.SolverSort = .{ .kind = .integer };
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = integer, .operation = .{ .value = fixture.v_sum } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = integer, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(1) } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = integer, .operation = .{ .remainder = .{
            .mode = .integer_floor,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
            .defined_by = ir.SolverTermId.fromIndex(2),
        } } },
    };
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    const definition: ir.SolverValueDefinition = .{
        .value = fixture.v_result,
        .expression = ir.SolverTermId.fromIndex(3),
    };

    try std.testing.expect(valid(&program, integer, definition));
    terms[3].operation.remainder.mode = .integer_euclidean;
    try std.testing.expect(!valid(&program, integer, definition));
    terms[3].operation.remainder.mode = .integer_floor;
    terms[3].operation.remainder.left = ir.SolverTermId.fromIndex(1);
    try std.testing.expect(!valid(&program, integer, definition));
    terms[3].operation.remainder.left = ir.SolverTermId.fromIndex(0);
    try std.testing.expect(!valid(&program, integer, .{ .value = fixture.v_sum, .expression = definition.expression }));
    var values = fixture.values;
    values[fixture.v_result.index()].type = .dynamic;
    program.values = &values;
    try std.testing.expect(!valid(&program, integer, definition));
}

test "exact mathematical value definitions require static nonwrapping domains" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const integer: ir.SolverSort = .{ .kind = .integer };
    var values = fixture.values;
    var instructions = fixture.instructions;
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = integer, .operation = .{ .value = fixture.v_sum } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = integer, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = integer, .operation = .{ .binary = .{
            .operator = .multiply,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    const definition: ir.SolverValueDefinition = .{
        .value = fixture.v_result,
        .expression = ir.SolverTermId.fromIndex(2),
    };

    try std.testing.expect(valid(&program, integer, definition));
    values[fixture.v_result.index()].type = .dynamic;
    try std.testing.expect(!valid(&program, integer, definition));
    values[fixture.v_result.index()].type = .integer;
    const signed_bv64: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 64, .signed = true };
    for (&terms) |*term| term.sort = signed_bv64;
    try std.testing.expect(!valid(&program, signed_bv64, definition));
    for (&terms) |*term| term.sort = integer;
    instructions[fixture.i_result.index()].effects.may_throw = true;
    try std.testing.expect(!valid(&program, integer, definition));
}

test "exact integer negation maps to arithmetic negation" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .unary = .{
        .operator = .negate,
        .operand = fixture.v_sum,
    } };
    const integer: ir.SolverSort = .{ .kind = .integer };
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = integer, .operation = .{ .value = fixture.v_sum } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = integer, .operation = .{ .arithmetic_negate = ir.SolverTermId.fromIndex(0) } },
    };
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    const definition: ir.SolverValueDefinition = .{
        .value = fixture.v_result,
        .expression = ir.SolverTermId.fromIndex(1),
    };

    try std.testing.expect(valid(&program, integer, definition));
    terms[1].operation = .{ .integer_to_bit_vector = ir.SolverTermId.fromIndex(0) };
    try std.testing.expect(!valid(&program, integer, definition));
    terms[1].operation = .{ .arithmetic_negate = ir.SolverTermId.fromIndex(0) };
    instructions[fixture.i_result.index()].operation.unary.operand = fixture.v_factor;
    try std.testing.expect(!valid(&program, integer, definition));
}

test "exact string length definitions authenticate concatenation provenance" {
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
    var instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "ab" } }, .results = &.{left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "cd" } }, .results = &.{right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .concat, .left = left, .right = right } }, .results = &.{concatenated}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .length, .operand = concatenated } }, .results = &.{length}, .effects = .pure },
    };
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "4" } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .value_definition = .{ .value = length, .expression = ir.SolverTermId.fromIndex(0) } } },
    };
    const program: ir.Program = .{
        .program_id = "exact-string-length-definition",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };
    const sort: ir.SolverSort = .{ .kind = .integer };

    try std.testing.expect(valid(&program, sort, terms[1].operation.value_definition));
    terms[0].operation = .{ .integer_literal = "5" };
    try std.testing.expect(!valid(&program, sort, terms[1].operation.value_definition));
    terms[0].operation = .{ .integer_literal = "4" };
    instructions[2].effects = .dynamic_call;
    try std.testing.expect(!valid(&program, sort, terms[1].operation.value_definition));
}

test "exact number ordering definitions authenticate Boolean results" {
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const ordered = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = left, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = right, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = ordered, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
    };
    var instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 1.5 } }, .results = &.{left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 2.25 } }, .results = &.{right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .less, .left = left, .right = right } }, .results = &.{ordered}, .effects = .pure },
    };
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .value_definition = .{ .value = ordered, .expression = ir.SolverTermId.fromIndex(0) } } },
    };
    const program: ir.Program = .{
        .program_id = "exact-number-ordering-definition",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };
    const sort: ir.SolverSort = .{ .kind = .boolean };

    try std.testing.expect(valid(&program, sort, terms[1].operation.value_definition));
    terms[0].operation = .{ .boolean_literal = false };
    try std.testing.expect(!valid(&program, sort, terms[1].operation.value_definition));
    terms[0].operation = .{ .boolean_literal = true };
    instructions[2].effects = .dynamic_call;
    try std.testing.expect(!valid(&program, sort, terms[1].operation.value_definition));
}

test "exact primitive equality definitions accept literal and structural forms" {
    const fixture = @import("fixtures.zig").dynamic_truthiness_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_truthy_not.index()].operation = .{ .binary = .{
        .operator = .equal,
        .left = fixture.v_truthy_literal,
        .right = fixture.v_truthy_condition,
    } };
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_truthy_literal } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_truthy_condition } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = false } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .value_definition = .{
            .value = fixture.v_truthy_not,
            .expression = ir.SolverTermId.fromIndex(3),
        } } },
    };
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    const sort: ir.SolverSort = .{ .kind = .boolean };

    try std.testing.expect(valid(&program, sort, terms[5].operation.value_definition));
    terms[5].operation.value_definition.expression = ir.SolverTermId.fromIndex(4);
    try std.testing.expect(!valid(&program, sort, terms[5].operation.value_definition));
    terms[5].operation.value_definition.expression = ir.SolverTermId.fromIndex(2);
    try std.testing.expect(valid(&program, sort, terms[5].operation.value_definition));
    terms[2].operation.binary.operator = .not_equal;
    try std.testing.expect(!valid(&program, sort, terms[5].operation.value_definition));
    terms[2].operation.binary.operator = .equal;
    instructions[fixture.i_truthy_not.index()].effects = .dynamic_call;
    try std.testing.expect(!valid(&program, sort, terms[5].operation.value_definition));
}

test "exact Boolean definitions authenticate decisive logical results" {
    const false_value = ir.ValueId.fromIndex(0);
    const unknown = ir.ValueId.fromIndex(1);
    const result = ir.ValueId.fromIndex(2);
    var values = [_]ir.Value{
        .{ .id = false_value, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = unknown, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = result, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
    };
    var instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .logical_and, .left = false_value, .right = unknown } }, .results = &.{result}, .effects = .pure },
    };
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = false } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .value = false_value } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .value = unknown } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .value_definition = .{ .value = result, .expression = ir.SolverTermId.fromIndex(0) } } },
    };
    const program: ir.Program = .{
        .program_id = "exact-boolean-logic-definition",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };
    const sort: ir.SolverSort = .{ .kind = .boolean };

    try std.testing.expect(valid(&program, sort, terms[4].operation.value_definition));
    terms[0].operation = .{ .boolean_literal = true };
    try std.testing.expect(!valid(&program, sort, terms[4].operation.value_definition));
    terms[0].operation = .{ .boolean_literal = false };
    terms[4].operation.value_definition.expression = ir.SolverTermId.fromIndex(3);
    try std.testing.expect(valid(&program, sort, terms[4].operation.value_definition));
    terms[3].operation.binary.operator = .logical_or;
    try std.testing.expect(!valid(&program, sort, terms[4].operation.value_definition));
    terms[3].operation.binary.operator = .logical_and;
    values[unknown.index()].type = .dynamic;
    try std.testing.expect(!valid(&program, sort, terms[4].operation.value_definition));
    values[unknown.index()].type = .boolean;
    instructions[1].effects = .dynamic_call;
    try std.testing.expect(!valid(&program, sort, terms[4].operation.value_definition));
}

test "u32 value definitions replay exact bitwise operation identity" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };
    const bv32: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 32 };
    var values = fixture.values;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_factor.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .bit_xor,
        .left = fixture.v_sum,
        .right = fixture.v_factor,
        .mode = .primitive,
    } };
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv32, .operation = .{ .value = fixture.v_sum } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv32, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = bv32, .operation = .{ .binary = .{
            .operator = .bit_xor,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    const definition: ir.SolverValueDefinition = .{
        .value = fixture.v_result,
        .expression = ir.SolverTermId.fromIndex(2),
    };

    try std.testing.expect(valid(&program, bv32, definition));
    instructions[fixture.i_result.index()].operation.binary.operator = .bit_or;
    try std.testing.expect(!valid(&program, bv32, definition));
    instructions[fixture.i_result.index()].operation.binary.operator = .bit_xor;
    instructions[fixture.i_result.index()].operation.binary.mode = .semantic;
    try std.testing.expect(!valid(&program, bv32, definition));
    instructions[fixture.i_result.index()].operation.binary.mode = .primitive;
    instructions[fixture.i_result.index()].operation.binary.operator = .shift_left;
    instructions[fixture.i_result.index()].operation.binary.shift_behavior = .luau_bit32;
    instructions[fixture.i_result.index()].operation.binary.right = fixture.v_sum;
    terms[2].operation.binary.operator = .shift_left;
    terms[2].operation.binary.right = ir.SolverTermId.fromIndex(0);
    try std.testing.expect(!valid(&program, bv32, definition));
    instructions[fixture.i_result.index()].operation.binary.operator = .bit_xor;
    instructions[fixture.i_result.index()].operation.binary.shift_behavior = null;
    instructions[fixture.i_result.index()].operation.binary.right = fixture.v_factor;
    terms[2].operation.binary.operator = .bit_xor;
    terms[2].operation.binary.right = ir.SolverTermId.fromIndex(1);
    instructions[fixture.i_result.index()].effects.may_throw = true;
    try std.testing.expect(!valid(&program, bv32, definition));
    instructions[fixture.i_result.index()].effects = .pure;
    values[fixture.v_result.index()].type.signed = true;
    try std.testing.expect(!valid(&program, bv32, definition));
}

test "u32 shift definitions require an exact bounded displacement" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };
    const bv32: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 32 };
    var values = fixture.values;
    values[fixture.v_right.index()].type = u32_type;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_factor.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .shift_right,
        .left = fixture.v_sum,
        .right = fixture.v_factor,
        .mode = .primitive,
        .shift_behavior = .luau_bit32,
    } };
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv32, .operation = .{ .value = fixture.v_sum } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv32, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = bv32, .operation = .{ .bit_vector_literal = .{
            .value = "32",
            .bit_width = 32,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .less,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = bv32, .operation = .{ .binary = .{
            .operator = .shift_right,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    var definition: ir.SolverValueDefinition = .{
        .value = fixture.v_result,
        .expression = ir.SolverTermId.fromIndex(4),
    };

    try std.testing.expect(valid(&program, bv32, definition));
    instructions[fixture.i_factor.index()].operation.constant.integer = "32";
    try std.testing.expect(!valid(&program, bv32, definition));
    instructions[fixture.i_factor.index()].operation.constant.integer = "-1";
    try std.testing.expect(!valid(&program, bv32, definition));
    instructions[fixture.i_factor.index()].operation.constant.integer = "4";
    instructions[fixture.i_result.index()].operation.binary.right = fixture.v_right;
    terms[1].operation = .{ .value = fixture.v_right };
    try std.testing.expect(!valid(&program, bv32, definition));
    definition.valid_when = ir.SolverTermId.fromIndex(3);
    try std.testing.expect(valid(&program, bv32, definition));
    terms[2].operation.bit_vector_literal.value = "33";
    try std.testing.expect(!valid(&program, bv32, definition));
    terms[2].operation.bit_vector_literal.value = "32";
    terms[3].operation.binary.operator = .greater;
    try std.testing.expect(!valid(&program, bv32, definition));
    terms[3].operation.binary.operator = .less;
    terms[3].operation.binary.left = ir.SolverTermId.fromIndex(0);
    try std.testing.expect(!valid(&program, bv32, definition));
    terms[3].operation.binary.left = ir.SolverTermId.fromIndex(1);
    definition.valid_when = ir.SolverTermId.fromIndex(99);
    try std.testing.expect(!valid(&program, bv32, definition));

    definition.valid_when = null;
    instructions[fixture.i_result.index()].operation.binary.shift_behavior = .zero_saturating;
    try std.testing.expect(valid(&program, bv32, definition));
    definition.valid_when = ir.SolverTermId.fromIndex(3);
    try std.testing.expect(!valid(&program, bv32, definition));
    definition.valid_when = null;
    instructions[fixture.i_result.index()].operation.binary.shift_behavior = null;
    try std.testing.expect(!valid(&program, bv32, definition));
    instructions[fixture.i_result.index()].operation.binary.shift_behavior = .luau_bit32;
    try std.testing.expect(!valid(&program, bv32, definition));
}

test "u32 value definitions replay exact bitwise not" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };
    const bv32: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 32 };
    var values = fixture.values;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .unary = .{
        .operator = .bit_not,
        .operand = fixture.v_sum,
        .mode = .primitive,
    } };
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv32, .operation = .{ .value = fixture.v_sum } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv32, .operation = .{ .bit_vector_not = ir.SolverTermId.fromIndex(0) } },
    };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    const definition: ir.SolverValueDefinition = .{
        .value = fixture.v_result,
        .expression = ir.SolverTermId.fromIndex(1),
    };

    try std.testing.expect(valid(&program, bv32, definition));
    instructions[fixture.i_result.index()].operation.unary.mode = .semantic;
    try std.testing.expect(!valid(&program, bv32, definition));
    instructions[fixture.i_result.index()].operation.unary.mode = .primitive;
    instructions[fixture.i_result.index()].operation.unary.operator = .negate;
    try std.testing.expect(!valid(&program, bv32, definition));
    instructions[fixture.i_result.index()].operation.unary.operator = .bit_not;
    terms[1].operation = .{ .bit_vector_not = ir.SolverTermId.fromIndex(1) };
    try std.testing.expect(!valid(&program, bv32, definition));
}

test "u32 value definitions authenticate exact bit-vector literals" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };
    const bv32: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 32 };
    var values = fixture.values;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_factor.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation = .{ .constant = .{ .integer = "305419896" } };
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = "252645135" } };
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .bit_and,
        .left = fixture.v_sum,
        .right = fixture.v_factor,
        .mode = .primitive,
    } };
    var terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = bv32,
        .operation = .{ .bit_vector_literal = .{ .value = "33818120", .bit_width = 32 } },
    }};
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    const definition: ir.SolverValueDefinition = .{
        .value = fixture.v_result,
        .expression = ir.SolverTermId.fromIndex(0),
    };

    try std.testing.expect(valid(&program, bv32, definition));
    try std.testing.expect(solver_equivalence.termRepresentsValue(&program, definition.expression, definition.value));

    terms[0].operation.bit_vector_literal.value = "33818121";
    try std.testing.expect(!valid(&program, bv32, definition));
    terms[0].operation.bit_vector_literal.value = "033818120";
    try std.testing.expect(!valid(&program, bv32, definition));
    terms[0].operation.bit_vector_literal.value = "33818120";
    terms[0].operation.bit_vector_literal.bit_width = 31;
    try std.testing.expect(!valid(&program, bv32, definition));
    terms[0].operation.bit_vector_literal.bit_width = 32;

    instructions[fixture.i_result.index()].effects = .dynamic_call;
    try std.testing.expect(!valid(&program, bv32, definition));
    instructions[fixture.i_result.index()].effects = .pure;
    instructions[fixture.i_result.index()].operation.binary.mode = .semantic;
    try std.testing.expect(!valid(&program, bv32, definition));
    instructions[fixture.i_result.index()].operation.binary.mode = .primitive;

    instructions[fixture.i_factor.index()].operation.constant.integer = "32";
    instructions[fixture.i_result.index()].operation.binary.operator = .shift_left;
    instructions[fixture.i_result.index()].operation.binary.shift_behavior = .luau_bit32;
    try std.testing.expect(!valid(&program, bv32, definition));
}

test "exact u32 descriptors evaluate primitive bitwise results" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };
    var values = fixture.values;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_factor.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation = .{ .constant = .{ .integer = "305419896" } };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;

    const Case = struct {
        operator: ir.BinaryOperator,
        right: []const u8,
        expected: u32,
    };
    for ([_]Case{
        .{ .operator = .bit_and, .right = "252645135", .expected = 0x02040608 },
        .{ .operator = .bit_or, .right = "252645135", .expected = 0x1f3f5f7f },
        .{ .operator = .bit_xor, .right = "252645135", .expected = 0x1d3b5977 },
        .{ .operator = .shift_left, .right = "4", .expected = 0x23456780 },
        .{ .operator = .shift_right, .right = "4", .expected = 0x01234567 },
    }) |case| {
        instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = case.right } };
        instructions[fixture.i_result.index()].operation = .{ .binary = .{
            .operator = case.operator,
            .left = fixture.v_sum,
            .right = fixture.v_factor,
            .mode = .primitive,
            .shift_behavior = if (case.operator == .shift_left or case.operator == .shift_right) .luau_bit32 else null,
        } };
        try std.testing.expectEqual(case.expected, solver_equivalence.exactPrimitiveBit32Result(&program, fixture.v_result).?);
        const descriptor = solver_equivalence.dynamicValueDescriptor(&program, fixture.v_result).?;
        try std.testing.expectEqual(
            solver_equivalence.DynamicRelation.equivalent,
            solver_equivalence.dynamicDescriptorRelation(descriptor, .{
                .category = .number,
                .exact_number = .{ .number = @floatFromInt(case.expected) },
            }),
        );
    }

    instructions[fixture.i_result.index()].operation = .{ .unary = .{
        .operator = .bit_not,
        .operand = fixture.v_sum,
        .mode = .primitive,
    } };
    try std.testing.expectEqual(@as(u32, 0xedcba987), solver_equivalence.exactPrimitiveBit32Result(&program, fixture.v_result).?);
    instructions[fixture.i_result.index()].operation = .{ .copy = fixture.v_sum };
    try std.testing.expectEqual(@as(u32, 0x12345678), solver_equivalence.exactPrimitiveBit32Result(&program, fixture.v_result).?);

    instructions[fixture.i_sum.index()].operation.constant.integer = "2147483649";
    const ShiftCase = struct {
        count: []const u8,
        bounded_left: ?u32,
        bounded_right: ?u32,
        zero_left: u32,
        zero_right: u32,
    };
    for ([_]ir.ShiftBehavior{ .luau_bit32, .zero_saturating }) |behavior| {
        for ([_]ShiftCase{
            .{ .count = "31", .bounded_left = 0x80000000, .bounded_right = 1, .zero_left = 0x80000000, .zero_right = 1 },
            .{ .count = "32", .bounded_left = null, .bounded_right = null, .zero_left = 0, .zero_right = 0 },
            .{ .count = "2147483648", .bounded_left = null, .bounded_right = null, .zero_left = 0, .zero_right = 0 },
            .{ .count = "4294967295", .bounded_left = null, .bounded_right = null, .zero_left = 0, .zero_right = 0 },
        }) |case| {
            instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = case.count } };
            for ([_]ir.BinaryOperator{ .shift_left, .shift_right }) |operator| {
                instructions[fixture.i_result.index()].operation = .{ .binary = .{
                    .operator = operator,
                    .left = fixture.v_sum,
                    .right = fixture.v_factor,
                    .mode = .primitive,
                    .shift_behavior = behavior,
                } };
                const expected: ?u32 = switch (behavior) {
                    .luau_bit32 => if (operator == .shift_left) case.bounded_left else case.bounded_right,
                    .zero_saturating => if (operator == .shift_left) case.zero_left else case.zero_right,
                };
                try std.testing.expectEqual(expected, solver_equivalence.exactPrimitiveBit32Result(&program, fixture.v_result));
            }
        }
    }
    instructions[fixture.i_factor.index()].operation.constant.integer = "1";
    instructions[fixture.i_result.index()].operation.binary.operator = .shift_left;
    instructions[fixture.i_result.index()].operation.binary.shift_behavior = null;
    try std.testing.expectEqual(@as(?u32, null), solver_equivalence.exactPrimitiveBit32Result(&program, fixture.v_result));
    instructions[fixture.i_result.index()].operation.binary.shift_behavior = .luau_bit32;
    instructions[fixture.i_result.index()].operation.binary.mode = .semantic;
    try std.testing.expectEqual(@as(?u32, null), solver_equivalence.exactPrimitiveBit32Result(&program, fixture.v_result));
    instructions[fixture.i_result.index()].operation.binary.mode = .primitive;
    instructions[fixture.i_result.index()].effects = .dynamic_call;
    try std.testing.expectEqual(@as(?u32, null), solver_equivalence.exactPrimitiveBit32Result(&program, fixture.v_result));
    instructions[fixture.i_result.index()].effects = .pure;
    values[fixture.v_result.index()].type.signed = true;
    try std.testing.expectEqual(@as(?u32, null), solver_equivalence.exactPrimitiveBit32Result(&program, fixture.v_result));
    values[fixture.v_result.index()].type = u32_type;
    values[fixture.v_left.index()].type = u32_type;
    instructions[fixture.i_result.index()].operation.binary.operator = .bit_and;
    instructions[fixture.i_result.index()].operation.binary.right = fixture.v_left;
    try std.testing.expectEqual(@as(?u32, null), solver_equivalence.exactPrimitiveBit32Result(&program, fixture.v_result));
}
