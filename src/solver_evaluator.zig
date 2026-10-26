const std = @import("std");
const ir = @import("ir.zig");
const normalized_value = @import("normalized_value.zig");
const numerals = @import("numerals.zig");
const solver_equivalence = @import("solver_equivalence.zig");

pub const BitVectorConstant = struct {
    value: u64,
    bit_width: u16,
};

pub const Truth = enum {
    true_value,
    false_value,
    unknown,
};

pub const Constant = union(enum) {
    boolean: bool,
    integer: i64,
    real: ir.SolverRational,
    bit_vector: BitVectorConstant,
    unknown: void,
};

pub const NormalizedValueSource = normalized_value.Source;
pub const normalizedValueSource = normalized_value.source;
pub const isExactPure = normalized_value.isExactPure;

pub fn evaluate(program: *const ir.Program, term_id: ir.SolverTermId) Constant {
    return evaluateDepth(program, term_id, 0);
}

pub fn evaluateValue(program: *const ir.Program, value_id: ir.ValueId) Constant {
    return evaluateValueDepth(program, value_id, 0);
}

pub fn evaluateTruth(program: *const ir.Program, term_id: ir.SolverTermId) Truth {
    return switch (evaluate(program, term_id)) {
        .boolean => |value| if (value) .true_value else .false_value,
        else => .unknown,
    };
}

pub fn evaluatesTrue(program: *const ir.Program, term_id: ir.SolverTermId) bool {
    return evaluateTruth(program, term_id) == .true_value;
}

fn evaluateDepth(program: *const ir.Program, term_id: ir.SolverTermId, depth: usize) Constant {
    if (term_id.index() >= program.solver_terms.len) return .{ .unknown = {} };
    if (depth > program.solver_terms.len) return .{ .unknown = {} };

    const term = program.solver_terms[term_id.index()];
    return switch (term.operation) {
        .value => |value_id| coerceValueToSort(evaluateValueDepth(program, value_id, depth + 1), term.sort),
        .value_definition => |definition| exactLuauIntegerConstant(evaluateDepth(program, definition.expression, depth + 1)),
        .semantic_atom => .{ .unknown = {} },
        .dynamic_truthiness => |operand| if (solver_equivalence.dynamicTermTruthiness(program, operand)) |truth|
            .{ .boolean = truth }
        else
            .{ .unknown = {} },
        .dynamic_number_is_nan => |operand| if (solver_equivalence.dynamicTermIsNaN(program, operand)) |is_nan|
            .{ .boolean = is_nan }
        else
            .{ .unknown = {} },
        .boolean_literal => |value| .{ .boolean = value },
        .integer_literal => |value| parseInteger(value),
        .real_literal => |value| parseReal(value),
        .bit_vector_literal => |value| parseBitVector(value),
        .logical_not => |operand| switch (evaluateDepth(program, operand, depth + 1)) {
            .boolean => |value| .{ .boolean = !value },
            else => .{ .unknown = {} },
        },
        .binary => |binary| evaluateSolverBinary(program, binary, depth + 1),
        .if_then_else => |selection| evaluateIfThenElse(program, selection, depth + 1),
        .bit_vector_not => |operand| evaluateBitVectorNot(evaluateDepth(program, operand, depth + 1)),
        .bit_vector_extract => |extract| evaluateBitVectorExtract(
            evaluateDepth(program, extract.operand, depth + 1),
            extract.high,
            extract.low,
        ),
        .bit_vector_concat => |concat| evaluateBitVectorConcat(
            evaluateDepth(program, concat.high, depth + 1),
            evaluateDepth(program, concat.low, depth + 1),
        ),
        .bit_vector_extend => |extension| evaluateBitVectorExtend(
            evaluateDepth(program, extension.operand, depth + 1),
            extension.extra_bits,
            extension.mode,
        ),
        .bit_vector_rotate => |rotation| evaluateBitVectorRotate(
            evaluateDepth(program, rotation.operand, depth + 1),
            evaluateDepth(program, rotation.amount, depth + 1),
            rotation.direction,
        ),
        .integer_to_bit_vector => |operand| switch (evaluateDepth(program, operand, depth + 1)) {
            .integer => |value| integerToBitVector(value, term.sort.bit_width),
            else => .{ .unknown = {} },
        },
        .bit_vector_to_integer => |conversion| evaluateBitVectorToInteger(
            evaluateDepth(program, conversion.operand, depth + 1),
            conversion.signed,
        ),
        .arithmetic_negate => |operand| evaluateArithmeticNegate(evaluateDepth(program, operand, depth + 1)),
        .is_nonzero => |operand| evaluateNonzero(evaluateDepth(program, operand, depth + 1)),
        .division => |division| evaluateDivision(program, division, depth + 1),
        .remainder => |remainder| evaluateRemainder(program, remainder, depth + 1),
    };
}

fn evaluateSolverBinary(program: *const ir.Program, binary: ir.SolverBinary, depth: usize) Constant {
    if (binary.operator == .equal or binary.operator == .not_equal) {
        if (solver_equivalence.termsEquivalent(program, binary.left, binary.right)) {
            return .{ .boolean = binary.operator == .equal };
        }
        if (solver_equivalence.termsDistinct(program, binary.left, binary.right)) {
            return .{ .boolean = binary.operator == .not_equal };
        }
    }
    return evaluateBinary(
        binary.operator,
        evaluateDepth(program, binary.left, depth),
        evaluateDepth(program, binary.right, depth),
        if (binary.left.index() < program.solver_terms.len) program.solver_terms[binary.left.index()].sort else null,
    );
}

fn evaluateIfThenElse(program: *const ir.Program, selection: ir.SolverIfThenElse, depth: usize) Constant {
    switch (evaluateDepth(program, selection.condition, depth)) {
        .boolean => |condition| return evaluateDepth(
            program,
            if (condition) selection.then_term else selection.else_term,
            depth,
        ),
        else => {},
    }
    const then_value = evaluateDepth(program, selection.then_term, depth);
    const else_value = evaluateDepth(program, selection.else_term, depth);
    return if (constantsEqual(then_value, else_value) orelse false)
        then_value
    else
        .{ .unknown = {} };
}

fn coerceValueToSort(value: Constant, sort: ir.SolverSort) Constant {
    return switch (sort.kind) {
        .boolean => switch (value) {
            .boolean => value,
            else => .{ .unknown = {} },
        },
        .integer => switch (value) {
            .integer => value,
            else => .{ .unknown = {} },
        },
        .bit_vector => switch (value) {
            .bit_vector => |bit_vector| if (bit_vector.bit_width == sort.bit_width) value else .{ .unknown = {} },
            .integer => |integer| integerToBitVector(integer, sort.bit_width),
            else => .{ .unknown = {} },
        },
        .real => switch (value) {
            .real => value,
            else => .{ .unknown = {} },
        },
        .dynamic_value => .{ .unknown = {} },
    };
}

fn integerToBitVector(value: i64, bit_width: u16) Constant {
    const mask = bitVectorMask(bit_width) orelse return .{ .unknown = {} };
    const raw: u64 = @bitCast(value);
    return .{ .bit_vector = .{ .value = raw & mask, .bit_width = bit_width } };
}

fn evaluateValueDepth(program: *const ir.Program, value_id: ir.ValueId, depth: usize) Constant {
    if (depth > program.values.len + program.instructions.len) return .{ .unknown = {} };
    const source = normalizedValueSource(program, value_id) orelse return .{ .unknown = {} };
    return switch (source) {
        .constant => |constant| evaluateLiteral(constant.literal),
        .copy => |copy| evaluateValueDepth(program, copy.source, depth + 1),
        .unary => |unary| evaluateNormalizedUnary(program, unary, depth + 1),
        .binary => |binary| evaluateNormalizedBinary(program, binary, depth + 1),
    };
}

fn evaluateNormalizedBinary(
    program: *const ir.Program,
    binary: @FieldType(NormalizedValueSource, "binary"),
    depth: usize,
) Constant {
    if (solver_equivalence.exactPrimitiveBooleanResult(program, .{ .binary = .{
        .operator = binary.operator,
        .left = binary.left,
        .right = binary.right,
    } })) |value| return .{ .boolean = value };
    const operator = normalized_value.solverBinaryOperator(binary.operator) orelse return .{ .unknown = {} };
    return exactLuauIntegerConstant(evaluateBinary(
        operator,
        evaluateValueDepth(program, binary.left, depth),
        evaluateValueDepth(program, binary.right, depth),
        null,
    ));
}

fn evaluateLiteral(literal: ir.Literal) Constant {
    return switch (literal) {
        .boolean => |value| .{ .boolean = value },
        .integer => |value| exactLuauIntegerConstant(parseInteger(value)),
        .nil_value, .number, .special_number, .string => .{ .unknown = {} },
    };
}

/// Luau numbers are IEEE-754 doubles, so an integer payload outside [-2^53, 2^53] has no exact double. Such a
/// payload reads as unknown wherever the exact-integer walk would otherwise return it, for every value type, so a
/// branch is never decided against Luau's double arithmetic.
fn exactLuauIntegerConstant(value: Constant) Constant {
    const limit: i64 = 1 << 53;
    return switch (value) {
        .integer => |payload| if (payload < -limit or payload > limit) .{ .unknown = {} } else value,
        else => value,
    };
}

fn evaluateNormalizedUnary(
    program: *const ir.Program,
    unary: @FieldType(NormalizedValueSource, "unary"),
    depth: usize,
) Constant {
    if (solver_equivalence.exactPrimitiveBooleanResult(program, .{ .unary = .{
        .operator = unary.operator,
        .operand = unary.operand,
    } })) |value| return .{ .boolean = value };
    return switch (unary.operator) {
        .logical_not => switch (evaluateValueDepth(program, unary.operand, depth)) {
            .boolean => |value| .{ .boolean = !value },
            .integer, .real, .bit_vector => .{ .boolean = false },
            .unknown => .{ .unknown = {} },
        },
        .negate => exactLuauIntegerConstant(switch (evaluateValueDepth(program, unary.operand, depth)) {
            .integer => |value| .{ .integer = std.math.sub(i64, 0, value) catch return .{ .unknown = {} } },
            else => .{ .unknown = {} },
        }),
        .length => .{ .integer = std.math.cast(i64, normalized_value.exactStringLength(program, unary.operand) orelse return .{ .unknown = {} }) orelse return .{ .unknown = {} } },
        .bit_not => .{ .unknown = {} },
    };
}

fn parseInteger(decimal: []const u8) Constant {
    const value = std.fmt.parseInt(i64, decimal, 10) catch return .{ .unknown = {} };
    return .{ .integer = value };
}

fn parseReal(value: ir.SolverRational) Constant {
    if (!numerals.isCanonicalSignedDecimal(value.numerator) or
        !numerals.isCanonicalUnsignedDecimal(value.denominator) or
        std.mem.eql(u8, value.denominator, "0"))
    {
        return .{ .unknown = {} };
    }
    return .{ .real = value };
}

fn parseBitVector(literal: ir.BitVectorLiteral) Constant {
    const value = std.fmt.parseInt(u64, literal.value, 10) catch return .{ .unknown = {} };
    return .{ .bit_vector = .{ .value = value, .bit_width = literal.bit_width } };
}

fn evaluateBinary(operator: ir.SolverBinaryOperator, left: Constant, right: Constant, operand_sort: ?ir.SolverSort) Constant {
    return switch (operator) {
        .equal => .{ .boolean = constantsEqual(left, right) orelse return .{ .unknown = {} } },
        .not_equal => .{ .boolean = !(constantsEqual(left, right) orelse return .{ .unknown = {} }) },
        .logical_and => booleanBinary(left, right, true),
        .logical_or => booleanBinary(left, right, false),
        .less => compareConstants(left, right, operand_sort, .less),
        .less_equal => compareConstants(left, right, operand_sort, .less_equal),
        .greater => compareConstants(left, right, operand_sort, .greater),
        .greater_equal => compareConstants(left, right, operand_sort, .greater_equal),
        .add => arithmetic(left, right, .add),
        .subtract => arithmetic(left, right, .subtract),
        .multiply => arithmetic(left, right, .multiply),
        .bit_and => bitVectorBinary(left, right, .bit_and),
        .bit_or => bitVectorBinary(left, right, .bit_or),
        .bit_xor => bitVectorBinary(left, right, .bit_xor),
        .shift_left => bitVectorBinary(left, right, .shift_left),
        .shift_right => blk: {
            const sort = operand_sort orelse break :blk .{ .unknown = {} };
            if (sort.kind != .bit_vector) break :blk .{ .unknown = {} };
            break :blk bitVectorBinary(left, right, if (sort.signed) .shift_right_arithmetic else .shift_right_logical);
        },
    };
}

fn constantsEqual(left: Constant, right: Constant) ?bool {
    return switch (left) {
        .boolean => |left_value| switch (right) {
            .boolean => |right_value| left_value == right_value,
            else => null,
        },
        .integer => |left_value| switch (right) {
            .integer => |right_value| left_value == right_value,
            else => null,
        },
        .real => |left_value| switch (right) {
            .real => |right_value| rationalsEqual(left_value, right_value),
            else => null,
        },
        .bit_vector => |left_value| switch (right) {
            .bit_vector => |right_value| left_value.value == right_value.value and left_value.bit_width == right_value.bit_width,
            else => null,
        },
        .unknown => null,
    };
}

fn evaluateBitVectorNot(operand: Constant) Constant {
    const value = switch (operand) {
        .bit_vector => |bit_vector| bit_vector,
        else => return .{ .unknown = {} },
    };
    const mask = bitVectorMask(value.bit_width) orelse return .{ .unknown = {} };
    return .{ .bit_vector = .{ .value = ~value.value & mask, .bit_width = value.bit_width } };
}

fn evaluateBitVectorExtract(operand: Constant, high: u16, low: u16) Constant {
    const value = switch (operand) {
        .bit_vector => |bit_vector| bit_vector,
        else => return .{ .unknown = {} },
    };
    if (low > high or high >= value.bit_width) return .{ .unknown = {} };
    const result_width_u32 = @as(u32, high) - @as(u32, low) + 1;
    if (result_width_u32 > 64) return .{ .unknown = {} };
    const result_width: u16 = @intCast(result_width_u32);
    const mask = bitVectorMask(result_width) orelse return .{ .unknown = {} };
    const shifted = if (low >= 64) 0 else value.value >> @intCast(low);
    return .{ .bit_vector = .{ .value = shifted & mask, .bit_width = result_width } };
}

fn evaluateBitVectorConcat(high: Constant, low: Constant) Constant {
    const high_value = switch (high) {
        .bit_vector => |bit_vector| bit_vector,
        else => return .{ .unknown = {} },
    };
    const low_value = switch (low) {
        .bit_vector => |bit_vector| bit_vector,
        else => return .{ .unknown = {} },
    };
    const result_width_u32 = @as(u32, high_value.bit_width) + @as(u32, low_value.bit_width);
    if (result_width_u32 == 0 or result_width_u32 > 64 or low_value.bit_width >= 64) return .{ .unknown = {} };
    const result_width: u16 = @intCast(result_width_u32);
    const mask = bitVectorMask(result_width) orelse return .{ .unknown = {} };
    const raw = (high_value.value << @intCast(low_value.bit_width)) | low_value.value;
    return .{ .bit_vector = .{ .value = raw & mask, .bit_width = result_width } };
}

fn evaluateBitVectorExtend(operand: Constant, extra_bits: u16, mode: ir.SolverBitVectorExtension) Constant {
    const value = switch (operand) {
        .bit_vector => |bit_vector| bit_vector,
        else => return .{ .unknown = {} },
    };
    const result_width_u32 = @as(u32, value.bit_width) + @as(u32, extra_bits);
    if (extra_bits == 0 or result_width_u32 > 64) return .{ .unknown = {} };
    const result_width: u16 = @intCast(result_width_u32);
    const result_mask = bitVectorMask(result_width) orelse return .{ .unknown = {} };
    const raw = switch (mode) {
        .zero => value.value,
        .sign => blk: {
            const source_mask = bitVectorMask(value.bit_width) orelse return .{ .unknown = {} };
            const sign_bit = @as(u64, 1) << @intCast(value.bit_width - 1);
            break :blk if (value.value & sign_bit == 0)
                value.value
            else
                value.value | (result_mask ^ source_mask);
        },
    };
    return .{ .bit_vector = .{ .value = raw & result_mask, .bit_width = result_width } };
}

fn evaluateBitVectorRotate(operand: Constant, amount: Constant, direction: ir.SolverBitVectorRotation) Constant {
    const value = switch (operand) {
        .bit_vector => |bit_vector| bit_vector,
        else => return .{ .unknown = {} },
    };
    const amount_value = switch (amount) {
        .bit_vector => |bit_vector| bit_vector,
        else => return .{ .unknown = {} },
    };
    if (value.bit_width != amount_value.bit_width) return .{ .unknown = {} };
    const mask = bitVectorMask(value.bit_width) orelse return .{ .unknown = {} };
    const shift: u16 = @intCast(amount_value.value % @as(u64, value.bit_width));
    if (shift == 0) return .{ .bit_vector = .{ .value = value.value & mask, .bit_width = value.bit_width } };
    const complement: u16 = value.bit_width - shift;
    const raw = switch (direction) {
        .left => (value.value << @intCast(shift)) | (value.value >> @intCast(complement)),
        .right => (value.value >> @intCast(shift)) | (value.value << @intCast(complement)),
    };
    return .{ .bit_vector = .{ .value = raw & mask, .bit_width = value.bit_width } };
}

fn evaluateBitVectorToInteger(operand: Constant, signed: bool) Constant {
    const value = switch (operand) {
        .bit_vector => |bit_vector| bit_vector,
        else => return .{ .unknown = {} },
    };
    const mask = bitVectorMask(value.bit_width) orelse return .{ .unknown = {} };
    const raw = value.value & mask;
    if (!signed) return .{ .integer = std.math.cast(i64, raw) orelse return .{ .unknown = {} } };
    const sign_bit = @as(u64, 1) << @intCast(value.bit_width - 1);
    const extended = if (raw & sign_bit == 0) raw else raw | ~mask;
    return .{ .integer = @bitCast(extended) };
}

fn evaluateArithmeticNegate(operand: Constant) Constant {
    return switch (operand) {
        .integer => |value| .{ .integer = std.math.sub(i64, 0, value) catch return .{ .unknown = {} } },
        .bit_vector => |value| blk: {
            const mask = bitVectorMask(value.bit_width) orelse return .{ .unknown = {} };
            break :blk .{ .bit_vector = .{
                .value = (~value.value +% 1) & mask,
                .bit_width = value.bit_width,
            } };
        },
        .boolean, .real, .unknown => .{ .unknown = {} },
    };
}

fn evaluateNonzero(operand: Constant) Constant {
    return switch (operand) {
        .integer => |value| .{ .boolean = value != 0 },
        .bit_vector => |value| .{ .boolean = value.value != 0 },
        .real => |value| .{ .boolean = rationalSign(value) != .eq },
        .boolean, .unknown => .{ .unknown = {} },
    };
}

fn evaluateDivision(program: *const ir.Program, division: ir.SolverDivision, depth: usize) Constant {
    switch (evaluateDepth(program, division.defined_by, depth)) {
        .boolean => |defined| if (!defined) return .{ .unknown = {} },
        else => return .{ .unknown = {} },
    }
    const left = evaluateDepth(program, division.left, depth);
    const right = evaluateDepth(program, division.right, depth);
    return switch (division.mode) {
        .integer_euclidean => evaluateIntegerEuclideanDivision(left, right),
        .integer_floor => evaluateIntegerFloorDivision(left, right),
        .real => .{ .unknown = {} },
        .bit_vector_unsigned => evaluateBitVectorUnsignedDivision(left, right),
        .bit_vector_signed => evaluateBitVectorSignedDivision(left, right),
    };
}

fn evaluateIntegerFloorDivision(left: Constant, right: Constant) Constant {
    const left_value = switch (left) {
        .integer => |value| value,
        else => return .{ .unknown = {} },
    };
    const right_value = switch (right) {
        .integer => |value| value,
        else => return .{ .unknown = {} },
    };
    if (right_value == 0) return .{ .unknown = {} };
    const quotient = @divFloor(@as(i128, left_value), @as(i128, right_value));
    return .{ .integer = std.math.cast(i64, quotient) orelse return .{ .unknown = {} } };
}

fn evaluateIntegerEuclideanDivision(left: Constant, right: Constant) Constant {
    const left_value = switch (left) {
        .integer => |value| value,
        else => return .{ .unknown = {} },
    };
    const right_value = switch (right) {
        .integer => |value| value,
        else => return .{ .unknown = {} },
    };
    if (right_value == 0) return .{ .unknown = {} };
    const dividend: i128 = left_value;
    const divisor: i128 = right_value;
    const positive_divisor = if (divisor < 0) -divisor else divisor;
    const remainder = @mod(dividend, positive_divisor);
    const quotient = @divExact(dividend - remainder, divisor);
    return .{ .integer = std.math.cast(i64, quotient) orelse return .{ .unknown = {} } };
}

fn evaluateBitVectorUnsignedDivision(left: Constant, right: Constant) Constant {
    const left_value = switch (left) {
        .bit_vector => |value| value,
        else => return .{ .unknown = {} },
    };
    const right_value = switch (right) {
        .bit_vector => |value| value,
        else => return .{ .unknown = {} },
    };
    if (left_value.bit_width != right_value.bit_width) return .{ .unknown = {} };
    const mask = bitVectorMask(left_value.bit_width) orelse return .{ .unknown = {} };
    const divisor = right_value.value & mask;
    if (divisor == 0) return .{ .unknown = {} };
    return .{ .bit_vector = .{
        .value = (left_value.value & mask) / divisor,
        .bit_width = left_value.bit_width,
    } };
}

fn evaluateBitVectorSignedDivision(left: Constant, right: Constant) Constant {
    const left_value = switch (left) {
        .bit_vector => |value| value,
        else => return .{ .unknown = {} },
    };
    const right_value = switch (right) {
        .bit_vector => |value| value,
        else => return .{ .unknown = {} },
    };
    if (left_value.bit_width != right_value.bit_width) return .{ .unknown = {} };
    const dividend = bitVectorSignedValue(left_value) orelse return .{ .unknown = {} };
    const divisor = bitVectorSignedValue(right_value) orelse return .{ .unknown = {} };
    if (divisor == 0) return .{ .unknown = {} };
    if (dividend == minimumSignedValue(left_value.bit_width) and divisor == -1) return .{ .bit_vector = left_value };
    return integerToBitVector(@divTrunc(dividend, divisor), left_value.bit_width);
}

fn bitVectorSignedValue(value: BitVectorConstant) ?i64 {
    const mask = bitVectorMask(value.bit_width) orelse return null;
    const raw = value.value & mask;
    const sign_bit = @as(u64, 1) << @intCast(value.bit_width - 1);
    return @bitCast(if (raw & sign_bit == 0) raw else raw | ~mask);
}

fn minimumSignedValue(bit_width: u16) i64 {
    return if (bit_width == 64)
        std.math.minInt(i64)
    else
        -(@as(i64, 1) << @intCast(bit_width - 1));
}

fn evaluateRemainder(program: *const ir.Program, remainder: ir.SolverRemainder, depth: usize) Constant {
    switch (evaluateDepth(program, remainder.defined_by, depth)) {
        .boolean => |defined| if (!defined) return .{ .unknown = {} },
        else => return .{ .unknown = {} },
    }
    const left = evaluateDepth(program, remainder.left, depth);
    const right = evaluateDepth(program, remainder.right, depth);
    return switch (remainder.mode) {
        .integer_euclidean => evaluateIntegerRemainder(left, right, false),
        .integer_floor => evaluateIntegerRemainder(left, right, true),
        .bit_vector_unsigned => evaluateBitVectorUnsignedRemainder(left, right),
        .bit_vector_signed_dividend => evaluateBitVectorSignedRemainder(left, right, false),
        .bit_vector_signed_divisor => evaluateBitVectorSignedRemainder(left, right, true),
    };
}

fn evaluateIntegerRemainder(left: Constant, right: Constant, follows_divisor: bool) Constant {
    const left_value = switch (left) {
        .integer => |value| value,
        else => return .{ .unknown = {} },
    };
    const right_value = switch (right) {
        .integer => |value| value,
        else => return .{ .unknown = {} },
    };
    if (right_value == 0) return .{ .unknown = {} };
    const divisor: i128 = right_value;
    const positive_divisor = if (divisor < 0) -divisor else divisor;
    const modulo = @mod(@as(i128, left_value), positive_divisor);
    const value = if (follows_divisor and divisor < 0 and modulo != 0)
        modulo - positive_divisor
    else
        modulo;
    return .{ .integer = std.math.cast(i64, value) orelse return .{ .unknown = {} } };
}

fn evaluateBitVectorUnsignedRemainder(left: Constant, right: Constant) Constant {
    const left_value = switch (left) {
        .bit_vector => |value| value,
        else => return .{ .unknown = {} },
    };
    const right_value = switch (right) {
        .bit_vector => |value| value,
        else => return .{ .unknown = {} },
    };
    if (left_value.bit_width != right_value.bit_width) return .{ .unknown = {} };
    const mask = bitVectorMask(left_value.bit_width) orelse return .{ .unknown = {} };
    const divisor = right_value.value & mask;
    if (divisor == 0) return .{ .unknown = {} };
    return .{ .bit_vector = .{
        .value = (left_value.value & mask) % divisor,
        .bit_width = left_value.bit_width,
    } };
}

fn evaluateBitVectorSignedRemainder(left: Constant, right: Constant, follows_divisor: bool) Constant {
    const left_value = switch (left) {
        .bit_vector => |value| value,
        else => return .{ .unknown = {} },
    };
    const right_value = switch (right) {
        .bit_vector => |value| value,
        else => return .{ .unknown = {} },
    };
    if (left_value.bit_width != right_value.bit_width) return .{ .unknown = {} };
    const dividend = bitVectorSignedValue(left_value) orelse return .{ .unknown = {} };
    const divisor = bitVectorSignedValue(right_value) orelse return .{ .unknown = {} };
    if (divisor == 0) return .{ .unknown = {} };
    const signed_remainder = if (dividend == minimumSignedValue(left_value.bit_width) and divisor == -1)
        0
    else
        @rem(dividend, divisor);
    const value = if (follows_divisor and signed_remainder != 0 and ((signed_remainder < 0) != (divisor < 0)))
        signed_remainder + divisor
    else
        signed_remainder;
    return integerToBitVector(value, left_value.bit_width);
}

fn bitVectorMask(bit_width: u16) ?u64 {
    if (bit_width == 0 or bit_width > 64) return null;
    return if (bit_width == 64)
        ~@as(u64, 0)
    else
        (@as(u64, 1) << @intCast(bit_width)) - 1;
}

fn booleanBinary(left: Constant, right: Constant, is_and: bool) Constant {
    const left_value: ?bool = switch (left) {
        .boolean => |value| value,
        else => null,
    };
    const right_value: ?bool = switch (right) {
        .boolean => |value| value,
        else => null,
    };
    if (left_value) |value| if (value != is_and) return .{ .boolean = value };
    if (right_value) |value| if (value != is_and) return .{ .boolean = value };
    if (left_value != null and right_value != null) return .{ .boolean = is_and };
    return .{ .unknown = {} };
}

const Comparison = enum { less, less_equal, greater, greater_equal };

fn compareConstants(left: Constant, right: Constant, operand_sort: ?ir.SolverSort, comparison: Comparison) Constant {
    return switch (left) {
        .integer => |left_value| switch (right) {
            .integer => |right_value| .{ .boolean = compareValues(left_value, right_value, comparison) },
            else => .{ .unknown = {} },
        },
        .bit_vector => |left_value| switch (right) {
            .bit_vector => |right_value| blk: {
                if (left_value.bit_width != right_value.bit_width) break :blk .{ .unknown = {} };
                const sort = operand_sort orelse break :blk .{ .unknown = {} };
                if (sort.kind != .bit_vector or sort.bit_width != left_value.bit_width) break :blk .{ .unknown = {} };
                if (sort.signed) {
                    const left_signed = bitVectorSignedValue(left_value) orelse break :blk .{ .unknown = {} };
                    const right_signed = bitVectorSignedValue(right_value) orelse break :blk .{ .unknown = {} };
                    break :blk .{ .boolean = compareValues(left_signed, right_signed, comparison) };
                }
                const mask = bitVectorMask(left_value.bit_width) orelse break :blk .{ .unknown = {} };
                break :blk .{ .boolean = compareValues(left_value.value & mask, right_value.value & mask, comparison) };
            },
            else => .{ .unknown = {} },
        },
        .real => |left_value| switch (right) {
            .real => |right_value| if (compareRationals(left_value, right_value)) |order|
                .{ .boolean = compareOrder(order, comparison) }
            else
                .{ .unknown = {} },
            else => .{ .unknown = {} },
        },
        .boolean, .unknown => .{ .unknown = {} },
    };
}

fn rationalsEqual(left: ir.SolverRational, right: ir.SolverRational) ?bool {
    const left_sign = rationalSign(left);
    const right_sign = rationalSign(right);
    if (left_sign == .eq or right_sign == .eq) return left_sign == right_sign;
    if (left_sign != right_sign) return false;
    if (std.mem.eql(u8, left.numerator, right.numerator) and
        std.mem.eql(u8, left.denominator, right.denominator)) return true;
    return null;
}

fn compareRationals(left: ir.SolverRational, right: ir.SolverRational) ?std.math.Order {
    if (rationalsEqual(left, right)) |equal| if (equal) return .eq;
    const left_sign = rationalSign(left);
    const right_sign = rationalSign(right);
    if (left_sign == .eq) return switch (right_sign) {
        .lt => .gt,
        .eq => .eq,
        .gt => .lt,
    };
    if (right_sign == .eq or left_sign != right_sign) return left_sign;
    return null;
}

fn rationalSign(value: ir.SolverRational) std.math.Order {
    if (std.mem.eql(u8, value.numerator, "0")) return .eq;
    return if (value.numerator[0] == '-') .lt else .gt;
}

fn compareOrder(order: std.math.Order, comparison: Comparison) bool {
    return switch (comparison) {
        .less => order == .lt,
        .less_equal => order != .gt,
        .greater => order == .gt,
        .greater_equal => order != .lt,
    };
}

fn compareValues(left: anytype, right: @TypeOf(left), comparison: Comparison) bool {
    return switch (comparison) {
        .less => left < right,
        .less_equal => left <= right,
        .greater => left > right,
        .greater_equal => left >= right,
    };
}

const Arithmetic = enum { add, subtract, multiply };

fn arithmetic(left: Constant, right: Constant, operation: Arithmetic) Constant {
    return switch (left) {
        .integer => integerArithmetic(left, right, operation),
        .bit_vector => bitVectorArithmetic(left, right, operation),
        .boolean, .real, .unknown => .{ .unknown = {} },
    };
}

fn integerArithmetic(left: Constant, right: Constant, operation: Arithmetic) Constant {
    const left_value = switch (left) {
        .integer => |value| value,
        else => return .{ .unknown = {} },
    };
    const right_value = switch (right) {
        .integer => |value| value,
        else => return .{ .unknown = {} },
    };
    const value = switch (operation) {
        .add => std.math.add(i64, left_value, right_value) catch return .{ .unknown = {} },
        .subtract => std.math.sub(i64, left_value, right_value) catch return .{ .unknown = {} },
        .multiply => std.math.mul(i64, left_value, right_value) catch return .{ .unknown = {} },
    };
    return .{ .integer = value };
}

fn bitVectorArithmetic(left: Constant, right: Constant, operation: Arithmetic) Constant {
    const left_value = switch (left) {
        .bit_vector => |value| value,
        else => return .{ .unknown = {} },
    };
    const right_value = switch (right) {
        .bit_vector => |value| value,
        else => return .{ .unknown = {} },
    };
    if (left_value.bit_width != right_value.bit_width) return .{ .unknown = {} };
    const mask = bitVectorMask(left_value.bit_width) orelse return .{ .unknown = {} };
    const left_raw = left_value.value & mask;
    const right_raw = right_value.value & mask;
    const raw_value = switch (operation) {
        .add => left_raw +% right_raw,
        .subtract => left_raw -% right_raw,
        .multiply => left_raw *% right_raw,
    };
    return .{ .bit_vector = .{
        .value = raw_value & mask,
        .bit_width = left_value.bit_width,
    } };
}

const BitOperation = enum { bit_and, bit_or, bit_xor, shift_left, shift_right_logical, shift_right_arithmetic };

fn bitVectorBinary(left: Constant, right: Constant, operation: BitOperation) Constant {
    const left_value = switch (left) {
        .bit_vector => |value| value,
        else => return .{ .unknown = {} },
    };
    const right_value = switch (right) {
        .bit_vector => |value| value,
        else => return .{ .unknown = {} },
    };
    if (left_value.bit_width != right_value.bit_width) return .{ .unknown = {} };
    const mask = bitVectorMask(left_value.bit_width) orelse return .{ .unknown = {} };
    const left_raw = left_value.value & mask;
    const shift_amount = right_value.value & mask;
    const oversized_shift = shift_amount >= left_value.bit_width;
    const shift: u6 = if (oversized_shift) 0 else @intCast(shift_amount);
    const raw_value = switch (operation) {
        .bit_and => left_raw & right_value.value,
        .bit_or => left_raw | right_value.value,
        .bit_xor => left_raw ^ right_value.value,
        .shift_left => if (oversized_shift) 0 else left_raw << shift,
        .shift_right_logical => if (oversized_shift) 0 else left_raw >> shift,
        .shift_right_arithmetic => arithmeticRightShift(left_raw, left_value.bit_width, shift_amount, mask),
    };
    return .{ .bit_vector = .{ .value = raw_value & mask, .bit_width = left_value.bit_width } };
}

fn arithmeticRightShift(value: u64, bit_width: u16, amount: u64, mask: u64) u64 {
    const sign_bit = @as(u64, 1) << @intCast(bit_width - 1);
    if (amount >= bit_width) return if (value & sign_bit == 0) 0 else mask;
    if (amount == 0) return value;
    const shift: u6 = @intCast(amount);
    const shifted = value >> shift;
    if (value & sign_bit == 0) return shifted;
    return shifted | (mask ^ (mask >> shift));
}
