const std = @import("std");
const ir = @import("ir.zig");

const BigInt = std.math.big.int.Managed;

pub const Error = std.mem.Allocator.Error || error{InvalidValue};

pub const Rational = struct {
    numerator: *BigInt,
    denominator: *BigInt,
};

pub const BitVector = struct {
    value: *BigInt,
    bit_width: u16,
};

pub const Value = union(enum) {
    unknown: void,
    boolean: bool,
    integer: *BigInt,
    real: Rational,
    bit_vector: BitVector,
    dynamic_identity: u32,
};

pub const Context = struct {
    allocator: std.mem.Allocator,

    pub fn fromModel(self: Context, value: ir.SolverModelValue) Error!Value {
        return switch (value) {
            .boolean => |boolean| .{ .boolean = boolean },
            .integer => |integer| .{ .integer = try self.parseInt(integer) },
            .real => |real| try self.realLiteral(real),
            .bit_vector => |bit_vector| try self.bitVectorLiteral(bit_vector),
            .dynamic_identity => |identity| .{ .dynamic_identity = identity },
        };
    }

    pub fn booleanValue(_: Context, value: bool) Value {
        return .{ .boolean = value };
    }

    pub fn integerLiteral(self: Context, decimal: []const u8) Error!Value {
        return .{ .integer = try self.parseInt(decimal) };
    }

    pub fn realLiteral(self: Context, literal: ir.SolverRational) Error!Value {
        const numerator = try self.parseInt(literal.numerator);
        const denominator = try self.parseInt(literal.denominator);
        if (denominator.eqlZero()) return error.InvalidValue;
        try normalizeRationalSign(numerator, denominator);
        return .{ .real = .{ .numerator = numerator, .denominator = denominator } };
    }

    pub fn bitVectorLiteral(self: Context, literal: ir.BitVectorLiteral) Error!Value {
        if (literal.bit_width == 0) return error.InvalidValue;
        const raw = try self.parseInt(literal.value);
        return .{ .bit_vector = .{
            .value = try self.normalizeBitVector(raw, literal.bit_width),
            .bit_width = literal.bit_width,
        } };
    }

    pub fn integerToBitVector(self: Context, operand: Value, bit_width: u16) Error!Value {
        const integer = switch (operand) {
            .integer => |value| value,
            else => return unknown(),
        };
        if (bit_width == 0) return error.InvalidValue;
        return .{ .bit_vector = .{
            .value = try self.normalizeBitVector(integer, bit_width),
            .bit_width = bit_width,
        } };
    }

    pub fn bitVectorToInteger(self: Context, operand: Value, signed: bool) Error!Value {
        const bit_vector = switch (operand) {
            .bit_vector => |value| value,
            else => return unknown(),
        };
        return .{ .integer = if (signed)
            try self.signedBitVector(bit_vector)
        else
            try self.cloneInt(bit_vector.value) };
    }

    pub fn logicalNot(_: Context, operand: Value) Value {
        return switch (operand) {
            .boolean => |value| .{ .boolean = !value },
            else => unknown(),
        };
    }

    pub fn binary(
        self: Context,
        operator: ir.SolverBinaryOperator,
        operand_sort: ir.SolverSort,
        left: Value,
        right: Value,
    ) Error!Value {
        return switch (operator) {
            .equal => .{ .boolean = (try self.eql(left, right)) orelse return unknown() },
            .not_equal => .{ .boolean = !((try self.eql(left, right)) orelse return unknown()) },
            .less, .less_equal, .greater, .greater_equal => try self.compare(operator, operand_sort, left, right),
            .logical_and => booleanBinary(left, right, true),
            .logical_or => booleanBinary(left, right, false),
            .add, .subtract, .multiply => try self.arithmetic(operator, left, right),
            .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => try self.bitOperation(operator, operand_sort, left, right),
        };
    }

    pub fn select(self: Context, condition: Value, then_value: Value, else_value: Value) Error!Value {
        return switch (condition) {
            .boolean => |value| if (value) then_value else else_value,
            else => if ((try self.eql(then_value, else_value)) orelse false) then_value else unknown(),
        };
    }

    pub fn bitVectorNot(self: Context, operand: Value) Error!Value {
        const value = switch (operand) {
            .bit_vector => |bit_vector| bit_vector,
            else => return unknown(),
        };
        const mask = try self.bitVectorMask(value.bit_width);
        const result = try self.allocInt();
        try BigInt.bitXor(result, value.value, mask);
        return .{ .bit_vector = .{ .value = result, .bit_width = value.bit_width } };
    }

    pub fn bitVectorExtract(self: Context, operand: Value, high: u16, low: u16) Error!Value {
        const value = switch (operand) {
            .bit_vector => |bit_vector| bit_vector,
            else => return unknown(),
        };
        if (low > high or high >= value.bit_width) return error.InvalidValue;
        const shifted = try self.allocInt();
        try BigInt.shiftRight(shifted, value.value, low);
        const result_width: u16 = @intCast(@as(u32, high) - @as(u32, low) + 1);
        return .{ .bit_vector = .{
            .value = try self.normalizeBitVector(shifted, result_width),
            .bit_width = result_width,
        } };
    }

    pub fn bitVectorConcat(self: Context, high: Value, low: Value) Error!Value {
        const high_value = switch (high) {
            .bit_vector => |value| value,
            else => return unknown(),
        };
        const low_value = switch (low) {
            .bit_vector => |value| value,
            else => return unknown(),
        };
        const result_width_u32 = @as(u32, high_value.bit_width) + @as(u32, low_value.bit_width);
        if (result_width_u32 == 0 or result_width_u32 > std.math.maxInt(u16)) return error.InvalidValue;
        const shifted = try self.allocInt();
        try BigInt.shiftLeft(shifted, high_value.value, low_value.bit_width);
        const result = try self.allocInt();
        try BigInt.bitOr(result, shifted, low_value.value);
        return .{ .bit_vector = .{
            .value = result,
            .bit_width = @intCast(result_width_u32),
        } };
    }

    pub fn bitVectorExtend(self: Context, operand: Value, extra_bits: u16, mode: ir.SolverBitVectorExtension) Error!Value {
        const value = switch (operand) {
            .bit_vector => |bit_vector| bit_vector,
            else => return unknown(),
        };
        const result_width_u32 = @as(u32, value.bit_width) + @as(u32, extra_bits);
        if (extra_bits == 0 or result_width_u32 > std.math.maxInt(u16)) return error.InvalidValue;
        const source = switch (mode) {
            .zero => value.value,
            .sign => try self.signedBitVector(value),
        };
        const result_width: u16 = @intCast(result_width_u32);
        return .{ .bit_vector = .{
            .value = try self.normalizeBitVector(source, result_width),
            .bit_width = result_width,
        } };
    }

    pub fn bitVectorRotate(self: Context, operand: Value, amount: Value, direction: ir.SolverBitVectorRotation) Error!Value {
        const value = switch (operand) {
            .bit_vector => |bit_vector| bit_vector,
            else => return unknown(),
        };
        const amount_value = switch (amount) {
            .bit_vector => |bit_vector| bit_vector,
            else => return unknown(),
        };
        if (value.bit_width != amount_value.bit_width) return error.InvalidValue;
        const shift = try self.rotateAmount(amount_value.value, value.bit_width);
        if (shift == 0) return operand;
        const complement = @as(usize, value.bit_width) - shift;
        const first = try self.allocInt();
        const second = try self.allocInt();
        switch (direction) {
            .left => {
                try BigInt.shiftLeft(first, value.value, shift);
                try BigInt.shiftRight(second, value.value, complement);
            },
            .right => {
                try BigInt.shiftRight(first, value.value, shift);
                try BigInt.shiftLeft(second, value.value, complement);
            },
        }
        const combined = try self.allocInt();
        try BigInt.bitOr(combined, first, second);
        return .{ .bit_vector = .{
            .value = try self.normalizeBitVector(combined, value.bit_width),
            .bit_width = value.bit_width,
        } };
    }

    pub fn negate(self: Context, operand: Value) Error!Value {
        return switch (operand) {
            .integer => |integer| .{ .integer = try self.negated(integer) },
            .real => |real_value| .{ .real = .{
                .numerator = try self.negated(real_value.numerator),
                .denominator = real_value.denominator,
            } },
            .bit_vector => |bit_vector| blk: {
                const negated_value = try self.negated(bit_vector.value);
                break :blk .{ .bit_vector = .{
                    .value = try self.normalizeBitVector(negated_value, bit_vector.bit_width),
                    .bit_width = bit_vector.bit_width,
                } };
            },
            else => unknown(),
        };
    }

    pub fn isNonzero(_: Context, operand: Value) Value {
        return switch (operand) {
            .integer => |integer| .{ .boolean = !integer.eqlZero() },
            .real => |real_value| .{ .boolean = !real_value.numerator.eqlZero() },
            .bit_vector => |bit_vector| .{ .boolean = !bit_vector.value.eqlZero() },
            else => unknown(),
        };
    }

    pub fn division(
        self: Context,
        mode: ir.SolverDivisionMode,
        left: Value,
        right: Value,
        defined_by: Value,
    ) Error!Value {
        if (!isTrue(defined_by)) return unknown();
        return switch (mode) {
            .integer_euclidean => try self.integerDivision(left, right, true),
            .integer_floor => try self.integerDivision(left, right, false),
            .real => try self.realDivision(left, right),
            .bit_vector_unsigned => try self.bitVectorDivision(left, right, false),
            .bit_vector_signed => try self.bitVectorDivision(left, right, true),
        };
    }

    pub fn remainder(
        self: Context,
        mode: ir.SolverRemainderMode,
        left: Value,
        right: Value,
        defined_by: Value,
    ) Error!Value {
        if (!isTrue(defined_by)) return unknown();
        return switch (mode) {
            .integer_euclidean => try self.integerRemainder(left, right, true),
            .integer_floor => try self.integerRemainder(left, right, false),
            .bit_vector_unsigned => try self.bitVectorRemainder(left, right, .unsigned),
            .bit_vector_signed_dividend => try self.bitVectorRemainder(left, right, .signed_dividend),
            .bit_vector_signed_divisor => try self.bitVectorRemainder(left, right, .signed_divisor),
        };
    }

    pub fn eql(self: Context, left: Value, right: Value) Error!?bool {
        return switch (left) {
            .unknown => null,
            .boolean => |left_value| switch (right) {
                .boolean => |right_value| left_value == right_value,
                else => null,
            },
            .integer => |left_value| switch (right) {
                .integer => |right_value| BigInt.eql(left_value.*, right_value.*),
                else => null,
            },
            .real => |left_value| switch (right) {
                .real => |right_value| (try self.compareRationals(left_value, right_value)) == .eq,
                else => null,
            },
            .bit_vector => |left_value| switch (right) {
                .bit_vector => |right_value| left_value.bit_width == right_value.bit_width and
                    BigInt.eql(left_value.value.*, right_value.value.*),
                else => null,
            },
            .dynamic_identity => |left_value| switch (right) {
                .dynamic_identity => |right_value| left_value == right_value,
                else => null,
            },
        };
    }

    fn compare(
        self: Context,
        operator: ir.SolverBinaryOperator,
        operand_sort: ir.SolverSort,
        left: Value,
        right: Value,
    ) Error!Value {
        const order = switch (left) {
            .integer => |left_value| switch (right) {
                .integer => |right_value| BigInt.order(left_value.*, right_value.*),
                else => return unknown(),
            },
            .real => |left_value| switch (right) {
                .real => |right_value| try self.compareRationals(left_value, right_value),
                else => return unknown(),
            },
            .bit_vector => |left_value| switch (right) {
                .bit_vector => |right_value| blk: {
                    if (left_value.bit_width != right_value.bit_width or
                        operand_sort.kind != .bit_vector or
                        operand_sort.bit_width != left_value.bit_width)
                    {
                        return unknown();
                    }
                    if (operand_sort.signed) {
                        const left_signed = try self.signedBitVector(left_value);
                        const right_signed = try self.signedBitVector(right_value);
                        break :blk BigInt.order(left_signed.*, right_signed.*);
                    }
                    break :blk BigInt.order(left_value.value.*, right_value.value.*);
                },
                else => return unknown(),
            },
            else => return unknown(),
        };
        return .{ .boolean = switch (operator) {
            .less => order == .lt,
            .less_equal => order != .gt,
            .greater => order == .gt,
            .greater_equal => order != .lt,
            else => return error.InvalidValue,
        } };
    }

    fn arithmetic(self: Context, operator: ir.SolverBinaryOperator, left: Value, right: Value) Error!Value {
        return switch (left) {
            .integer => |left_value| switch (right) {
                .integer => |right_value| .{ .integer = try self.integerArithmetic(operator, left_value, right_value) },
                else => unknown(),
            },
            .real => |left_value| switch (right) {
                .real => |right_value| .{ .real = try self.rationalArithmetic(operator, left_value, right_value) },
                else => unknown(),
            },
            .bit_vector => |left_value| switch (right) {
                .bit_vector => |right_value| try self.bitVectorArithmetic(operator, left_value, right_value),
                else => unknown(),
            },
            else => unknown(),
        };
    }

    fn integerArithmetic(self: Context, operator: ir.SolverBinaryOperator, left: *BigInt, right: *BigInt) Error!*BigInt {
        const result = try self.allocInt();
        switch (operator) {
            .add => try BigInt.add(result, left, right),
            .subtract => try BigInt.sub(result, left, right),
            .multiply => try BigInt.mul(result, left, right),
            else => return error.InvalidValue,
        }
        return result;
    }

    fn rationalArithmetic(self: Context, operator: ir.SolverBinaryOperator, left: Rational, right: Rational) Error!Rational {
        if (operator == .multiply) {
            return .{
                .numerator = try self.integerArithmetic(.multiply, left.numerator, right.numerator),
                .denominator = try self.integerArithmetic(.multiply, left.denominator, right.denominator),
            };
        }
        const left_scaled = try self.integerArithmetic(.multiply, left.numerator, right.denominator);
        const right_scaled = try self.integerArithmetic(.multiply, right.numerator, left.denominator);
        const numerator = try self.integerArithmetic(operator, left_scaled, right_scaled);
        const denominator = try self.integerArithmetic(.multiply, left.denominator, right.denominator);
        return .{ .numerator = numerator, .denominator = denominator };
    }

    fn bitVectorArithmetic(self: Context, operator: ir.SolverBinaryOperator, left: BitVector, right: BitVector) Error!Value {
        if (left.bit_width != right.bit_width) return unknown();
        const raw = try self.integerArithmetic(operator, left.value, right.value);
        return .{ .bit_vector = .{
            .value = try self.normalizeBitVector(raw, left.bit_width),
            .bit_width = left.bit_width,
        } };
    }

    fn bitOperation(
        self: Context,
        operator: ir.SolverBinaryOperator,
        operand_sort: ir.SolverSort,
        left: Value,
        right: Value,
    ) Error!Value {
        const left_value = switch (left) {
            .bit_vector => |bit_vector| bit_vector,
            else => return unknown(),
        };
        const right_value = switch (right) {
            .bit_vector => |bit_vector| bit_vector,
            else => return unknown(),
        };
        if (left_value.bit_width != right_value.bit_width or
            operand_sort.kind != .bit_vector or
            operand_sort.bit_width != left_value.bit_width)
        {
            return unknown();
        }
        const raw = switch (operator) {
            .bit_and, .bit_or, .bit_xor => blk: {
                const result = try self.allocInt();
                switch (operator) {
                    .bit_and => try BigInt.bitAnd(result, left_value.value, right_value.value),
                    .bit_or => try BigInt.bitOr(result, left_value.value, right_value.value),
                    .bit_xor => try BigInt.bitXor(result, left_value.value, right_value.value),
                    else => unreachable,
                }
                break :blk result;
            },
            .shift_left, .shift_right => try self.shiftBitVector(operator, operand_sort.signed, left_value, right_value.value),
            else => return error.InvalidValue,
        };
        return .{ .bit_vector = .{
            .value = try self.normalizeBitVector(raw, left_value.bit_width),
            .bit_width = left_value.bit_width,
        } };
    }

    fn shiftBitVector(
        self: Context,
        operator: ir.SolverBinaryOperator,
        signed: bool,
        left: BitVector,
        amount: *BigInt,
    ) Error!*BigInt {
        const order = amount.toConst().orderAgainstScalar(left.bit_width);
        if (order != .lt) {
            if (operator == .shift_right and signed and try self.bitVectorIsNegative(left)) {
                return self.bitVectorMask(left.bit_width);
            }
            return self.intFromScalar(0);
        }
        const shift = amount.toInt(usize) catch return error.InvalidValue;
        const result = try self.allocInt();
        switch (operator) {
            .shift_left => try BigInt.shiftLeft(result, left.value, shift),
            .shift_right => if (signed) {
                const signed_value = try self.signedBitVector(left);
                try BigInt.shiftRight(result, signed_value, shift);
            } else {
                try BigInt.shiftRight(result, left.value, shift);
            },
            else => return error.InvalidValue,
        }
        return result;
    }

    fn integerDivision(self: Context, left: Value, right: Value, euclidean: bool) Error!Value {
        const left_value = switch (left) {
            .integer => |integer| integer,
            else => return unknown(),
        };
        const right_value = switch (right) {
            .integer => |integer| integer,
            else => return unknown(),
        };
        if (right_value.eqlZero()) return unknown();
        var divisor = right_value;
        if (euclidean and isNegative(divisor)) divisor = try self.negated(divisor);
        const quotient = try self.allocInt();
        const remainder_value = try self.allocInt();
        try BigInt.divFloor(quotient, remainder_value, left_value, divisor);
        if (euclidean and isNegative(right_value) and !quotient.eqlZero()) quotient.negate();
        return .{ .integer = quotient };
    }

    fn integerRemainder(self: Context, left: Value, right: Value, euclidean: bool) Error!Value {
        const left_value = switch (left) {
            .integer => |integer| integer,
            else => return unknown(),
        };
        const right_value = switch (right) {
            .integer => |integer| integer,
            else => return unknown(),
        };
        if (right_value.eqlZero()) return unknown();
        var divisor = right_value;
        if (euclidean and isNegative(divisor)) divisor = try self.negated(divisor);
        const quotient = try self.allocInt();
        const remainder_value = try self.allocInt();
        try BigInt.divFloor(quotient, remainder_value, left_value, divisor);
        return .{ .integer = remainder_value };
    }

    fn realDivision(self: Context, left: Value, right: Value) Error!Value {
        const left_value = switch (left) {
            .real => |real_value| real_value,
            else => return unknown(),
        };
        const right_value = switch (right) {
            .real => |real_value| real_value,
            else => return unknown(),
        };
        if (right_value.numerator.eqlZero()) return unknown();
        const numerator = try self.integerArithmetic(.multiply, left_value.numerator, right_value.denominator);
        const denominator = try self.integerArithmetic(.multiply, left_value.denominator, right_value.numerator);
        try normalizeRationalSign(numerator, denominator);
        return .{ .real = .{ .numerator = numerator, .denominator = denominator } };
    }

    fn bitVectorDivision(self: Context, left: Value, right: Value, signed: bool) Error!Value {
        const pair = bitVectorPair(left, right) orelse return unknown();
        if (pair.right.value.eqlZero()) return unknown();
        const dividend = if (signed) try self.signedBitVector(pair.left) else pair.left.value;
        const divisor = if (signed) try self.signedBitVector(pair.right) else pair.right.value;
        const quotient = try self.allocInt();
        const remainder_value = try self.allocInt();
        try BigInt.divTrunc(quotient, remainder_value, dividend, divisor);
        return .{ .bit_vector = .{
            .value = try self.normalizeBitVector(quotient, pair.left.bit_width),
            .bit_width = pair.left.bit_width,
        } };
    }

    const SignedRemainder = enum { unsigned, signed_dividend, signed_divisor };

    fn bitVectorRemainder(self: Context, left: Value, right: Value, mode: SignedRemainder) Error!Value {
        const pair = bitVectorPair(left, right) orelse return unknown();
        if (pair.right.value.eqlZero()) return unknown();
        const signed = mode != .unsigned;
        const dividend = if (signed) try self.signedBitVector(pair.left) else pair.left.value;
        const divisor = if (signed) try self.signedBitVector(pair.right) else pair.right.value;
        const quotient = try self.allocInt();
        const remainder_value = try self.allocInt();
        if (mode == .signed_divisor) {
            try BigInt.divFloor(quotient, remainder_value, dividend, divisor);
        } else {
            try BigInt.divTrunc(quotient, remainder_value, dividend, divisor);
        }
        return .{ .bit_vector = .{
            .value = try self.normalizeBitVector(remainder_value, pair.left.bit_width),
            .bit_width = pair.left.bit_width,
        } };
    }

    fn compareRationals(self: Context, left: Rational, right: Rational) Error!std.math.Order {
        const left_scaled = try self.integerArithmetic(.multiply, left.numerator, right.denominator);
        const right_scaled = try self.integerArithmetic(.multiply, right.numerator, left.denominator);
        return BigInt.order(left_scaled.*, right_scaled.*);
    }

    fn normalizeBitVector(self: Context, value: *BigInt, bit_width: u16) Error!*BigInt {
        if (bit_width == 0) return error.InvalidValue;
        const modulus = try self.bitVectorModulus(bit_width);
        const quotient = try self.allocInt();
        const remainder_value = try self.allocInt();
        try BigInt.divFloor(quotient, remainder_value, value, modulus);
        return remainder_value;
    }

    fn bitVectorModulus(self: Context, bit_width: u16) Error!*BigInt {
        const modulus = try self.intFromScalar(1);
        try BigInt.shiftLeft(modulus, modulus, bit_width);
        return modulus;
    }

    fn bitVectorMask(self: Context, bit_width: u16) Error!*BigInt {
        const mask = try self.bitVectorModulus(bit_width);
        try BigInt.addScalar(mask, mask, -1);
        return mask;
    }

    fn signedBitVector(self: Context, value: BitVector) Error!*BigInt {
        const result = try self.cloneInt(value.value);
        if (!try self.bitVectorIsNegative(value)) return result;
        const modulus = try self.bitVectorModulus(value.bit_width);
        try BigInt.sub(result, result, modulus);
        return result;
    }

    fn bitVectorIsNegative(self: Context, value: BitVector) Error!bool {
        const sign_bit = try self.intFromScalar(1);
        try BigInt.shiftLeft(sign_bit, sign_bit, value.bit_width - 1);
        return BigInt.order(value.value.*, sign_bit.*) != .lt;
    }

    fn rotateAmount(self: Context, value: *BigInt, bit_width: u16) Error!usize {
        const divisor = try self.intFromScalar(bit_width);
        const quotient = try self.allocInt();
        const remainder_value = try self.allocInt();
        try BigInt.divTrunc(quotient, remainder_value, value, divisor);
        return remainder_value.toInt(usize) catch error.InvalidValue;
    }

    fn parseInt(self: Context, decimal: []const u8) Error!*BigInt {
        const value = try self.allocInt();
        value.setString(10, decimal) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.InvalidValue,
        };
        return value;
    }

    fn intFromScalar(self: Context, value: anytype) Error!*BigInt {
        const result = try self.allocInt();
        try result.set(value);
        return result;
    }

    fn cloneInt(self: Context, value: *const BigInt) Error!*BigInt {
        const result = try self.allocInt();
        try result.copy(value.toConst());
        return result;
    }

    fn negated(self: Context, value: *const BigInt) Error!*BigInt {
        const result = try self.cloneInt(value);
        if (!result.eqlZero()) result.negate();
        return result;
    }

    fn allocInt(self: Context) Error!*BigInt {
        const result = try self.allocator.create(BigInt);
        errdefer self.allocator.destroy(result);
        result.* = try BigInt.init(self.allocator);
        return result;
    }
};

pub fn unknown() Value {
    return .{ .unknown = {} };
}

pub fn isUnknown(value: Value) bool {
    return std.meta.activeTag(value) == .unknown;
}

pub fn truth(value: Value) ?bool {
    return switch (value) {
        .boolean => |boolean| boolean,
        else => null,
    };
}

fn isTrue(value: Value) bool {
    return truth(value) orelse false;
}

fn booleanBinary(left: Value, right: Value, is_and: bool) Value {
    const left_value = truth(left);
    const right_value = truth(right);
    if (left_value) |value| if (value != is_and) return .{ .boolean = value };
    if (right_value) |value| if (value != is_and) return .{ .boolean = value };
    if (left_value != null and right_value != null) return .{ .boolean = is_and };
    return unknown();
}

fn normalizeRationalSign(numerator: *BigInt, denominator: *BigInt) Error!void {
    if (!isNegative(denominator)) return;
    denominator.negate();
    if (!numerator.eqlZero()) numerator.negate();
}

fn isNegative(value: *const BigInt) bool {
    return !value.isPositive() and !value.eqlZero();
}

const BitVectorPair = struct { left: BitVector, right: BitVector };

fn bitVectorPair(left: Value, right: Value) ?BitVectorPair {
    const left_value = switch (left) {
        .bit_vector => |value| value,
        else => return null,
    };
    const right_value = switch (right) {
        .bit_vector => |value| value,
        else => return null,
    };
    if (left_value.bit_width != right_value.bit_width) return null;
    return .{ .left = left_value, .right = right_value };
}
