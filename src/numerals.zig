const std = @import("std");
const ir = @import("ir.zig");

pub fn exactF64RationalAlloc(allocator: std.mem.Allocator, value: f64) std.mem.Allocator.Error!?ir.SolverRational {
    if (!std.math.isFinite(value)) return null;
    const bits: u64 = @bitCast(value);
    const fraction_mask = (@as(u64, 1) << 52) - 1;
    const fraction = bits & fraction_mask;
    const exponent_bits: u16 = @intCast((bits >> 52) & 0x7ff);
    var significand: u64 = if (exponent_bits == 0) fraction else fraction | (@as(u64, 1) << 52);
    if (significand == 0) {
        const numerator = try allocator.dupe(u8, "0");
        errdefer allocator.free(numerator);
        return .{
            .numerator = numerator,
            .denominator = try allocator.dupe(u8, "1"),
        };
    }

    var exponent: i32 = if (exponent_bits == 0)
        -1074
    else
        @as(i32, exponent_bits) - 1023 - 52;
    var denominator_shift: u16 = 0;
    if (exponent < 0) {
        denominator_shift = @intCast(-exponent);
        const reduction: u16 = @min(@as(u16, @intCast(@ctz(significand))), denominator_shift);
        significand >>= @intCast(reduction);
        denominator_shift -= reduction;
        exponent = 0;
    }

    const BigInt = std.math.big.int.Managed;
    var numerator = try BigInt.init(allocator);
    defer numerator.deinit();
    try numerator.set(significand);
    if (exponent > 0) try BigInt.shiftLeft(&numerator, &numerator, @intCast(exponent));
    if (bits >> 63 != 0) numerator.negate();
    const numerator_text = try managedDecimalAlloc(allocator, &numerator);
    errdefer allocator.free(numerator_text);

    var denominator = try BigInt.init(allocator);
    defer denominator.deinit();
    try denominator.set(1);
    if (denominator_shift > 0) try BigInt.shiftLeft(&denominator, &denominator, denominator_shift);
    return .{
        .numerator = numerator_text,
        .denominator = try managedDecimalAlloc(allocator, &denominator),
    };
}

pub fn rationalExactlyRepresentsF64(rational: ir.SolverRational, value: f64) bool {
    var storage: [8192]u8 = undefined;
    var fixed = std.heap.FixedBufferAllocator.init(&storage);
    const maybe_expected = exactF64RationalAlloc(fixed.allocator(), value) catch return false;
    const expected = maybe_expected orelse return false;
    return std.mem.eql(u8, rational.numerator, expected.numerator) and
        std.mem.eql(u8, rational.denominator, expected.denominator);
}

fn managedDecimalAlloc(allocator: std.mem.Allocator, value: *const std.math.big.int.Managed) std.mem.Allocator.Error![]u8 {
    return value.toString(allocator, 10, .lower) catch |err| switch (err) {
        error.InvalidBase => unreachable,
        error.OutOfMemory => return error.OutOfMemory,
    };
}

pub fn parseCanonicalSigned(comptime T: type, decimal: []const u8) ?T {
    if (!isCanonicalSignedDecimal(decimal)) return null;
    return std.fmt.parseInt(T, decimal, 10) catch null;
}

pub fn parseCanonicalUnsigned(comptime T: type, decimal: []const u8) ?T {
    if (!isCanonicalUnsignedDecimal(decimal)) return null;
    return std.fmt.parseInt(T, decimal, 10) catch null;
}

pub fn isCanonicalSignedDecimal(decimal: []const u8) bool {
    if (decimal.len == 0) return false;
    if (decimal[0] != '-') return isCanonicalUnsignedDecimal(decimal);
    if (decimal.len == 1 or decimal[1] == '0') return false;
    return allDecimalDigits(decimal[1..]);
}

pub fn isCanonicalUnsignedDecimal(decimal: []const u8) bool {
    if (decimal.len == 0) return false;
    if (decimal.len > 1 and decimal[0] == '0') return false;
    return allDecimalDigits(decimal);
}

pub fn signedFitsBits(decimal: []const u8, bit_width: u16) bool {
    if (bit_width == 0 or !isCanonicalSignedDecimal(decimal)) return false;
    const negative = decimal[0] == '-';
    const magnitude = if (negative) decimal[1..] else decimal;
    return switch (compareMagnitudeToPowerOfTwo(magnitude, bit_width - 1)) {
        .less => true,
        .equal => negative,
        .greater => false,
    };
}

pub fn unsignedFitsBits(decimal: []const u8, bit_width: u16) bool {
    if (bit_width == 0 or !isCanonicalUnsignedDecimal(decimal)) return false;
    return compareMagnitudeToPowerOfTwo(decimal, bit_width) == .less;
}

fn allDecimalDigits(decimal: []const u8) bool {
    for (decimal) |byte| if (byte < '0' or byte > '9') return false;
    return true;
}

const MagnitudeOrder = enum {
    less,
    equal,
    greater,
};

fn compareMagnitudeToPowerOfTwo(decimal: []const u8, exponent: u16) MagnitudeOrder {
    const max_limbs = (@as(usize, std.math.maxInt(u16)) + 63) / 64;
    var limbs = [_]u64{0} ** max_limbs;
    var used: usize = 1;

    for (decimal) |byte| {
        var carry: u128 = byte - '0';
        for (limbs[0..used]) |*limb| {
            const product = @as(u128, limb.*) * 10 + carry;
            limb.* = @truncate(product);
            carry = product >> 64;
        }
        if (carry != 0) {
            if (used == limbs.len) return .greater;
            limbs[used] = @intCast(carry);
            used += 1;
        }

        if (compareLimbsToPowerOfTwo(limbs[0..used], exponent) == .greater) return .greater;
    }
    return compareLimbsToPowerOfTwo(limbs[0..used], exponent);
}

fn compareLimbsToPowerOfTwo(limbs: []const u64, exponent: u16) MagnitudeOrder {
    const power_limb: usize = exponent / 64;
    if (limbs.len - 1 > power_limb) return .greater;
    if (limbs.len - 1 < power_limb) return .less;

    const power_bit: u6 = @intCast(exponent % 64);
    const threshold = @as(u64, 1) << power_bit;
    if (limbs[power_limb] < threshold) return .less;
    if (limbs[power_limb] > threshold) return .greater;
    for (limbs[0..power_limb]) |limb| if (limb != 0) return .greater;
    return .equal;
}

test "canonical decimal parsing rejects ambiguous spelling and overflow" {
    try std.testing.expectEqual(@as(?i64, -7), parseCanonicalSigned(i64, "-7"));
    try std.testing.expectEqual(@as(?u64, 7), parseCanonicalUnsigned(u64, "7"));
    try std.testing.expect(parseCanonicalSigned(i64, "-0") == null);
    try std.testing.expect(parseCanonicalUnsigned(u64, "07") == null);
    try std.testing.expect(parseCanonicalUnsigned(u8, "256") == null);
}

test "fixed-width decimal range checks are independent of host integer width" {
    try std.testing.expect(signedFitsBits("-1", 1));
    try std.testing.expect(signedFitsBits("0", 1));
    try std.testing.expect(!signedFitsBits("1", 1));
    try std.testing.expect(unsignedFitsBits("255", 8));
    try std.testing.expect(!unsignedFitsBits("256", 8));
    try std.testing.expect(!unsignedFitsBits("-1", 8));

    try std.testing.expect(signedFitsBits("170141183460469231731687303715884105727", 128));
    try std.testing.expect(!signedFitsBits("170141183460469231731687303715884105728", 128));
    try std.testing.expect(signedFitsBits("-170141183460469231731687303715884105728", 128));
    try std.testing.expect(!signedFitsBits("-170141183460469231731687303715884105729", 128));
    try std.testing.expect(unsignedFitsBits("340282366920938463463374607431768211455", 128));
    try std.testing.expect(!unsignedFitsBits("340282366920938463463374607431768211456", 128));
}

test "finite f64 values become exact canonical rationals" {
    const cases = [_]struct {
        value: f64,
        numerator: []const u8,
        denominator: []const u8,
    }{
        .{ .value = -0.0, .numerator = "0", .denominator = "1" },
        .{ .value = -0.5, .numerator = "-1", .denominator = "2" },
        .{ .value = 0.1, .numerator = "3602879701896397", .denominator = "36028797018963968" },
    };
    for (cases) |case| {
        const rational = (try exactF64RationalAlloc(std.testing.allocator, case.value)).?;
        defer std.testing.allocator.free(@constCast(rational.numerator));
        defer std.testing.allocator.free(@constCast(rational.denominator));
        try std.testing.expectEqualStrings(case.numerator, rational.numerator);
        try std.testing.expectEqualStrings(case.denominator, rational.denominator);
        try std.testing.expect(rationalExactlyRepresentsF64(rational, case.value));
    }
    try std.testing.expect((try exactF64RationalAlloc(std.testing.allocator, std.math.inf(f64))) == null);

    for ([_]f64{
        @bitCast(@as(u64, 1)),
        @bitCast(@as(u64, 0x7fef_ffff_ffff_ffff)),
    }) |value| {
        const rational = (try exactF64RationalAlloc(std.testing.allocator, value)).?;
        defer std.testing.allocator.free(@constCast(rational.numerator));
        defer std.testing.allocator.free(@constCast(rational.denominator));
        try std.testing.expect(rationalExactlyRepresentsF64(rational, value));
    }
}
