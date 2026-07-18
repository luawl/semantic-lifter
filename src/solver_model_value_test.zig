const std = @import("std");
const ir = @import("ir.zig");
const model_value = @import("solver_model_value.zig");

const Context = model_value.Context;
const Value = model_value.Value;

fn expectValue(context: Context, actual: Value, expected: ir.SolverModelValue) !void {
    const expected_value = try context.fromModel(expected);
    try std.testing.expect((try context.eql(actual, expected_value)) orelse false);
}

test "opaque dynamic model values preserve identity equality and selection" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const context: Context = .{ .allocator = arena.allocator() };
    const first = try context.fromModel(.{ .dynamic_identity = 0 });
    const same = try context.fromModel(.{ .dynamic_identity = 0 });
    const distinct = try context.fromModel(.{ .dynamic_identity = 1 });

    try std.testing.expectEqual(true, (try context.eql(first, same)).?);
    try std.testing.expectEqual(false, (try context.eql(first, distinct)).?);
    try std.testing.expectEqual(true, model_value.truth(try context.binary(.equal, .{ .kind = .dynamic_value }, first, same)).?);
    try std.testing.expectEqual(true, model_value.truth(try context.binary(.not_equal, .{ .kind = .dynamic_value }, first, distinct)).?);
    try expectValue(context, try context.select(model_value.unknown(), first, same), .{ .dynamic_identity = 0 });
    try std.testing.expect(model_value.isUnknown(try context.select(model_value.unknown(), first, distinct)));
}

test "model Boolean values preserve decisive operands around unknowns" {
    const context: Context = .{ .allocator = std.testing.allocator };
    const unknown = model_value.unknown();
    const false_value = context.booleanValue(false);
    const true_value = context.booleanValue(true);
    const boolean_sort: ir.SolverSort = .{ .kind = .boolean };

    try std.testing.expectEqual(false, model_value.truth(try context.binary(.logical_and, boolean_sort, false_value, unknown)).?);
    try std.testing.expectEqual(false, model_value.truth(try context.binary(.logical_and, boolean_sort, unknown, false_value)).?);
    try std.testing.expectEqual(true, model_value.truth(try context.binary(.logical_or, boolean_sort, true_value, unknown)).?);
    try std.testing.expectEqual(true, model_value.truth(try context.binary(.logical_or, boolean_sort, unknown, true_value)).?);
    try std.testing.expect(model_value.isUnknown(try context.binary(.logical_and, boolean_sort, true_value, unknown)));
    try std.testing.expect(model_value.isUnknown(try context.binary(.logical_or, boolean_sort, false_value, unknown)));
}

test "model values preserve arbitrary integer and rational arithmetic" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const context: Context = .{ .allocator = arena.allocator() };

    const left = try context.integerLiteral("340282366920938463463374607431768211455");
    const right = try context.integerLiteral("2");
    const sum = try context.binary(.add, .{ .kind = .integer }, left, right);
    try expectValue(context, sum, .{ .integer = "340282366920938463463374607431768211457" });

    const first = try context.realLiteral(.{ .numerator = "3", .denominator = "2" });
    const second = try context.realLiteral(.{ .numerator = "5", .denominator = "3" });
    try expectValue(context, try context.binary(.add, .{ .kind = .real }, first, second), .{ .real = .{ .numerator = "19", .denominator = "6" } });
    try expectValue(context, try context.binary(.subtract, .{ .kind = .real }, first, second), .{ .real = .{ .numerator = "-1", .denominator = "6" } });
    try expectValue(context, try context.binary(.multiply, .{ .kind = .real }, first, second), .{ .real = .{ .numerator = "5", .denominator = "2" } });
    try expectValue(context, try context.division(.real, first, second, context.booleanValue(true)), .{ .real = .{ .numerator = "9", .denominator = "10" } });
    try expectValue(context, try context.negate(first), .{ .real = .{ .numerator = "-3", .denominator = "2" } });
    try std.testing.expectEqual(true, model_value.truth(try context.binary(.less, .{ .kind = .real }, first, second)).?);
    try std.testing.expectEqual(true, model_value.truth(context.isNonzero(first)).?);
}

test "model values preserve integer division and remainder modes" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const context: Context = .{ .allocator = arena.allocator() };
    const left = try context.integerLiteral("-5");
    const right = try context.integerLiteral("-3");
    const defined = context.booleanValue(true);

    try expectValue(context, try context.division(.integer_euclidean, left, right, defined), .{ .integer = "2" });
    try expectValue(context, try context.remainder(.integer_euclidean, left, right, defined), .{ .integer = "1" });
    try expectValue(context, try context.division(.integer_floor, left, right, defined), .{ .integer = "1" });
    try expectValue(context, try context.remainder(.integer_floor, left, right, defined), .{ .integer = "-2" });
}

test "model values preserve wide and structural bit-vector operations" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const context: Context = .{ .allocator = arena.allocator() };
    const wide_sort: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 128 };
    const max = try context.bitVectorLiteral(.{ .value = "340282366920938463463374607431768211455", .bit_width = 128 });
    const wide_one = try context.bitVectorLiteral(.{ .value = "1", .bit_width = 128 });
    try expectValue(context, try context.binary(.add, wide_sort, max, wide_one), .{ .bit_vector = .{ .value = "0", .bit_width = 128 } });
    try expectValue(context, try context.binary(.shift_right, .{ .kind = .bit_vector, .bit_width = 128, .signed = true }, max, wide_one), .{ .bit_vector = .{
        .value = "340282366920938463463374607431768211455",
        .bit_width = 128,
    } });
    try expectValue(context, try context.bitVectorToInteger(max, true), .{ .integer = "-1" });

    const byte_sort: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8 };
    const signed_byte_sort: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8, .signed = true };
    const high_bit = try context.bitVectorLiteral(.{ .value = "129", .bit_width = 8 });
    const one = try context.bitVectorLiteral(.{ .value = "1", .bit_width = 8 });
    const seven = try context.bitVectorLiteral(.{ .value = "7", .bit_width = 8 });
    const eight = try context.bitVectorLiteral(.{ .value = "8", .bit_width = 8 });
    try expectValue(context, try context.bitVectorNot(high_bit), .{ .bit_vector = .{ .value = "126", .bit_width = 8 } });
    try expectValue(context, try context.bitVectorExtract(high_bit, 7, 4), .{ .bit_vector = .{ .value = "8", .bit_width = 4 } });
    const high_nibble = try context.bitVectorLiteral(.{ .value = "10", .bit_width = 4 });
    const low_nibble = try context.bitVectorLiteral(.{ .value = "5", .bit_width = 4 });
    try expectValue(context, try context.bitVectorConcat(high_nibble, low_nibble), .{ .bit_vector = .{ .value = "165", .bit_width = 8 } });
    const negative_nibble = try context.bitVectorLiteral(.{ .value = "15", .bit_width = 4 });
    try expectValue(context, try context.bitVectorExtend(negative_nibble, 4, .zero), .{ .bit_vector = .{ .value = "15", .bit_width = 8 } });
    try expectValue(context, try context.bitVectorExtend(negative_nibble, 4, .sign), .{ .bit_vector = .{ .value = "255", .bit_width = 8 } });
    try expectValue(context, try context.bitVectorRotate(high_bit, one, .left), .{ .bit_vector = .{ .value = "3", .bit_width = 8 } });
    try expectValue(context, try context.bitVectorRotate(high_bit, one, .right), .{ .bit_vector = .{ .value = "192", .bit_width = 8 } });
    try expectValue(context, try context.integerToBitVector(try context.integerLiteral("-1"), 8), .{ .bit_vector = .{ .value = "255", .bit_width = 8 } });
    try expectValue(context, try context.negate(one), .{ .bit_vector = .{ .value = "255", .bit_width = 8 } });
    try std.testing.expectEqual(true, model_value.truth(try context.binary(.greater, byte_sort, high_bit, one)).?);
    try std.testing.expectEqual(true, model_value.truth(try context.binary(.less, signed_byte_sort, high_bit, one)).?);
    try expectValue(context, try context.binary(.shift_left, byte_sort, one, seven), .{ .bit_vector = .{ .value = "128", .bit_width = 8 } });
    try expectValue(context, try context.binary(.shift_left, byte_sort, one, eight), .{ .bit_vector = .{ .value = "0", .bit_width = 8 } });
    try expectValue(context, try context.binary(.shift_right, signed_byte_sort, high_bit, one), .{ .bit_vector = .{ .value = "192", .bit_width = 8 } });
}

test "model values preserve bit-vector division and remainder modes" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const context: Context = .{ .allocator = arena.allocator() };
    const defined = context.booleanValue(true);
    const left_unsigned = try context.bitVectorLiteral(.{ .value = "250", .bit_width = 8 });
    const right_positive = try context.bitVectorLiteral(.{ .value = "3", .bit_width = 8 });
    try expectValue(context, try context.division(.bit_vector_unsigned, left_unsigned, right_positive, defined), .{ .bit_vector = .{ .value = "83", .bit_width = 8 } });
    try expectValue(context, try context.remainder(.bit_vector_unsigned, left_unsigned, right_positive, defined), .{ .bit_vector = .{ .value = "1", .bit_width = 8 } });

    const left_signed = try context.bitVectorLiteral(.{ .value = "251", .bit_width = 8 });
    try expectValue(context, try context.division(.bit_vector_signed, left_signed, right_positive, defined), .{ .bit_vector = .{ .value = "255", .bit_width = 8 } });
    try expectValue(context, try context.remainder(.bit_vector_signed_dividend, left_signed, right_positive, defined), .{ .bit_vector = .{ .value = "254", .bit_width = 8 } });
    try expectValue(context, try context.remainder(.bit_vector_signed_divisor, left_signed, right_positive, defined), .{ .bit_vector = .{ .value = "1", .bit_width = 8 } });
    const right_negative = try context.bitVectorLiteral(.{ .value = "253", .bit_width = 8 });
    try expectValue(context, try context.remainder(.bit_vector_signed_divisor, left_signed, right_negative, defined), .{ .bit_vector = .{ .value = "254", .bit_width = 8 } });
}
