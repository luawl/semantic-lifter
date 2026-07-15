const std = @import("std");
const ir = @import("ir.zig");

pub fn unaryIsStatic(values: []const ir.Value, operation: ir.Unary) bool {
    if (operation.operator == .logical_not) return true;
    if (operation.operand.index() >= values.len) return false;
    const kind = values[operation.operand.index()].type.kind;
    return switch (operation.operator) {
        .logical_not => true,
        .negate, .bit_not => isNumeric(kind),
        .length => kind == .string,
    };
}

pub fn binaryIsStatic(values: []const ir.Value, operation: ir.Binary) bool {
    if (operation.operator == .logical_and or operation.operator == .logical_or) return true;
    if (operation.left.index() >= values.len or operation.right.index() >= values.len) return false;
    const left = values[operation.left.index()].type.kind;
    const right = values[operation.right.index()].type.kind;
    return switch (operation.operator) {
        .logical_and, .logical_or => true,
        .add,
        .subtract,
        .multiply,
        .divide,
        .floor_divide,
        .modulo,
        .power,
        .bit_and,
        .bit_or,
        .bit_xor,
        .shift_left,
        .shift_right,
        => isNumeric(left) and isNumeric(right),
        .concat => isStringConvertible(left) and isStringConvertible(right),
        .less, .less_equal, .greater, .greater_equal => (isNumeric(left) and isNumeric(right)) or
            (left == .string and right == .string),
        .equal, .not_equal => isPrimitiveEqualityKind(left) and isPrimitiveEqualityKind(right),
    };
}

fn isNumeric(kind: ir.TypeKind) bool {
    return kind == .integer or kind == .number;
}

fn isStringConvertible(kind: ir.TypeKind) bool {
    return kind == .string or isNumeric(kind);
}

fn isPrimitiveEqualityKind(kind: ir.TypeKind) bool {
    return switch (kind) {
        .nil_value, .boolean, .integer, .number, .string, .function, .thread => true,
        .dynamic, .table, .userdata, .tuple => false,
    };
}

test "static operator domains preserve Luau dispatch boundaries" {
    const function_id = ir.FunctionId.fromIndex(0);
    const dynamic = ir.ValueId.fromIndex(0);
    const integer = ir.ValueId.fromIndex(1);
    const string = ir.ValueId.fromIndex(2);
    const table = ir.ValueId.fromIndex(3);
    const values = [_]ir.Value{
        .{ .id = dynamic, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = integer, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = string, .function = function_id, .type = .string, .origin = .{ .parameter = 2 } },
        .{ .id = table, .function = function_id, .type = .{ .kind = .table }, .origin = .{ .parameter = 3 } },
    };

    try std.testing.expect(unaryIsStatic(&values, .{ .operator = .logical_not, .operand = dynamic }));
    try std.testing.expect(unaryIsStatic(&values, .{ .operator = .negate, .operand = integer }));
    try std.testing.expect(unaryIsStatic(&values, .{ .operator = .length, .operand = string }));
    try std.testing.expect(!unaryIsStatic(&values, .{ .operator = .negate, .operand = dynamic }));
    try std.testing.expect(binaryIsStatic(&values, .{ .operator = .add, .left = integer, .right = integer }));
    try std.testing.expect(binaryIsStatic(&values, .{ .operator = .concat, .left = string, .right = integer }));
    try std.testing.expect(binaryIsStatic(&values, .{ .operator = .logical_and, .left = dynamic, .right = table }));
    try std.testing.expect(!binaryIsStatic(&values, .{ .operator = .add, .left = table, .right = integer }));
    try std.testing.expect(!binaryIsStatic(&values, .{ .operator = .equal, .left = table, .right = table }));
}
