const std = @import("std");
const ir = @import("ir.zig");

pub const Replacement = struct {
    from: ir.ValueId,
    to: ir.ValueId,
};

pub fn operationAlloc(
    allocator: std.mem.Allocator,
    operation: ir.Operation,
    replacements: []const Replacement,
) std.mem.Allocator.Error!ir.Operation {
    return switch (operation) {
        .constant, .make_table, .function_ref, .place_read, .adjust_pack => operation,
        .pack_values => |values| .{ .pack_values = try valuesAlloc(allocator, values, replacements) },
        .copy => |value| .{ .copy = replace(value, replacements) },
        .unary => |value| .{ .unary = .{
            .operator = value.operator,
            .operand = replace(value.operand, replacements),
            .mode = value.mode,
        } },
        .binary => |value| .{ .binary = .{
            .operator = value.operator,
            .left = replace(value.left, replacements),
            .right = replace(value.right, replacements),
            .mode = value.mode,
            .shift_behavior = value.shift_behavior,
        } },
        .call => |value| .{ .call = .{
            .callee = replace(value.callee, replacements),
            .arguments = try valuesAlloc(allocator, value.arguments, replacements),
            .argument_pack = value.argument_pack,
            .result_arity = value.result_arity,
        } },
        .call_repeated_table_get => |value| .{ .call_repeated_table_get = .{
            .callee = replace(value.callee, replacements),
            .prefix_arguments = try valuesAlloc(allocator, value.prefix_arguments, replacements),
            .table = replace(value.table, replacements),
            .key = replace(value.key, replacements),
            .from = replace(value.from, replacements),
            .to = replace(value.to, replacements),
            .step = replace(value.step, replacements),
            .counter = value.counter,
            .result_arity = value.result_arity,
        } },
        .namecall => |value| .{ .namecall = .{
            .receiver = replace(value.receiver, replacements),
            .method = value.method,
            .arguments = try valuesAlloc(allocator, value.arguments, replacements),
            .argument_pack = value.argument_pack,
            .result_arity = value.result_arity,
        } },
        .protected_call => |value| .{ .protected_call = .{
            .callee = replace(value.callee, replacements),
            .error_handler = if (value.error_handler) |handler| replace(handler, replacements) else null,
            .arguments = try valuesAlloc(allocator, value.arguments, replacements),
            .argument_pack = value.argument_pack,
            .result_arity = value.result_arity,
        } },
        .coroutine_create => |value| .{ .coroutine_create = .{
            .callee = replace(value.callee, replacements),
        } },
        .coroutine_resume => |value| .{ .coroutine_resume = .{
            .thread = replace(value.thread, replacements),
            .arguments = try valuesAlloc(allocator, value.arguments, replacements),
            .argument_pack = value.argument_pack,
            .result_arity = value.result_arity,
        } },
        .coroutine_yield => |value| .{ .coroutine_yield = .{
            .arguments = try valuesAlloc(allocator, value.arguments, replacements),
            .argument_pack = value.argument_pack,
            .result_arity = value.result_arity,
        } },
        .environment_get => |value| .{ .environment_get = .{
            .target = replaceEnvironmentTarget(value.target, replacements),
            .name = value.name,
            .mode = value.mode,
        } },
        .environment_set => |value| .{ .environment_set = .{
            .target = replaceEnvironmentTarget(value.target, replacements),
            .name = value.name,
            .value = replace(value.value, replacements),
            .mode = value.mode,
        } },
        .table_get => |value| .{ .table_get = .{
            .table = replace(value.table, replacements),
            .key = replace(value.key, replacements),
            .mode = value.mode,
        } },
        .table_set => |value| .{ .table_set = .{
            .table = replace(value.table, replacements),
            .key = replace(value.key, replacements),
            .value = replace(value.value, replacements),
            .mode = value.mode,
        } },
        .table_set_pack => |value| .{ .table_set_pack = .{
            .table = replace(value.table, replacements),
            .first_index = value.first_index,
            .pack = value.pack,
        } },
        .make_table_literal => |value| .{ .make_table_literal = .{
            .fields = try fieldsAlloc(allocator, value.fields, replacements),
            .tail_pack = value.tail_pack,
        } },
        .string_interpolate => |value| .{ .string_interpolate = .{
            .segments = value.segments,
            .values = try valuesAlloc(allocator, value.values, replacements),
        } },
        .make_closure => |value| .{ .make_closure = .{
            .function = value.function,
            .bindings = try bindingsAlloc(allocator, value.bindings, replacements),
        } },
        .place_write => |value| .{ .place_write = .{
            .place = value.place,
            .value = replace(value.value, replacements),
        } },
        .numeric_for_next => |value| .{ .numeric_for_next = .{
            .control = replace(value.control, replacements),
            .limit = replace(value.limit, replacements),
            .step = replace(value.step, replacements),
            .initial = replace(value.initial, replacements),
            .mode = value.mode,
        } },
        .generic_for_next => |value| .{ .generic_for_next = .{
            .iterator = replace(value.iterator, replacements),
            .state = replace(value.state, replacements),
            .control = replace(value.control, replacements),
            .initial = replace(value.initial, replacements),
            .variable_count = value.variable_count,
        } },
    };
}

pub fn terminatorAlloc(
    allocator: std.mem.Allocator,
    terminator: ir.Terminator,
    replacements: []const Replacement,
) std.mem.Allocator.Error!ir.Terminator {
    return switch (terminator) {
        .jump => |edge| .{ .jump = try edgeAlloc(allocator, edge, replacements) },
        .branch => |branch| .{ .branch = .{
            .condition = replace(branch.condition, replacements),
            .then_edge = try edgeAlloc(allocator, branch.then_edge, replacements),
            .else_edge = try edgeAlloc(allocator, branch.else_edge, replacements),
        } },
        .return_values => |values| .{ .return_values = try valuesAlloc(allocator, values, replacements) },
        .return_pack, .unreachable_block => terminator,
        .return_expanded => |value| .{ .return_expanded = .{
            .values = try valuesAlloc(allocator, value.values, replacements),
            .pack = value.pack,
        } },
        .throw_error => |value| .{ .throw_error = .{
            .value = replace(value.value, replacements),
            .level = value.level,
            .dynamic_level = if (value.dynamic_level) |level| replace(level, replacements) else null,
        } },
    };
}

fn edgeAlloc(
    allocator: std.mem.Allocator,
    edge: ir.Edge,
    replacements: []const Replacement,
) std.mem.Allocator.Error!ir.Edge {
    return .{
        .target = edge.target,
        .arguments = try valuesAlloc(allocator, edge.arguments, replacements),
    };
}

fn valuesAlloc(
    allocator: std.mem.Allocator,
    values: []const ir.ValueId,
    replacements: []const Replacement,
) std.mem.Allocator.Error![]const ir.ValueId {
    var changed = false;
    for (values) |value| {
        if (replace(value, replacements) != value) {
            changed = true;
            break;
        }
    }
    if (!changed) return values;
    const mapped = try allocator.alloc(ir.ValueId, values.len);
    for (values, 0..) |value, index| mapped[index] = replace(value, replacements);
    return mapped;
}

fn fieldsAlloc(
    allocator: std.mem.Allocator,
    fields: []const ir.TableConstructorField,
    replacements: []const Replacement,
) std.mem.Allocator.Error![]const ir.TableConstructorField {
    var changed = false;
    for (fields) |field| switch (field) {
        .list => |value| changed = changed or replace(value, replacements) != value,
        .keyed => |value| changed = changed or replace(value.key, replacements) != value.key or
            replace(value.value, replacements) != value.value,
    };
    if (!changed) return fields;
    const mapped = try allocator.alloc(ir.TableConstructorField, fields.len);
    for (fields, 0..) |field, index| mapped[index] = switch (field) {
        .list => |value| .{ .list = replace(value, replacements) },
        .keyed => |value| .{ .keyed = .{
            .key = replace(value.key, replacements),
            .value = replace(value.value, replacements),
        } },
    };
    return mapped;
}

fn bindingsAlloc(
    allocator: std.mem.Allocator,
    bindings: []const ir.CaptureBinding,
    replacements: []const Replacement,
) std.mem.Allocator.Error![]const ir.CaptureBinding {
    var changed = false;
    for (bindings) |binding| switch (binding) {
        .value => |value| changed = changed or replace(value, replacements) != value,
        .place => {},
    };
    if (!changed) return bindings;
    const mapped = try allocator.alloc(ir.CaptureBinding, bindings.len);
    for (bindings, 0..) |binding, index| mapped[index] = switch (binding) {
        .value => |value| .{ .value = replace(value, replacements) },
        .place => |place| .{ .place = place },
    };
    return mapped;
}

fn replaceEnvironmentTarget(target: ir.EnvironmentTarget, replacements: []const Replacement) ir.EnvironmentTarget {
    return switch (target) {
        .ambient => target,
        .value => |value| .{ .value = replace(value, replacements) },
    };
}

fn replace(value: ir.ValueId, replacements: []const Replacement) ir.ValueId {
    for (replacements) |replacement| if (replacement.from == value) return replacement.to;
    return value;
}

test "runtime value rewriting preserves shift behavior" {
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const rewritten_left = ir.ValueId.fromIndex(2);
    const rewritten_right = ir.ValueId.fromIndex(3);
    const operation: ir.Operation = .{ .binary = .{
        .operator = .shift_right,
        .left = left,
        .right = right,
        .mode = .primitive,
        .shift_behavior = .zero_saturating,
    } };
    const rewritten = try operationAlloc(std.testing.allocator, operation, &.{
        .{ .from = left, .to = rewritten_left },
        .{ .from = right, .to = rewritten_right },
    });

    try std.testing.expectEqual(ir.BinaryOperator.shift_right, rewritten.binary.operator);
    try std.testing.expectEqual(rewritten_left, rewritten.binary.left);
    try std.testing.expectEqual(rewritten_right, rewritten.binary.right);
    try std.testing.expectEqual(ir.ShiftBehavior.zero_saturating, rewritten.binary.shift_behavior.?);
}

test "runtime value rewriting remaps dynamic error levels" {
    const message = ir.ValueId.fromIndex(0);
    const level = ir.ValueId.fromIndex(1);
    const rewritten_message = ir.ValueId.fromIndex(2);
    const rewritten_level = ir.ValueId.fromIndex(3);
    const terminator: ir.Terminator = .{ .throw_error = .{
        .value = message,
        .level = 0,
        .dynamic_level = level,
    } };

    const rewritten = try terminatorAlloc(std.testing.allocator, terminator, &.{
        .{ .from = message, .to = rewritten_message },
        .{ .from = level, .to = rewritten_level },
    });

    try std.testing.expectEqual(rewritten_message, rewritten.throw_error.value);
    try std.testing.expectEqual(@as(u32, 0), rewritten.throw_error.level);
    try std.testing.expectEqual(rewritten_level, rewritten.throw_error.dynamic_level.?);
}
