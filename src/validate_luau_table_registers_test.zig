const std = @import("std");
const ir = @import("ir.zig");
const diagnostics = @import("diagnostics.zig");
const readable_scope = @import("readable_scope.zig");
const register_validation = @import("validate_luau_registers.zig");

fn validate(
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
) !void {
    return register_validation.validate(allocator, report, program, scope, .direct_locals_luau);
}

fn tableTemporaryPressureReport(comptime field_count: usize) !diagnostics.Report {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const produce_id = ir.InstructionId.fromIndex(0);
    const table_id = ir.InstructionId.fromIndex(1);
    const callee = ir.ValueId.fromIndex(0);
    const table = ir.ValueId.fromIndex(field_count + 1);
    var values: [field_count + 2]ir.Value = undefined;
    var results: [field_count]ir.ValueId = undefined;
    var fields: [field_count]ir.TableConstructorField = undefined;
    values[0] = .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } };
    for (&results, &fields, 0..) |*result, *field, index| {
        result.* = ir.ValueId.fromIndex(index + 1);
        values[index + 1] = .{
            .id = result.*,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = produce_id, .index = @intCast(index) } },
        };
        field.* = .{ .list = result.* };
    }
    values[table.index()] = .{
        .id = table,
        .function = function_id,
        .type = .{ .kind = .table },
        .origin = .{ .instruction_result = .{ .instruction = table_id, .index = 0 } },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = produce_id,
            .block = block_id,
            .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = field_count } } },
            .results = &results,
            .effects = .dynamic_call,
        },
        .{
            .id = table_id,
            .block = block_id,
            .operation = .{ .make_table_literal = .{ .fields = &fields } },
            .results = &.{table},
            .effects = .pure,
        },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ produce_id, table_id },
        .terminator = .{ .return_values = &.{ table, table } },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{callee},
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "table-register-pressure",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer scope.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    errdefer report.deinit();
    try validate(std.testing.allocator, &report, &program, &scope);
    return report;
}

test "table construction shares the total register budget with retained locals" {
    var boundary = try tableTemporaryPressureReport(126);
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var excessive = try tableTemporaryPressureReport(127);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

fn registerAtomicKeyedTableReport(comptime field_count: usize) !diagnostics.Report {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const scalar_count = field_count * 2;
    const table_id = ir.InstructionId.fromIndex(scalar_count);
    const table_value = ir.ValueId.fromIndex(scalar_count);
    var scalar_results: [scalar_count]ir.ValueId = undefined;
    var values: [scalar_count + 1]ir.Value = undefined;
    var instruction_ids: [scalar_count + 1]ir.InstructionId = undefined;
    var instructions: [scalar_count + 1]ir.Instruction = undefined;
    var fields: [field_count]ir.TableConstructorField = undefined;
    for (0..field_count) |field_index| {
        const key_index = field_index * 2;
        const value_index = key_index + 1;
        const key_id = ir.ValueId.fromIndex(key_index);
        const value_id = ir.ValueId.fromIndex(value_index);
        scalar_results[key_index] = key_id;
        scalar_results[value_index] = value_id;
        values[key_index] = .{
            .id = key_id,
            .function = function_id,
            .type = .{ .kind = .integer },
            .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(key_index), .index = 0 } },
        };
        values[value_index] = .{
            .id = value_id,
            .function = function_id,
            .type = .{ .kind = .string },
            .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(value_index), .index = 0 } },
        };
        instruction_ids[key_index] = ir.InstructionId.fromIndex(key_index);
        instruction_ids[value_index] = ir.InstructionId.fromIndex(value_index);
        instructions[key_index] = .{
            .id = instruction_ids[key_index],
            .block = block_id,
            .operation = .{ .constant = .{ .integer = "1" } },
            .results = scalar_results[key_index .. key_index + 1],
            .effects = .pure,
        };
        instructions[value_index] = .{
            .id = instruction_ids[value_index],
            .block = block_id,
            .operation = .{ .constant = .{ .string = "value" } },
            .results = scalar_results[value_index .. value_index + 1],
            .effects = .pure,
        };
        fields[field_index] = .{ .keyed = .{ .key = key_id, .value = value_id } };
    }
    values[table_value.index()] = .{
        .id = table_value,
        .function = function_id,
        .type = .{ .kind = .table },
        .origin = .{ .instruction_result = .{ .instruction = table_id, .index = 0 } },
    };
    instruction_ids[scalar_count] = table_id;
    const table_results = [_]ir.ValueId{table_value};
    instructions[scalar_count] = .{
        .id = table_id,
        .block = block_id,
        .operation = .{ .make_table_literal = .{ .fields = &fields } },
        .results = &table_results,
        .effects = .pure,
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &instruction_ids,
        .terminator = .{ .return_values = &table_results },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "register-atomic-keyed-table",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer scope.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    errdefer report.deinit();
    try validate(std.testing.allocator, &report, &program, &scope);
    return report;
}

test "register-atomic keyed constructor fields reuse a sequential frame" {
    var report = try registerAtomicKeyedTableReport(256);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}
