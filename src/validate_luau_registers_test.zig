const std = @import("std");
const ir = @import("ir.zig");
const diagnostics = @import("diagnostics.zig");
const emit_luau = @import("emit_luau.zig");
const emission_planning = @import("emit_luau_plan.zig");
const readable_scope = @import("readable_scope.zig");
const register_validation = @import("validate_luau_registers.zig");
const validation = @import("validate.zig");

fn validate(
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
) !void {
    return register_validation.validate(allocator, report, program, scope, .direct_locals_luau);
}
const operationTemporaryFrameSize = register_validation.operationTemporaryFrameSize;
const edgeAssignmentCycleCount = register_validation.edgeAssignmentCycleCount;

fn invocationPressureReport(comptime result_count: usize, protected: bool) !diagnostics.Report {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(0);
    var values: [result_count + 1]ir.Value = undefined;
    var results: [result_count]ir.ValueId = undefined;
    values[0] = .{
        .id = callee,
        .function = function_id,
        .type = .function,
        .origin = .{ .parameter = 0 },
    };
    for (&results, 0..) |*result, index| {
        result.* = ir.ValueId.fromIndex(index + 1);
        values[index + 1] = .{
            .id = result.*,
            .function = function_id,
            .type = if (protected and index == 0) .boolean else .dynamic,
            .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = @intCast(index) } },
        };
    }
    const operation: ir.Operation = if (protected)
        .{ .protected_call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = result_count } } }
    else
        .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = result_count } } };
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = block_id,
        .operation = operation,
        .results = &results,
        .effects = if (protected) .protected_invocation else .dynamic_call,
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{instruction_id},
        .terminator = .{ .return_values = &results },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{callee},
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "register-pressure",
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

test "function parameters reduce the fixed-result register budget" {
    var boundary = try invocationPressureReport(199, false);
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var excessive = try invocationPressureReport(200, false);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_register_pressure));
}

test "entry runtime captures reduce the fixed-result register budget" {
    var boundary = try invocationPressureReport(198, true);
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var excessive = try invocationPressureReport(199, true);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_register_pressure));
}

fn sequentialSnapshotClosurePressureReport(comptime snapshot_count: usize) !diagnostics.Report {
    const parameter_count = 188;
    const closure_count = 2;
    const source_count = closure_count * snapshot_count;
    const instruction_count = source_count + closure_count;
    const value_count = parameter_count + source_count + closure_count + snapshot_count;
    const entry_function = ir.FunctionId.fromIndex(0);
    const closure_function = ir.FunctionId.fromIndex(1);
    const entry_block = ir.BlockId.fromIndex(0);
    const closure_block = ir.BlockId.fromIndex(1);

    var parameters: [parameter_count]ir.ValueId = undefined;
    var closure_results: [closure_count]ir.ValueId = undefined;
    var captured_values: [snapshot_count]ir.ValueId = undefined;
    var capture_ids: [snapshot_count]ir.CaptureId = undefined;
    var values: [value_count]ir.Value = undefined;
    var captures: [snapshot_count]ir.Capture = undefined;
    var bindings: [closure_count][snapshot_count]ir.CaptureBinding = undefined;
    var result_ids: [instruction_count][1]ir.ValueId = undefined;
    var instruction_ids: [instruction_count]ir.InstructionId = undefined;
    var instructions: [instruction_count]ir.Instruction = undefined;

    for (&parameters, 0..) |*parameter, index| {
        parameter.* = ir.ValueId.fromIndex(index);
        values[index] = .{
            .id = parameter.*,
            .function = entry_function,
            .origin = .{ .parameter = @intCast(index) },
        };
    }
    for (0..closure_count) |closure_index| {
        for (0..snapshot_count) |capture_index| {
            const source_index = closure_index * snapshot_count + capture_index;
            const instruction_id = ir.InstructionId.fromIndex(source_index);
            const source = ir.ValueId.fromIndex(parameter_count + source_index);
            instruction_ids[source_index] = instruction_id;
            result_ids[source_index][0] = source;
            values[source.index()] = .{
                .id = source,
                .function = entry_function,
                .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } },
            };
            bindings[closure_index][capture_index] = .{ .value = source };
            instructions[source_index] = .{
                .id = instruction_id,
                .block = entry_block,
                .operation = .{ .constant = .{ .integer = "0" } },
                .results = &result_ids[source_index],
                .effects = .pure,
            };
        }
    }
    for (&closure_results, 0..) |*result, closure_index| {
        const instruction_index = source_count + closure_index;
        const instruction_id = ir.InstructionId.fromIndex(instruction_index);
        result.* = ir.ValueId.fromIndex(parameter_count + source_count + closure_index);
        instruction_ids[instruction_index] = instruction_id;
        result_ids[instruction_index][0] = result.*;
        values[result.index()] = .{
            .id = result.*,
            .function = entry_function,
            .type = .function,
            .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } },
        };
        instructions[instruction_index] = .{
            .id = instruction_id,
            .block = entry_block,
            .operation = .{ .make_closure = .{
                .function = closure_function,
                .bindings = &bindings[closure_index],
            } },
            .results = &result_ids[instruction_index],
            .effects = .pure,
        };
    }
    for (&captures, &capture_ids, &captured_values, 0..) |*capture, *capture_id, *captured, index| {
        capture_id.* = ir.CaptureId.fromIndex(index);
        captured.* = ir.ValueId.fromIndex(parameter_count + source_count + closure_count + index);
        values[captured.index()] = .{
            .id = captured.*,
            .function = closure_function,
            .origin = .{ .capture = capture_id.* },
        };
        capture.* = .{
            .id = capture_id.*,
            .function = closure_function,
            .kind = .{ .immutable_value = captured.* },
        };
    }

    const blocks = [_]ir.Block{
        .{
            .id = entry_block,
            .function = entry_function,
            .instructions = &instruction_ids,
            .terminator = .{ .return_values = &closure_results },
        },
        .{
            .id = closure_block,
            .function = closure_function,
            .terminator = .{ .return_values = &captured_values },
        },
    };
    const functions = [_]ir.Function{
        .{
            .id = entry_function,
            .parameters = &parameters,
            .blocks = &.{entry_block},
            .entry_block = entry_block,
        },
        .{
            .id = closure_function,
            .lexical_parent = entry_function,
            .captures = &capture_ids,
            .blocks = &.{closure_block},
            .entry_block = closure_block,
        },
    };
    const program: ir.Program = .{
        .program_id = "sequential-closure-snapshot-register-pressure",
        .entry_function = entry_function,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .captures = &captures,
    };
    var scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer scope.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    errdefer report.deinit();
    try validate(std.testing.allocator, &report, &program, &scope);
    return report;
}

test "sequential closure snapshots use independent lexical register windows" {
    var boundary = try sequentialSnapshotClosurePressureReport(10);
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var excessive = try sequentialSnapshotClosurePressureReport(11);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_register_pressure));
}

fn invocationTemporaryPressureReport(comptime result_count: usize) !diagnostics.Report {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const produce_id = ir.InstructionId.fromIndex(0);
    const consume_id = ir.InstructionId.fromIndex(1);
    const callee = ir.ValueId.fromIndex(0);
    var values: [result_count + 1]ir.Value = undefined;
    var results: [result_count]ir.ValueId = undefined;
    values[0] = .{
        .id = callee,
        .function = function_id,
        .type = .function,
        .origin = .{ .parameter = 0 },
    };
    for (&results, 0..) |*result, index| {
        result.* = ir.ValueId.fromIndex(index + 1);
        values[index + 1] = .{
            .id = result.*,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = produce_id, .index = @intCast(index) } },
        };
    }
    const instructions = [_]ir.Instruction{
        .{
            .id = produce_id,
            .block = block_id,
            .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = result_count } } },
            .results = &results,
            .effects = .dynamic_call,
        },
        .{
            .id = consume_id,
            .block = block_id,
            .operation = .{ .call = .{ .callee = callee, .arguments = &results, .result_arity = .{ .fixed = 0 } } },
            .results = &.{},
            .effects = .dynamic_call,
        },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ produce_id, consume_id },
        .terminator = .{ .return_values = &results },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{callee},
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "temporary-register-pressure",
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

test "retained locals and invocation frames share the temporary register budget" {
    var boundary = try invocationTemporaryPressureReport(126);
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var excessive = try invocationTemporaryPressureReport(127);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

test "call-like operations have explicit emitted frame sizes" {
    const value = ir.ValueId.fromIndex(0);
    const pack = ir.ValuePackId.fromIndex(0);
    const arguments = &.{ value, value };
    const Row = struct {
        operation: ir.Operation,
        expected: usize,
    };
    const rows = [_]Row{
        .{ .operation = .{ .call = .{ .callee = value, .arguments = arguments, .result_arity = .{ .fixed = 0 } } }, .expected = 3 },
        .{ .operation = .{ .call = .{ .callee = value, .arguments = arguments, .argument_pack = pack, .result_arity = .{ .fixed = 0 } } }, .expected = 4 },
        .{ .operation = .{ .namecall = .{ .receiver = value, .method = "invoke", .arguments = arguments, .result_arity = .{ .fixed = 0 } } }, .expected = 4 },
        .{ .operation = .{ .protected_call = .{ .callee = value, .arguments = arguments, .result_arity = .{ .fixed = 0 } } }, .expected = 4 },
        .{ .operation = .{ .protected_call = .{ .callee = value, .error_handler = value, .arguments = arguments, .result_arity = .{ .fixed = 0 } } }, .expected = 5 },
        .{ .operation = .{ .coroutine_create = .{ .callee = value } }, .expected = 2 },
        .{ .operation = .{ .coroutine_resume = .{ .thread = value, .arguments = arguments, .result_arity = .{ .fixed = 0 } } }, .expected = 4 },
        .{ .operation = .{ .coroutine_yield = .{ .arguments = arguments, .result_arity = .{ .fixed = 0 } } }, .expected = 3 },
        .{ .operation = .{ .table_set_pack = .{ .table = value, .first_index = 1, .pack = pack } }, .expected = 4 },
    };
    for (rows) |row| try std.testing.expectEqual(row.expected, operationTemporaryFrameSize(row.operation).?);
}

fn interpolationTemporaryPressureReport(comptime value_count: usize) !diagnostics.Report {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const produce_id = ir.InstructionId.fromIndex(0);
    const interpolate_id = ir.InstructionId.fromIndex(1);
    const callee = ir.ValueId.fromIndex(0);
    const interpolated = ir.ValueId.fromIndex(value_count + 1);
    var values: [value_count + 2]ir.Value = undefined;
    var results: [value_count]ir.ValueId = undefined;
    const segments = [_][]const u8{""} ** (value_count + 1);
    values[0] = .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } };
    for (&results, 0..) |*result, index| {
        result.* = ir.ValueId.fromIndex(index + 1);
        values[index + 1] = .{
            .id = result.*,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = produce_id, .index = @intCast(index) } },
        };
    }
    values[interpolated.index()] = .{
        .id = interpolated,
        .function = function_id,
        .type = .string,
        .origin = .{ .instruction_result = .{ .instruction = interpolate_id, .index = 0 } },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = produce_id,
            .block = block_id,
            .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = value_count } } },
            .results = &results,
            .effects = .dynamic_call,
        },
        .{
            .id = interpolate_id,
            .block = block_id,
            .operation = .{ .string_interpolate = .{ .segments = &segments, .values = &results } },
            .results = &.{interpolated},
            .effects = .pure,
        },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ produce_id, interpolate_id },
        .terminator = .{ .return_values = &.{ interpolated, interpolated } },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{callee},
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "interpolation-register-pressure",
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

test "interpolation formatting has an explicit emitted register frame" {
    var boundary = try interpolationTemporaryPressureReport(125);
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var excessive = try interpolationTemporaryPressureReport(126);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

fn returnTemporaryPressureReport(comptime value_count: usize, comptime reversed: bool) !diagnostics.Report {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(0);
    var values: [value_count + 1]ir.Value = undefined;
    var results: [value_count]ir.ValueId = undefined;
    var returned: [value_count]ir.ValueId = undefined;
    values[0] = .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } };
    for (&results, 0..) |*result, index| {
        result.* = ir.ValueId.fromIndex(index + 1);
        values[index + 1] = .{
            .id = result.*,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = @intCast(index) } },
        };
    }
    for (&returned, 0..) |*value, index| {
        value.* = results[if (reversed) value_count - index - 1 else index];
    }
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = block_id,
        .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = value_count } } },
        .results = &results,
        .effects = .dynamic_call,
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{instruction_id},
        .terminator = .{ .return_values = &returned },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{callee},
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "return-register-pressure",
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

test "ordered returns reuse contiguous locals while reordered returns need a frame" {
    var ordered = try returnTemporaryPressureReport(199, false);
    defer ordered.deinit();
    try std.testing.expect(ordered.isClean());

    var reordered_boundary = try returnTemporaryPressureReport(127, true);
    defer reordered_boundary.deinit();
    try std.testing.expect(reordered_boundary.isClean());

    var reordered_excessive = try returnTemporaryPressureReport(128, true);
    defer reordered_excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), reordered_excessive.diagnostics.items.len);
    try std.testing.expect(reordered_excessive.contains(.unsupported_readable_temporary_register_pressure));
}

test "parallel edge assignments allocate one temporary per local cycle" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const loop_id = ir.BlockId.fromIndex(1);
    const inputs = [_]ir.ValueId{
        ir.ValueId.fromIndex(0),
        ir.ValueId.fromIndex(1),
        ir.ValueId.fromIndex(2),
        ir.ValueId.fromIndex(3),
    };
    const carried = [_]ir.ValueId{
        ir.ValueId.fromIndex(4),
        ir.ValueId.fromIndex(5),
        ir.ValueId.fromIndex(6),
        ir.ValueId.fromIndex(7),
    };
    var values: [8]ir.Value = undefined;
    for (inputs, 0..) |value_id, index| {
        values[value_id.index()] = .{
            .id = value_id,
            .function = function_id,
            .origin = .{ .parameter = @intCast(index) },
        };
    }
    for (carried, 0..) |value_id, index| {
        values[value_id.index()] = .{
            .id = value_id,
            .function = function_id,
            .origin = .{ .block_parameter = .{ .block = loop_id, .index = @intCast(index) } },
        };
    }
    const reversed = [_]ir.ValueId{ carried[3], carried[2], carried[1], carried[0] };
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .jump = .{ .target = loop_id, .arguments = &inputs } } },
        .{ .id = loop_id, .function = function_id, .parameters = &carried, .terminator = .{ .jump = .{ .target = loop_id, .arguments = &reversed } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &inputs,
        .blocks = &.{ entry_id, loop_id },
        .entry_block = entry_id,
    }};
    const program: ir.Program = .{
        .program_id = "edge-cycle-register-pressure",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var emission = try emission_planning.Plan.init(std.testing.allocator, &program, .standard_luau);
    defer emission.deinit();
    try std.testing.expectEqual(@as(usize, 2), edgeAssignmentCycleCount(&program, &emission, blocks[1].terminator.jump));
    try std.testing.expectEqual(@as(usize, 0), edgeAssignmentCycleCount(
        &program,
        &emission,
        .{ .target = loop_id, .arguments = &carried },
    ));
}

fn expandedReturnTemporaryPressureReport(comptime value_count: usize) !diagnostics.Report {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(0);
    var values: [value_count + 1]ir.Value = undefined;
    var results: [value_count]ir.ValueId = undefined;
    values[0] = .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } };
    for (&results, 0..) |*result, index| {
        result.* = ir.ValueId.fromIndex(index + 1);
        values[index + 1] = .{
            .id = result.*,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = @intCast(index) } },
        };
    }
    const packs = [_]ir.ValuePack{.{
        .id = pack_id,
        .function = function_id,
        .origin = .{ .varargs = function_id },
    }};
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = block_id,
        .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = value_count } } },
        .results = &results,
        .effects = .dynamic_call,
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{instruction_id},
        .terminator = .{ .return_expanded = .{ .values = &results, .pack = pack_id } },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{callee},
        .is_variadic = true,
        .vararg_pack = pack_id,
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "expanded-return-register-pressure",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
    };
    var scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer scope.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    errdefer report.deinit();
    try validate(std.testing.allocator, &report, &program, &scope);
    return report;
}

test "expanded returns stage a fixed prefix before the open tail" {
    var boundary = try expandedReturnTemporaryPressureReport(126);
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var excessive = try expandedReturnTemporaryPressureReport(127);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

fn storedPackTemporaryPressureReport(comptime value_count: usize, comptime expand_results: bool) !diagnostics.Report {
    const proof = ir.EvidenceId.fromIndex(0);
    const entry_function = ir.FunctionId.fromIndex(0);
    const worker_function = ir.FunctionId.fromIndex(1);
    const entry_block = ir.BlockId.fromIndex(0);
    const worker_producer_block = ir.BlockId.fromIndex(1);
    const worker_consumer_block = ir.BlockId.fromIndex(2);
    const worker_latch_block = ir.BlockId.fromIndex(3);
    const worker_return_block = ir.BlockId.fromIndex(4);
    const call_id = ir.InstructionId.fromIndex(0);
    const adjust_id = ir.InstructionId.fromIndex(1);
    const discard_adjust_id = ir.InstructionId.fromIndex(2);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(0);
    var values: [value_count + 1]ir.Value = undefined;
    var results: [value_count]ir.ValueId = undefined;
    values[0] = .{ .id = callee, .function = worker_function, .type = .function, .origin = .{ .parameter = 0 } };
    for (&results, 0..) |*result, index| {
        result.* = ir.ValueId.fromIndex(index + 1);
        values[index + 1] = .{
            .id = result.*,
            .function = worker_function,
            .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = @intCast(index) } },
        };
    }
    const packs = [_]ir.ValuePack{.{
        .id = pack_id,
        .function = worker_function,
        .origin = .{ .instruction_result = call_id },
    }};
    const instructions = [_]ir.Instruction{
        .{
            .id = call_id,
            .block = worker_producer_block,
            .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .variadic = {} } } },
            .results = &.{},
            .pack_result = pack_id,
            .effects = .dynamic_call,
        },
        .{
            .id = adjust_id,
            .block = worker_consumer_block,
            .operation = .{ .adjust_pack = pack_id },
            .results = &results,
            .effects = .pure,
            .evidence = &.{proof},
        },
        .{
            .id = discard_adjust_id,
            .block = worker_latch_block,
            .operation = .{ .adjust_pack = pack_id },
            .results = &.{},
            .effects = .pure,
        },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry_block, .function = entry_function, .terminator = .{ .return_values = &.{} } },
        .{
            .id = worker_producer_block,
            .function = worker_function,
            .instructions = &.{call_id},
            .terminator = .{ .jump = .{ .target = worker_consumer_block } },
        },
        .{
            .id = worker_consumer_block,
            .function = worker_function,
            .instructions = &.{adjust_id},
            .terminator = .{ .jump = .{ .target = worker_latch_block } },
        },
        .{
            .id = worker_latch_block,
            .function = worker_function,
            .instructions = &.{discard_adjust_id},
            .terminator = .{ .branch = .{
                .condition = results[0],
                .then_edge = .{ .target = worker_producer_block },
                .else_edge = .{ .target = worker_return_block },
            } },
        },
        .{
            .id = worker_return_block,
            .function = worker_function,
            .terminator = if (expand_results)
                .{ .return_expanded = .{ .values = &results, .pack = pack_id } }
            else
                .{ .return_pack = pack_id },
        },
    };
    const functions = [_]ir.Function{
        .{ .id = entry_function, .blocks = &.{entry_block}, .entry_block = entry_block },
        .{
            .id = worker_function,
            .parameters = &.{callee},
            .blocks = &.{ worker_producer_block, worker_consumer_block, worker_latch_block, worker_return_block },
            .entry_block = worker_producer_block,
        },
    };
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .conformance_oracle,
        .locator = "fixture:reentrant-stored-pack-register-pressure",
    }};
    const program: ir.Program = .{
        .program_id = "stored-expanded-return-register-pressure",
        .entry_function = entry_function,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
        .evidence = &evidence,
    };
    var scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer scope.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    errdefer report.deinit();
    try validate(std.testing.allocator, &report, &program, &scope);
    return report;
}

test "reentrant cross-block stored expanded returns budget loop transfers" {
    var boundary = try storedPackTemporaryPressureReport(99, true);
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var excessive = try storedPackTemporaryPressureReport(100, true);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_register_pressure));
}

test "cross-block stored fixed adjustments reach the Luau local limit before temporary pressure" {
    var boundary = try storedPackTemporaryPressureReport(198, false);
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var excessive = try storedPackTemporaryPressureReport(199, false);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_register_pressure));
}

const EmitterExpectation = enum {
    skip,
    accepted,
    rejected,
};

fn fixedReturnCountReport(
    value_count: usize,
    profile: ir.AdmissionProfile,
    emitter: EmitterExpectation,
) !diagnostics.Report {
    const allocator = std.testing.allocator;
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const values = try allocator.alloc(ir.Value, value_count);
    defer allocator.free(values);
    const instructions = try allocator.alloc(ir.Instruction, value_count);
    defer allocator.free(instructions);
    const instruction_ids = try allocator.alloc(ir.InstructionId, value_count);
    defer allocator.free(instruction_ids);
    const value_ids = try allocator.alloc(ir.ValueId, value_count);
    defer allocator.free(value_ids);
    const result_ids = try allocator.alloc([1]ir.ValueId, value_count);
    defer allocator.free(result_ids);

    for (0..value_count) |index| {
        const instruction_id = ir.InstructionId.fromIndex(index);
        const value_id = ir.ValueId.fromIndex(index);
        instruction_ids[index] = instruction_id;
        value_ids[index] = value_id;
        result_ids[index] = .{value_id};
        values[index] = .{
            .id = value_id,
            .function = function_id,
            .type = .{ .kind = .nil_value },
            .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } },
        };
        instructions[index] = .{
            .id = instruction_id,
            .block = block_id,
            .operation = .{ .constant = .{ .nil_value = {} } },
            .results = &result_ids[index],
            .effects = .pure,
            .evidence = &.{proof},
        };
    }

    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = instruction_ids,
        .terminator = .{ .return_values = value_ids },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .conformance_oracle,
        .locator = "fixture:fixed-return-count-boundary",
    }};
    const program: ir.Program = .{
        .program_id = "fixed-return-count-boundary",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = instructions,
        .values = values,
        .evidence = &evidence,
    };

    switch (emitter) {
        .skip => {},
        .accepted => {
            const source = try emit_luau.emitStandardLuauAlloc(allocator, &program);
            defer allocator.free(source);
            try std.testing.expectEqual(value_count, std.mem.count(u8, source, "nil"));
        },
        .rejected => try std.testing.expectError(error.InvalidIr, emit_luau.emitStandardLuauAlloc(allocator, &program)),
    }
    return validation.validate(allocator, &program, profile);
}

test "fixed return count and temporary pressure are independently diagnosed" {
    var boundary = try fixedReturnCountReport(254, .readable_luau, .accepted);
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var core = try fixedReturnCountReport(255, .core, .skip);
    defer core.deinit();
    try std.testing.expect(core.isClean());

    var excessive = try fixedReturnCountReport(255, .readable_luau, .rejected);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 2), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_return_count));
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

fn packedInvocationTemporaryPressureReport(comptime value_count: usize) !diagnostics.Report {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const produce_id = ir.InstructionId.fromIndex(0);
    const pack_id_instruction = ir.InstructionId.fromIndex(1);
    const consume_id = ir.InstructionId.fromIndex(2);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(0);
    var values: [value_count + 1]ir.Value = undefined;
    var results: [value_count]ir.ValueId = undefined;
    const types = [_]ir.ValueType{.dynamic} ** value_count;
    values[0] = .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } };
    for (&results, 0..) |*result, index| {
        result.* = ir.ValueId.fromIndex(index + 1);
        values[index + 1] = .{
            .id = result.*,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = produce_id, .index = @intCast(index) } },
        };
    }
    const packs = [_]ir.ValuePack{.{
        .id = pack_id,
        .function = function_id,
        .origin = .{ .instruction_result = pack_id_instruction },
        .shape = .{ .prefix = &types, .tail = .closed },
    }};
    const instructions = [_]ir.Instruction{
        .{
            .id = produce_id,
            .block = block_id,
            .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = value_count } } },
            .results = &results,
            .effects = .dynamic_call,
        },
        .{
            .id = pack_id_instruction,
            .block = block_id,
            .operation = .{ .pack_values = &results },
            .results = &.{},
            .pack_result = pack_id,
            .effects = .pure,
        },
        .{
            .id = consume_id,
            .block = block_id,
            .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .argument_pack = pack_id, .result_arity = .{ .fixed = 0 } } },
            .results = &.{},
            .effects = .dynamic_call,
        },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ produce_id, pack_id_instruction, consume_id },
        .terminator = .{ .return_values = &results },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{callee},
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "packed-invocation-register-pressure",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
    };
    var scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer scope.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    errdefer report.deinit();
    try validate(std.testing.allocator, &report, &program, &scope);
    return report;
}

test "closed pack values contribute every emitted invocation argument" {
    var boundary = try packedInvocationTemporaryPressureReport(126);
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var excessive = try packedInvocationTemporaryPressureReport(127);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

/// One function whose entry branches on its first parameter into two sibling arms that each write `arm_places`
/// places allocated per execution and rejoin to return: the structured layout declares each arm's places in that
/// arm's scope, the dispatcher layout declares both arms' places at the function root.
fn siblingArmPlacesReport(
    comptime arm_places: usize,
    strategy: register_validation.EmissionStrategy,
    flat_functions: ?[]const bool,
) !diagnostics.Report {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const then_block = ir.BlockId.fromIndex(1);
    const else_block = ir.BlockId.fromIndex(2);
    const join = ir.BlockId.fromIndex(3);
    const selector = ir.ValueId.fromIndex(0);
    const budget = ir.ValueId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = budget, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
    };
    var places: [2 * arm_places]ir.Place = undefined;
    var place_ids: [2 * arm_places]ir.PlaceId = undefined;
    var instructions: [2 * arm_places]ir.Instruction = undefined;
    var then_instructions: [arm_places]ir.InstructionId = undefined;
    var else_instructions: [arm_places]ir.InstructionId = undefined;
    for (0..2 * arm_places) |index| {
        const in_then = index < arm_places;
        const instruction_id = ir.InstructionId.fromIndex(index);
        place_ids[index] = ir.PlaceId.fromIndex(index);
        places[index] = .{ .id = place_ids[index], .function = function_id, .origin = .{ .instruction = instruction_id } };
        instructions[index] = .{
            .id = instruction_id,
            .block = if (in_then) then_block else else_block,
            .operation = .{ .place_write = .{ .place = place_ids[index], .value = if (in_then) selector else budget } },
            .results = &.{},
            .effects = .place_write,
        };
        if (in_then) then_instructions[index] = instruction_id else else_instructions[index - arm_places] = instruction_id;
    }
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = then_block },
            .else_edge = .{ .target = else_block },
        } } },
        .{ .id = then_block, .function = function_id, .instructions = &then_instructions, .terminator = .{ .jump = .{ .target = join } } },
        .{ .id = else_block, .function = function_id, .instructions = &else_instructions, .terminator = .{ .jump = .{ .target = join } } },
        .{ .id = join, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, budget },
        .local_places = &place_ids,
        .blocks = &.{ entry, then_block, else_block, join },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "sibling-arm-places",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };
    var scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer scope.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    errdefer report.deinit();
    try register_validation.validateWithLayout(std.testing.allocator, &report, &program, &scope, .standard_luau, strategy, flat_functions);
    return report;
}

test "a function marked flat is certified in the dispatcher layout" {
    // 99 places in each arm: the structured layout holds one arm's places at a time; the dispatcher layout declares
    // the 198 places at the root beside the two parameters and the `__lifter_pc` slot, 201 locals.
    var structured = try siblingArmPlacesReport(99, .automatic, null);
    defer structured.deinit();
    try std.testing.expect(structured.isClean());

    var unmarked = try siblingArmPlacesReport(99, .automatic, &.{false});
    defer unmarked.deinit();
    try std.testing.expect(unmarked.isClean());

    var marked = try siblingArmPlacesReport(99, .automatic, &.{true});
    defer marked.deinit();
    try std.testing.expectEqual(@as(usize, 1), marked.diagnostics.items.len);
    try std.testing.expect(marked.contains(.unsupported_readable_register_pressure));
    try std.testing.expectEqual(@as(?u32, 0), marked.diagnostics.items[0].entity_index);

    var dispatcher = try siblingArmPlacesReport(99, .dispatcher, null);
    defer dispatcher.deinit();
    try std.testing.expect(dispatcher.contains(.unsupported_readable_register_pressure));

    // 98 places in each arm: 199 locals in the dispatcher layout, admitted.
    var boundary = try siblingArmPlacesReport(98, .automatic, &.{true});
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());
}
