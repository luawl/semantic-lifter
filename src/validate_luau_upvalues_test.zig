const std = @import("std");
const diagnostics = @import("diagnostics.zig");
const emit_luau = @import("emit_luau.zig");
const ir = @import("ir.zig");
const readable_scope = @import("readable_scope.zig");
const register_validation = @import("validate_luau_registers.zig");
const validation = @import("validate.zig");

const Options = struct {
    duplicate_inner_sources: bool = false,
    use_first_capture_only: bool = false,
    runtime_capture: bool = false,
    profile: ?ir.AdmissionProfile = null,
    verify_emitter_success: bool = false,
    verify_emitter_rejection: bool = false,
};

fn upvaluePressureReport(comptime middle_parameter_count: usize, comptime options: Options) !diagnostics.Report {
    const outer_count = if (options.runtime_capture) 198 else 199;
    const inner_capture_count = outer_count + middle_parameter_count;
    const runtime_instruction_count: usize = @intFromBool(options.runtime_capture);

    const entry_closure_index = outer_count;
    const middle_capture_start = entry_closure_index + 1;
    const middle_parameter_start = middle_capture_start + outer_count;
    const middle_closure_index = middle_parameter_start + middle_parameter_count;
    const inner_capture_start = middle_closure_index + 1;
    const interpolation_result_index = inner_capture_start + inner_capture_count;
    const value_count = interpolation_result_index + runtime_instruction_count;

    const entry_function = ir.FunctionId.fromIndex(0);
    const middle_function = ir.FunctionId.fromIndex(1);
    const inner_function = ir.FunctionId.fromIndex(2);
    const entry_block = ir.BlockId.fromIndex(0);
    const middle_block = ir.BlockId.fromIndex(1);
    const inner_block = ir.BlockId.fromIndex(2);
    const make_middle = ir.InstructionId.fromIndex(0);
    const make_inner = ir.InstructionId.fromIndex(1);
    const interpolate = ir.InstructionId.fromIndex(2);
    const proof = ir.EvidenceId.fromIndex(0);
    const proof_ids = [_]ir.EvidenceId{proof};

    var values: [value_count]ir.Value = undefined;
    var entry_parameters: [outer_count]ir.ValueId = undefined;
    var middle_capture_values: [outer_count]ir.ValueId = undefined;
    var middle_parameters: [middle_parameter_count]ir.ValueId = undefined;
    var inner_capture_values: [inner_capture_count]ir.ValueId = undefined;

    var captures: [outer_count + inner_capture_count]ir.Capture = undefined;
    var middle_capture_ids: [outer_count]ir.CaptureId = undefined;
    var inner_capture_ids: [inner_capture_count]ir.CaptureId = undefined;
    var entry_bindings: [outer_count]ir.CaptureBinding = undefined;
    var inner_bindings: [inner_capture_count]ir.CaptureBinding = undefined;

    for (0..outer_count) |index| {
        const entry_value = ir.ValueId.fromIndex(index);
        entry_parameters[index] = entry_value;
        values[entry_value.index()] = .{
            .id = entry_value,
            .function = entry_function,
            .origin = .{ .parameter = @intCast(index) },
        };
        entry_bindings[index] = .{ .value = entry_value };

        const middle_capture = ir.CaptureId.fromIndex(index);
        const middle_value = ir.ValueId.fromIndex(middle_capture_start + index);
        middle_capture_ids[index] = middle_capture;
        middle_capture_values[index] = middle_value;
        values[middle_value.index()] = .{
            .id = middle_value,
            .function = middle_function,
            .origin = .{ .capture = middle_capture },
        };
        captures[middle_capture.index()] = .{
            .id = middle_capture,
            .function = middle_function,
            .kind = .{ .immutable_value = middle_value },
            .evidence = &proof_ids,
        };
    }

    const entry_closure = ir.ValueId.fromIndex(entry_closure_index);
    values[entry_closure.index()] = .{
        .id = entry_closure,
        .function = entry_function,
        .type = .function,
        .origin = .{ .instruction_result = .{ .instruction = make_middle, .index = 0 } },
    };
    for (0..middle_parameter_count) |index| {
        const parameter = ir.ValueId.fromIndex(middle_parameter_start + index);
        middle_parameters[index] = parameter;
        values[parameter.index()] = .{
            .id = parameter,
            .function = middle_function,
            .origin = .{ .parameter = @intCast(index) },
        };
    }
    const middle_closure = ir.ValueId.fromIndex(middle_closure_index);
    values[middle_closure.index()] = .{
        .id = middle_closure,
        .function = middle_function,
        .type = .function,
        .origin = .{ .instruction_result = .{ .instruction = make_inner, .index = 0 } },
    };

    for (0..inner_capture_count) |index| {
        const capture_id = ir.CaptureId.fromIndex(outer_count + index);
        const captured = ir.ValueId.fromIndex(inner_capture_start + index);
        inner_capture_ids[index] = capture_id;
        inner_capture_values[index] = captured;
        values[captured.index()] = .{
            .id = captured,
            .function = inner_function,
            .origin = .{ .capture = capture_id },
        };
        captures[capture_id.index()] = .{
            .id = capture_id,
            .function = inner_function,
            .kind = .{ .immutable_value = captured },
            .evidence = &proof_ids,
        };
        const unique_source = if (index < outer_count) middle_capture_values[index] else blk: {
            if (comptime middle_parameter_count == 0) unreachable;
            break :blk middle_parameters[index - outer_count];
        };
        inner_bindings[index] = .{ .value = if (options.duplicate_inner_sources) middle_capture_values[0] else unique_source };
    }

    const interpolation_segments = [_][]const u8{""} ** (inner_capture_count + 1);
    var instructions: [2 + runtime_instruction_count]ir.Instruction = undefined;
    instructions[make_middle.index()] = .{
        .id = make_middle,
        .block = entry_block,
        .operation = .{ .make_closure = .{ .function = middle_function, .bindings = &entry_bindings } },
        .results = &.{entry_closure},
        .effects = .pure,
        .evidence = &proof_ids,
    };
    instructions[make_inner.index()] = .{
        .id = make_inner,
        .block = middle_block,
        .operation = .{ .make_closure = .{ .function = inner_function, .bindings = &inner_bindings } },
        .results = &.{middle_closure},
        .effects = .pure,
        .evidence = &proof_ids,
    };

    var inner_instructions: [runtime_instruction_count]ir.InstructionId = undefined;
    const inner_returns: []const ir.ValueId = if (options.runtime_capture) blk: {
        const result = ir.ValueId.fromIndex(interpolation_result_index);
        values[result.index()] = .{
            .id = result,
            .function = inner_function,
            .type = .string,
            .origin = .{ .instruction_result = .{ .instruction = interpolate, .index = 0 } },
        };
        instructions[interpolate.index()] = .{
            .id = interpolate,
            .block = inner_block,
            .operation = .{ .string_interpolate = .{
                .segments = &interpolation_segments,
                .values = &inner_capture_values,
            } },
            .results = &.{result},
            .effects = .string_interpolation,
            .evidence = &proof_ids,
        };
        inner_instructions[0] = interpolate;
        break :blk &.{result};
    } else if (options.use_first_capture_only) &.{inner_capture_values[0]} else &inner_capture_values;

    const blocks = [_]ir.Block{
        .{
            .id = entry_block,
            .function = entry_function,
            .instructions = &.{make_middle},
            .terminator = .{ .return_values = &.{entry_closure} },
            .evidence = &proof_ids,
        },
        .{
            .id = middle_block,
            .function = middle_function,
            .instructions = &.{make_inner},
            .terminator = .{ .return_values = &.{middle_closure} },
            .evidence = &proof_ids,
        },
        .{
            .id = inner_block,
            .function = inner_function,
            .instructions = &inner_instructions,
            .terminator = .{ .return_values = inner_returns },
            .evidence = &proof_ids,
        },
    };
    const functions = [_]ir.Function{
        .{
            .id = entry_function,
            .parameters = &entry_parameters,
            .blocks = &.{entry_block},
            .entry_block = entry_block,
            .evidence = &proof_ids,
        },
        .{
            .id = middle_function,
            .lexical_parent = entry_function,
            .parameters = &middle_parameters,
            .captures = &middle_capture_ids,
            .blocks = &.{middle_block},
            .entry_block = middle_block,
            .evidence = &proof_ids,
        },
        .{
            .id = inner_function,
            .lexical_parent = middle_function,
            .captures = &inner_capture_ids,
            .blocks = &.{inner_block},
            .entry_block = inner_block,
            .evidence = &proof_ids,
        },
    };
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .conformance_oracle,
        .locator = "fixture:luau-upvalue-register-boundary",
    }};
    const program: ir.Program = .{
        .program_id = "luau-upvalue-register-boundary",
        .entry_function = entry_function,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .captures = &captures,
        .evidence = &evidence,
    };

    if (options.verify_emitter_success) {
        const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
        std.testing.allocator.free(source);
    }
    if (options.verify_emitter_rejection) {
        try std.testing.expectError(error.InvalidIr, emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program));
    }
    if (options.profile) |profile| return validation.validate(std.testing.allocator, &program, profile);
    var scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer scope.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    errdefer report.deinit();
    try register_validation.validate(std.testing.allocator, &report, &program, &scope, .standard_luau);
    return report;
}

test "nested closure instances enforce the independent upvalue register ceiling" {
    var boundary = try upvaluePressureReport(1, .{});
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var excessive = try upvaluePressureReport(2, .{});
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_upvalue_pressure));
}

test "stable duplicate capture sources share one emitted upvalue" {
    var report = try upvaluePressureReport(2, .{ .duplicate_inner_sources = true });
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "unused capture rows do not consume emitted upvalues" {
    var report = try upvaluePressureReport(2, .{ .use_first_capture_only = true });
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "backend runtime captures participate in upvalue admission" {
    var boundary = try upvaluePressureReport(1, .{ .runtime_capture = true });
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var excessive = try upvaluePressureReport(2, .{ .runtime_capture = true });
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_upvalue_pressure));
}

test "upvalue pressure is readable-only profile policy" {
    var boundary = try upvaluePressureReport(1, .{
        .profile = .readable_luau,
        .verify_emitter_success = true,
    });
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var core = try upvaluePressureReport(2, .{ .profile = .core });
    defer core.deinit();
    try std.testing.expect(core.isClean());

    var readable = try upvaluePressureReport(2, .{
        .profile = .readable_luau,
        .verify_emitter_rejection = true,
    });
    defer readable.deinit();
    try std.testing.expectEqual(@as(usize, 1), readable.diagnostics.items.len);
    try std.testing.expect(readable.contains(.unsupported_readable_upvalue_pressure));
}
