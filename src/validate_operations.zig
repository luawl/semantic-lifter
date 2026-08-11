const std = @import("std");
const ir = @import("ir.zig");
const numerals = @import("numerals.zig");
const luau_syntax = @import("luau_syntax.zig");
const diagnostics = @import("diagnostics.zig");
const closure_validation = @import("validate_closures.zig");
const effect_validation = @import("validate_effects.zig");
const type_validation = @import("validate_types.zig");
const readable_scope = @import("readable_scope.zig");
const readable_error_location = @import("readable_error_location.zig");

pub fn validate(
    report: *diagnostics.Report,
    program: *const ir.Program,
    instruction: ir.Instruction,
    function_id: ir.FunctionId,
    profile: ir.AdmissionProfile,
) !void {
    switch (instruction.operation) {
        .constant => |literal| {
            try requireResultCount(report, instruction, 1);
            switch (literal) {
                .integer => |decimal| {
                    if (!numerals.isCanonicalSignedDecimal(decimal)) {
                        try report.add(.invalid_integer_literal, instruction.id.index());
                        return;
                    }
                    if (profile == .readable_luau) {
                        const value = numerals.parseCanonicalSigned(i64, decimal);
                        const exact_luau_limit: i64 = 1 << 53;
                        if (value == null or value.? < -exact_luau_limit or value.? > exact_luau_limit) {
                            try report.add(.inexact_luau_integer_literal, instruction.id.index());
                        }
                    }
                },
                .number => |value| if (!std.math.isFinite(value)) {
                    try report.add(.invalid_number_literal, instruction.id.index());
                },
                else => {},
            }
        },
        .make_table => {
            try requireResultCount(report, instruction, 1);
            try effect_validation.validateTableConstructor(report, instruction);
        },
        .make_table_literal => |operation| {
            for (operation.fields) |field| switch (field) {
                .list => |value| try validateOperand(report, program, value, function_id, instruction.id.index()),
                .keyed => |keyed| {
                    try validateOperand(report, program, keyed.key, function_id, instruction.id.index());
                    try validateOperand(report, program, keyed.value, function_id, instruction.id.index());
                },
            };
            try requireResultCount(report, instruction, 1);
            try effect_validation.validateTableConstructor(report, instruction);
        },
        .string_interpolate => |operation| {
            for (operation.values) |value| try validateOperand(report, program, value, function_id, instruction.id.index());
            if (operation.segments.len != operation.values.len + 1) {
                try report.add(.invalid_string_interpolation_shape, instruction.id.index());
            }
            try requireResultCount(report, instruction, 1);
            try effect_validation.validateStringInterpolation(report, instruction);
        },
        .function_ref => |target| {
            try requireResultCount(report, instruction, 1);
            try closure_validation.validateFunctionReference(report, program, target, instruction.id.index());
        },
        .environment_get => |operation| {
            try validateEnvironmentTarget(report, program, operation.target, function_id, instruction.id.index());
            try requireResultCount(report, instruction, 1);
            try effect_validation.validateEnvironmentGet(report, program, instruction, operation);
        },
        .copy => |operand| {
            try validateOperand(report, program, operand, function_id, instruction.id.index());
            try requireResultCount(report, instruction, 1);
        },
        .unary => |operation| {
            try validateOperand(report, program, operation.operand, function_id, instruction.id.index());
            try requireResultCount(report, instruction, 1);
            try effect_validation.validateUnary(report, program, instruction, operation);
        },
        .binary => |operation| {
            try validateOperand(report, program, operation.left, function_id, instruction.id.index());
            try validateOperand(report, program, operation.right, function_id, instruction.id.index());
            try requireResultCount(report, instruction, 1);
            try validateShiftBehavior(report, instruction.id, operation);
            try effect_validation.validateBinary(report, program, instruction, operation);
        },
        .call => |operation| {
            try validateOperand(report, program, operation.callee, function_id, instruction.id.index());
            for (operation.arguments) |argument| try validateOperand(report, program, argument, function_id, instruction.id.index());
            switch (operation.result_arity) {
                .fixed => |count| if (instruction.results.len != count) try report.add(.invalid_result_arity, instruction.id.index()),
                .variadic => {},
            }
            try effect_validation.validateCall(report, program, instruction);
        },
        .call_repeated_table_get => |operation| {
            try validateOperand(report, program, operation.callee, function_id, instruction.id.index());
            for (operation.prefix_arguments) |argument| try validateOperand(report, program, argument, function_id, instruction.id.index());
            try validateOperand(report, program, operation.table, function_id, instruction.id.index());
            try validateOperand(report, program, operation.key, function_id, instruction.id.index());
            try validateOperand(report, program, operation.from, function_id, instruction.id.index());
            try validateOperand(report, program, operation.to, function_id, instruction.id.index());
            try validateOperand(report, program, operation.step, function_id, instruction.id.index());
            if (operation.counter) |counter| try validatePlaceOperand(report, program, counter, function_id, instruction.id.index());
            switch (operation.result_arity) {
                .fixed => |count| if (instruction.results.len != count) try report.add(.invalid_result_arity, instruction.id.index()),
                .variadic => {},
            }
            try effect_validation.validateCall(report, program, instruction);
        },
        .namecall => |operation| {
            try validateOperand(report, program, operation.receiver, function_id, instruction.id.index());
            for (operation.arguments) |argument| try validateOperand(report, program, argument, function_id, instruction.id.index());
            switch (operation.result_arity) {
                .fixed => |count| if (instruction.results.len != count) try report.add(.invalid_result_arity, instruction.id.index()),
                .variadic => {},
            }
            try effect_validation.validateNamecall(report, instruction);
        },
        .protected_call => |operation| {
            try validateOperand(report, program, operation.callee, function_id, instruction.id.index());
            if (operation.error_handler) |handler| try validateOperand(report, program, handler, function_id, instruction.id.index());
            for (operation.arguments) |argument| try validateOperand(report, program, argument, function_id, instruction.id.index());
            try validateStatusResult(report, program, instruction, operation.result_arity);
            try effect_validation.validateProtectedCall(report, instruction);
        },
        .coroutine_create => |operation| {
            try validateOperand(report, program, operation.callee, function_id, instruction.id.index());
            try requireResultCount(report, instruction, 1);
            if (instruction.results.len == 1 and validId(instruction.results[0], program.values.len)) {
                const kind = program.values[instruction.results[0].index()].type.kind;
                if (kind != .thread and kind != .dynamic) try report.add(.invalid_coroutine_value_type, instruction.id.index());
            }
            try effect_validation.validateCoroutineCreate(report, instruction);
        },
        .coroutine_resume => |operation| {
            try validateOperand(report, program, operation.thread, function_id, instruction.id.index());
            if (validId(operation.thread, program.values.len)) {
                const kind = program.values[operation.thread.index()].type.kind;
                if (kind != .thread and kind != .dynamic) try report.add(.invalid_coroutine_value_type, instruction.id.index());
            }
            for (operation.arguments) |argument| try validateOperand(report, program, argument, function_id, instruction.id.index());
            try validateStatusResult(report, program, instruction, operation.result_arity);
            try effect_validation.validateCoroutineResume(report, instruction);
        },
        .coroutine_yield => |operation| {
            for (operation.arguments) |argument| try validateOperand(report, program, argument, function_id, instruction.id.index());
            try effect_validation.validateCoroutineYield(report, instruction);
        },
        .pack_values => |values| {
            for (values) |value| try validateOperand(report, program, value, function_id, instruction.id.index());
            try requireResultCount(report, instruction, 0);
        },
        .adjust_pack => {},
        .environment_set => |operation| {
            try validateEnvironmentTarget(report, program, operation.target, function_id, instruction.id.index());
            try validateOperand(report, program, operation.value, function_id, instruction.id.index());
            try requireResultCount(report, instruction, 0);
            try effect_validation.validateEnvironmentSet(report, program, instruction, operation);
        },
        .table_get => |operation| {
            try validateOperand(report, program, operation.table, function_id, instruction.id.index());
            try validateOperand(report, program, operation.key, function_id, instruction.id.index());
            try requireResultCount(report, instruction, 1);
            try effect_validation.validateTableGet(report, program, instruction, operation);
        },
        .table_set => |operation| {
            try validateOperand(report, program, operation.table, function_id, instruction.id.index());
            try validateOperand(report, program, operation.key, function_id, instruction.id.index());
            try validateOperand(report, program, operation.value, function_id, instruction.id.index());
            try requireResultCount(report, instruction, 0);
            try effect_validation.validateTableSet(report, program, instruction, operation);
        },
        .table_set_pack => |operation| {
            try validateOperand(report, program, operation.table, function_id, instruction.id.index());
            try requireResultCount(report, instruction, 0);
            try effect_validation.validateTableSetPack(report, instruction);
        },
        .make_closure => |operation| {
            try requireResultCount(report, instruction, 1);
            try closure_validation.validateClosureOperation(report, program, operation, function_id, instruction.id.index());
        },
        .place_read => |place_id| {
            try requireResultCount(report, instruction, 1);
            try closure_validation.validatePlaceRead(report, program, place_id, function_id, instruction.effects, instruction.id.index());
        },
        .place_write => |operation| {
            try requireResultCount(report, instruction, 0);
            try closure_validation.validatePlaceWrite(report, program, operation, function_id, instruction.effects, instruction.id.index());
        },
        .numeric_for_next => |operation| {
            try validateOperand(report, program, operation.control, function_id, instruction.id.index());
            try validateOperand(report, program, operation.limit, function_id, instruction.id.index());
            try validateOperand(report, program, operation.step, function_id, instruction.id.index());
            try validateOperand(report, program, operation.initial, function_id, instruction.id.index());
            try validateBooleanOperand(report, program, operation.initial, instruction.id.index());
            try requireResultCount(report, instruction, 4);
            try effect_validation.validateNumericForNext(report, instruction, operation);
        },
        .generic_for_next => |operation| {
            try validateOperand(report, program, operation.iterator, function_id, instruction.id.index());
            try validateOperand(report, program, operation.state, function_id, instruction.id.index());
            try validateOperand(report, program, operation.control, function_id, instruction.id.index());
            try validateOperand(report, program, operation.initial, function_id, instruction.id.index());
            try validateBooleanOperand(report, program, operation.initial, instruction.id.index());
            if (operation.variable_count == 0) {
                try report.add(.invalid_iteration_variable_count, instruction.id.index());
            }
            try requireResultCount(report, instruction, @as(usize, operation.variable_count) + 3);
            try effect_validation.validateGenericForNext(report, instruction);
        },
    }
}

fn validateShiftBehavior(report: *diagnostics.Report, instruction_id: ir.InstructionId, operation: ir.Binary) !void {
    const is_shift = operation.operator == .shift_left or operation.operator == .shift_right;
    if (is_shift and operation.shift_behavior == null) {
        try report.add(.missing_shift_behavior, instruction_id.index());
    } else if (!is_shift and operation.shift_behavior != null) {
        try report.add(.unexpected_shift_behavior, instruction_id.index());
    }
}

pub fn validateReadableCapabilities(report: *diagnostics.Report, program: *const ir.Program, scope: *const readable_scope.Scope) !void {
    for (program.blocks, 0..) |block, block_index| if (scope.block(block.id)) switch (block.terminator) {
        .unreachable_block => try report.add(.unsupported_readable_terminator, block_index),
        .throw_error => |throw_error| if (errorLocationIsUnsupported(program, scope, block.id, throw_error)) {
            try report.add(.unsupported_readable_error_location, block_index);
        },
        else => {},
    };

    for (program.instructions, 0..) |instruction, instruction_index| {
        if (!scope.instruction(instruction.id)) continue;
        switch (instruction.operation) {
            .unary => |operation| if (operation.operator == .bit_not and
                !type_validation.supportsReadableBit32Unary(program, instruction, operation))
            {
                try report.add(.unsupported_readable_bit_operation, instruction_index);
            },
            .binary => |operation| switch (operation.operator) {
                .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => if (!type_validation.supportsReadableBit32Binary(program, instruction, operation)) {
                    try report.add(.unsupported_readable_bit_operation, instruction_index);
                },
                else => {},
            },
            .namecall => |operation| if (!luau_syntax.isIdentifier(operation.method)) {
                // Bracket dispatch changes native NAMECALL lookup order and missing-method errors.
                try report.add(.unsupported_readable_namecall, instruction_index);
            },
            else => {},
        }
    }
}

fn errorLocationIsUnsupported(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    block_id: ir.BlockId,
    throw_error: ir.ThrowError,
) bool {
    if (throw_error.dynamic_level) |level| {
        if (!validId(throw_error.value, program.values.len) or !validId(level, program.values.len)) return true;
        if (!readable_error_location.levelIsNumeric(program.values[level.index()].type.kind)) return true;
        return readable_error_location.messageMayIncludeSourceLocation(program.values[throw_error.value.index()].type.kind) and
            !readable_error_location.hasNonpositiveRequirement(program, scope, block_id, level);
    }
    return throw_error.level > 0 and
        validId(throw_error.value, program.values.len) and
        readable_error_location.messageMayIncludeSourceLocation(program.values[throw_error.value.index()].type.kind);
}

fn requireResultCount(report: *diagnostics.Report, instruction: ir.Instruction, expected: usize) !void {
    if (instruction.results.len != expected) try report.add(.invalid_result_arity, instruction.id.index());
}

fn validateStatusResult(report: *diagnostics.Report, program: *const ir.Program, instruction: ir.Instruction, arity: ir.ResultArity) !void {
    switch (arity) {
        .fixed => |count| {
            if (count == 0 or instruction.results.len == 0) {
                try report.add(.missing_status_result, instruction.id.index());
                return;
            }
            const status_id = instruction.results[0];
            if (!validId(status_id, program.values.len)) return;
            const kind = program.values[status_id.index()].type.kind;
            if (kind != .boolean and kind != .dynamic) try report.add(.invalid_status_result_type, instruction.id.index());
        },
        .variadic => {},
    }
}

pub fn validateOperand(
    report: *diagnostics.Report,
    program: *const ir.Program,
    value_id: ir.ValueId,
    function_id: ir.FunctionId,
    entity_index: usize,
) !void {
    if (!validId(value_id, program.values.len)) {
        try report.add(.invalid_operand, entity_index);
        return;
    }
    if (program.values[value_id.index()].function != function_id) try report.add(.cross_function_operand, entity_index);
}

fn validateEnvironmentTarget(
    report: *diagnostics.Report,
    program: *const ir.Program,
    target: ir.EnvironmentTarget,
    function_id: ir.FunctionId,
    entity_index: usize,
) !void {
    switch (target) {
        .ambient => {},
        .value => |value_id| try validateOperand(report, program, value_id, function_id, entity_index),
    }
}

fn validatePlaceOperand(
    report: *diagnostics.Report,
    program: *const ir.Program,
    place_id: ir.PlaceId,
    function_id: ir.FunctionId,
    entity_index: usize,
) !void {
    if (!validId(place_id, program.places.len)) {
        try report.add(.invalid_place_operand, entity_index);
    } else if (program.places[place_id.index()].function != function_id) {
        try report.add(.cross_function_place, entity_index);
    }
}

fn validateBooleanOperand(report: *diagnostics.Report, program: *const ir.Program, value_id: ir.ValueId, entity_index: usize) !void {
    if (!validId(value_id, program.values.len)) return;
    if (program.values[value_id.index()].type.kind != .boolean) {
        try report.add(.invalid_iteration_initial_type, entity_index);
    }
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}
