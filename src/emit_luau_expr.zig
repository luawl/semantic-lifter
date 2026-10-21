const std = @import("std");
const ir = @import("ir.zig");
const dead_code = @import("dead_code.zig");
const luau_runtime = @import("luau_runtime.zig");
const luau_syntax = @import("luau_syntax.zig");
const pack_plan = @import("pack_plan.zig");
const place_read_fusion = @import("place_read_fusion.zig");
const value_fusion = @import("value_fusion.zig");
const place_render = @import("emit_luau_place.zig");
const name_plan = @import("name_plan.zig");

pub const RenderError = std.mem.Allocator.Error || error{UnsupportedOperation};

pub const ValueOverride = struct {
    context: ?*anyopaque,
    contains_fn: *const fn (context: ?*anyopaque, value_id: ir.ValueId) bool,
    emit_fn: *const fn (
        context: ?*anyopaque,
        output: *std.ArrayList(u8),
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        plan: ValuePlan,
        value_id: ir.ValueId,
    ) RenderError!void,

    pub fn contains(self: ValueOverride, value_id: ir.ValueId) bool {
        return self.contains_fn(self.context, value_id);
    }

    pub fn emit(
        self: ValueOverride,
        output: *std.ArrayList(u8),
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        plan: ValuePlan,
        value_id: ir.ValueId,
    ) RenderError!void {
        return self.emit_fn(self.context, output, allocator, program, plan, value_id);
    }
};

pub const ValuePlan = struct {
    names: *const name_plan.Plan,
    dead: *const dead_code.Plan,
    place_reads: *const place_read_fusion.Plan,
    fused_values: *const value_fusion.Plan,
    packs: *const pack_plan.Plan,
    place_aliases: []const place_render.Alias,
    value_override: ?ValueOverride = null,
};

const OperandSide = enum {
    left,
    right,
};

const ExpressionContext = union(enum) {
    grouped,
    root,
    unary_operand,
    binary_operand: struct {
        operator: ir.BinaryOperator,
        side: OperandSide,
    },
};

const ResultContext = enum {
    preserve_adjustment,
    implicit_single,
};

pub fn expression(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, operation: ir.Operation) RenderError!void {
    try expressionWithContext(output, allocator, program, plan, operation, .grouped, .preserve_adjustment);
}

pub fn expressionRoot(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, operation: ir.Operation) RenderError!void {
    try expressionWithContext(output, allocator, program, plan, operation, .root, .preserve_adjustment);
}

fn expressionWithContext(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, operation: ir.Operation, context: ExpressionContext, result_context: ResultContext) RenderError!void {
    switch (operation) {
        .constant => |value| {
            const wrapped = expressionNeedsParentheses(operation, context);
            if (wrapped) try output.append(allocator, '(');
            try literal(output, allocator, value);
            if (wrapped) try output.append(allocator, ')');
        },
        .copy => |value| try valueUseContext(output, allocator, program, plan, value, context, result_context),
        .unary => |value| try unary(output, allocator, program, plan, value, context),
        .binary => |value| try binary(output, allocator, program, plan, value, context),
        .call, .namecall, .protected_call, .coroutine_create, .coroutine_resume, .coroutine_yield => try invocation(output, allocator, program, plan, operation),
        .environment_get => |value| try environmentGet(output, allocator, program, plan, value),
        .table_get => |value| {
            switch (value.mode) {
                .semantic => try semanticTableAddress(output, allocator, program, plan, value.table, value.key),
                .raw => {
                    try runtimeCallStart(output, allocator, plan, .rawget);
                    try valueUseScalar(output, allocator, program, plan, value.table);
                    try output.appendSlice(allocator, ", ");
                    try valueUseRoot(output, allocator, program, plan, value.key);
                    try output.append(allocator, ')');
                },
            }
        },
        .make_table => try output.appendSlice(allocator, "{}"),
        .string_interpolate => |value| try interpolation(output, allocator, program, plan, value),
        .function_ref => |function_id| try functionName(output, allocator, plan.names, function_id),
        else => return error.UnsupportedOperation,
    }
}

fn interpolation(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    value: ir.StringInterpolation,
) !void {
    if (value.segments.len != value.values.len + 1) return error.UnsupportedOperation;
    var format: std.ArrayList(u8) = .empty;
    defer format.deinit(allocator);
    for (value.segments, 0..) |segment, index| {
        for (segment) |byte| {
            try format.append(allocator, byte);
            if (byte == '%') try format.append(allocator, '%');
        }
        if (index < value.values.len) try format.appendSlice(allocator, "%*");
    }

    try runtimeCallStart(output, allocator, plan, .string_format);
    try literal(output, allocator, .{ .string = format.items });
    if (value.values.len != 0) {
        try output.appendSlice(allocator, ", ");
        try valueUseList(output, allocator, program, plan, value.values, false);
    }
    try output.append(allocator, ')');
}

pub fn statement(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, operation: ir.Operation) !void {
    switch (operation) {
        .call, .namecall, .protected_call, .coroutine_create, .coroutine_resume, .coroutine_yield => try invocation(output, allocator, program, plan, operation),
        .environment_set => |value| try environmentSet(output, allocator, program, plan, value),
        .table_set => |value| {
            switch (value.mode) {
                .semantic => {
                    try semanticTableAddress(output, allocator, program, plan, value.table, value.key);
                    try output.appendSlice(allocator, " = ");
                    try valueUseScalar(output, allocator, program, plan, value.value);
                },
                .raw => {
                    try runtimeCallStart(output, allocator, plan, .rawset);
                    try valueUseScalar(output, allocator, program, plan, value.table);
                    try output.appendSlice(allocator, ", ");
                    try valueUseScalar(output, allocator, program, plan, value.key);
                    try output.appendSlice(allocator, ", ");
                    try valueUseRoot(output, allocator, program, plan, value.value);
                    try output.append(allocator, ')');
                },
            }
        },
        else => return error.UnsupportedOperation,
    }
}

pub fn semanticTableAddress(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    table: ir.ValueId,
    key: ir.ValueId,
) !void {
    try valueUsePostfix(output, allocator, program, plan, table);
    try semanticValueIndexSuffix(output, allocator, program, plan, key);
}

pub fn statementNeedsSeparator(program: *const ir.Program, plan: ValuePlan, operation: ir.Operation) bool {
    return switch (operation) {
        .call => |value| valueUsePostfixStartsWithParenthesis(program, plan, value.callee, program.instructions.len + 1),
        .namecall => |value| valueUsePostfixStartsWithParenthesis(program, plan, value.receiver, program.instructions.len + 1),
        .environment_set => |value| switch (value.target) {
            .ambient => false,
            .value => |environment| value.mode == .semantic and valueUsePostfixStartsWithParenthesis(program, plan, environment, program.instructions.len + 1),
        },
        .table_set => |value| value.mode == .semantic and valueUsePostfixStartsWithParenthesis(program, plan, value.table, program.instructions.len + 1),
        else => false,
    };
}

pub fn globalIdentifier(output: *std.ArrayList(u8), allocator: std.mem.Allocator, name: []const u8) !void {
    std.debug.assert(luau_syntax.isIdentifier(name));
    try output.appendSlice(allocator, name);
}

pub fn runtimeCallStart(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    plan: ValuePlan,
    capability: luau_runtime.Capability,
) RenderError!void {
    const capture = plan.names.runtimeCapability(capability) orelse return error.UnsupportedOperation;
    try globalIdentifier(output, allocator, capture);
    try output.append(allocator, '(');
}

pub fn directVarargPackExpression(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    pack_id: ir.ValuePackId,
) RenderError!void {
    if (pack_id.index() >= program.value_packs.len) return error.UnsupportedOperation;
    const owner = switch (program.value_packs[pack_id.index()].origin) {
        .varargs => |function_id| function_id,
        .instruction_result => return error.UnsupportedOperation,
    };
    if (owner.index() >= program.functions.len) return error.UnsupportedOperation;
    const function = program.functions[owner.index()];
    if (!function.is_variadic or function.vararg_pack == null or function.vararg_pack.? != pack_id) return error.UnsupportedOperation;
    const fixed_prefix = std.math.add(usize, function.parameters.len, program.external_bindings.len) catch return error.UnsupportedOperation;
    if (owner != program.entry_function or fixed_prefix == 0) {
        try output.appendSlice(allocator, "...");
        return;
    }
    const first_tail_index = std.math.add(usize, fixed_prefix, 1) catch return error.UnsupportedOperation;
    try runtimeCallStart(output, allocator, plan, .select);
    try output.print(allocator, "{d}, ...)", .{first_tail_index});
}

pub fn semanticValueIndexSuffix(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    key: ir.ValueId,
) RenderError!void {
    if (valueIdentifierKey(program, plan, key)) |name| {
        try output.append(allocator, '.');
        try globalIdentifier(output, allocator, name);
        return;
    }
    try output.append(allocator, '[');
    try valueUseScalar(output, allocator, program, plan, key);
    try output.append(allocator, ']');
}

pub fn semanticStringIndexSuffix(output: *std.ArrayList(u8), allocator: std.mem.Allocator, name: []const u8) !void {
    if (luau_syntax.isIdentifier(name)) {
        try output.append(allocator, '.');
        try globalIdentifier(output, allocator, name);
        return;
    }
    try output.append(allocator, '[');
    try literal(output, allocator, .{ .string = name });
    try output.append(allocator, ']');
}

pub fn semanticConstructorKey(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    key: ir.ValueId,
) RenderError!void {
    if (valueIdentifierKey(program, plan, key)) |name| {
        try globalIdentifier(output, allocator, name);
        return;
    }
    try output.append(allocator, '[');
    try valueUseScalar(output, allocator, program, plan, key);
    try output.append(allocator, ']');
}

fn valueIdentifierKey(program: *const ir.Program, plan: ValuePlan, key: ir.ValueId) ?[]const u8 {
    const lexical_value = place_render.resolveValue(key, plan.place_aliases) orelse return null;
    const resolved = plan.dead.resolveValue(lexical_value);
    if (resolved.index() >= program.values.len) return null;
    const origin = switch (program.values[resolved.index()].origin) {
        .instruction_result => |value| value,
        else => return null,
    };
    if (origin.index != 0 or origin.instruction.index() >= program.instructions.len) return null;
    const name = switch (program.instructions[origin.instruction.index()].operation) {
        .constant => |literal_value| switch (literal_value) {
            .string => |value| value,
            else => return null,
        },
        else => return null,
    };
    return if (luau_syntax.isIdentifier(name)) name else null;
}

fn environmentGet(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    operation: ir.EnvironmentGet,
) !void {
    switch (operation.mode) {
        .semantic => try semanticEnvironmentAddress(output, allocator, program, plan, operation.target, operation.name),
        .raw => switch (operation.target) {
            .ambient => return error.UnsupportedOperation,
            .value => |environment| {
                try runtimeCallStart(output, allocator, plan, .rawget);
                try valueUseScalar(output, allocator, program, plan, environment);
                try output.appendSlice(allocator, ", ");
                try literal(output, allocator, .{ .string = operation.name });
                try output.append(allocator, ')');
            },
        },
    }
}

fn environmentSet(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    operation: ir.EnvironmentSet,
) !void {
    switch (operation.mode) {
        .semantic => {
            try semanticEnvironmentAddress(output, allocator, program, plan, operation.target, operation.name);
            try output.appendSlice(allocator, " = ");
            try valueUseScalar(output, allocator, program, plan, operation.value);
        },
        .raw => switch (operation.target) {
            .ambient => return error.UnsupportedOperation,
            .value => |environment| {
                try runtimeCallStart(output, allocator, plan, .rawset);
                try valueUseScalar(output, allocator, program, plan, environment);
                try output.appendSlice(allocator, ", ");
                try literal(output, allocator, .{ .string = operation.name });
                try output.appendSlice(allocator, ", ");
                try valueUseRoot(output, allocator, program, plan, operation.value);
                try output.append(allocator, ')');
            },
        },
    }
}

pub fn semanticEnvironmentAddress(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    target: ir.EnvironmentTarget,
    name: []const u8,
) !void {
    switch (target) {
        .ambient => if (luau_syntax.isIdentifier(name)) {
            try globalIdentifier(output, allocator, name);
        } else {
            try runtimeCallStart(output, allocator, plan, .getfenv);
            try output.append(allocator, ')');
            try semanticStringIndexSuffix(output, allocator, name);
        },
        .value => |environment| {
            try valueUsePostfix(output, allocator, program, plan, environment);
            try semanticStringIndexSuffix(output, allocator, name);
        },
    }
}

pub fn call(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, value: ir.Call) !void {
    try valueUsePostfix(output, allocator, program, plan, value.callee);
    try output.append(allocator, '(');
    try arguments(output, allocator, program, plan, value.arguments, value.argument_pack, false);
    try output.append(allocator, ')');
}

pub fn invocation(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, operation: ir.Operation) !void {
    switch (operation) {
        .call => |value| try call(output, allocator, program, plan, value),
        .namecall => |value| try namecall(output, allocator, program, plan, value),
        .protected_call => |value| {
            try runtimeCallStart(output, allocator, plan, if (value.error_handler == null) .pcall else .xpcall);
            const callee_has_following = value.error_handler != null or value.arguments.len != 0 or value.argument_pack != null;
            if (callee_has_following)
                try valueUseScalar(output, allocator, program, plan, value.callee)
            else
                try valueUseRoot(output, allocator, program, plan, value.callee);
            if (value.error_handler) |handler| {
                try output.appendSlice(allocator, ", ");
                if (value.arguments.len != 0 or value.argument_pack != null)
                    try valueUseScalar(output, allocator, program, plan, handler)
                else
                    try valueUseRoot(output, allocator, program, plan, handler);
            }
            try arguments(output, allocator, program, plan, value.arguments, value.argument_pack, true);
            try output.append(allocator, ')');
        },
        .coroutine_create => |value| {
            try runtimeCallStart(output, allocator, plan, .coroutine_create);
            try valueUseRoot(output, allocator, program, plan, value.callee);
            try output.append(allocator, ')');
        },
        .coroutine_resume => |value| {
            try runtimeCallStart(output, allocator, plan, .coroutine_resume);
            if (value.arguments.len != 0 or value.argument_pack != null)
                try valueUseScalar(output, allocator, program, plan, value.thread)
            else
                try valueUseRoot(output, allocator, program, plan, value.thread);
            try arguments(output, allocator, program, plan, value.arguments, value.argument_pack, true);
            try output.append(allocator, ')');
        },
        .coroutine_yield => |value| {
            try runtimeCallStart(output, allocator, plan, .coroutine_yield);
            try arguments(output, allocator, program, plan, value.arguments, value.argument_pack, false);
            try output.append(allocator, ')');
        },
        else => return error.UnsupportedOperation,
    }
}

fn namecall(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    value: ir.Namecall,
) !void {
    try valueUsePostfix(output, allocator, program, plan, value.receiver);
    try output.append(allocator, ':');
    try globalIdentifier(output, allocator, value.method);
    try output.append(allocator, '(');
    try arguments(output, allocator, program, plan, value.arguments, value.argument_pack, false);
    try output.append(allocator, ')');
}

pub fn plannedInvocation(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    packs: *const pack_plan.Plan,
    instruction: ir.Instruction,
) RenderError!void {
    switch (instruction.operation) {
        .call => |value| {
            try valueUsePostfix(output, allocator, program, plan, value.callee);
            try output.append(allocator, '(');
            try plannedArguments(output, allocator, program, plan, packs, instruction.id, value.arguments, value.argument_pack, false);
            try output.append(allocator, ')');
        },
        .namecall => |value| try plannedNamecall(output, allocator, program, plan, packs, instruction.id, value),
        .protected_call => |value| {
            try runtimeCallStart(output, allocator, plan, if (value.error_handler == null) .pcall else .xpcall);
            const callee_has_following = value.error_handler != null or value.arguments.len != 0 or value.argument_pack != null;
            if (callee_has_following)
                try valueUseScalar(output, allocator, program, plan, value.callee)
            else
                try valueUseRoot(output, allocator, program, plan, value.callee);
            if (value.error_handler) |handler| {
                try output.appendSlice(allocator, ", ");
                if (value.arguments.len != 0 or value.argument_pack != null)
                    try valueUseScalar(output, allocator, program, plan, handler)
                else
                    try valueUseRoot(output, allocator, program, plan, handler);
            }
            try plannedArguments(output, allocator, program, plan, packs, instruction.id, value.arguments, value.argument_pack, true);
            try output.append(allocator, ')');
        },
        .coroutine_create => |value| {
            try runtimeCallStart(output, allocator, plan, .coroutine_create);
            try valueUseRoot(output, allocator, program, plan, value.callee);
            try output.append(allocator, ')');
        },
        .coroutine_resume => |value| {
            try runtimeCallStart(output, allocator, plan, .coroutine_resume);
            if (value.arguments.len != 0 or value.argument_pack != null)
                try valueUseScalar(output, allocator, program, plan, value.thread)
            else
                try valueUseRoot(output, allocator, program, plan, value.thread);
            try plannedArguments(output, allocator, program, plan, packs, instruction.id, value.arguments, value.argument_pack, true);
            try output.append(allocator, ')');
        },
        .coroutine_yield => |value| {
            try runtimeCallStart(output, allocator, plan, .coroutine_yield);
            try plannedArguments(output, allocator, program, plan, packs, instruction.id, value.arguments, value.argument_pack, false);
            try output.append(allocator, ')');
        },
        else => return error.UnsupportedOperation,
    }
}

fn plannedNamecall(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    packs: *const pack_plan.Plan,
    consumer: ir.InstructionId,
    value: ir.Namecall,
) RenderError!void {
    try valueUsePostfix(output, allocator, program, plan, value.receiver);
    try output.append(allocator, ':');
    try globalIdentifier(output, allocator, value.method);
    try output.append(allocator, '(');
    try plannedArguments(output, allocator, program, plan, packs, consumer, value.arguments, value.argument_pack, false);
    try output.append(allocator, ')');
}

fn plannedArguments(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    packs: *const pack_plan.Plan,
    consumer: ir.InstructionId,
    values: []const ir.ValueId,
    argument_pack: ?ir.ValuePackId,
    has_prefix: bool,
) RenderError!void {
    for (values, 0..) |argument, index| {
        if (has_prefix or index != 0) try output.appendSlice(allocator, ", ");
        if (index + 1 < values.len or argument_pack != null)
            try valueUseScalar(output, allocator, program, plan, argument)
        else
            try valueUseRoot(output, allocator, program, plan, argument);
    }
    if (argument_pack) |pack_id| {
        if (has_prefix or values.len != 0) try output.appendSlice(allocator, ", ");
        if (pack_id.index() >= program.value_packs.len) return error.UnsupportedOperation;
        switch (program.value_packs[pack_id.index()].origin) {
            .varargs => try directVarargPackExpression(output, allocator, program, plan, pack_id),
            .instruction_result => |producer_id| {
                if (producer_id.index() >= program.instructions.len) return error.UnsupportedOperation;
                const producer = program.instructions[producer_id.index()];
                switch (producer.operation) {
                    .pack_values => {
                        if (!packs.packValuesServesInstruction(producer_id, consumer)) return error.UnsupportedOperation;
                        try plannedPackValues(output, allocator, program, plan, producer);
                    },
                    else => {
                        if (packs.storedPackServesInstruction(producer_id, consumer)) {
                            try storedPackExpansion(output, allocator, plan, pack_id);
                            return;
                        }
                        const target = switch (packs.role(producer_id)) {
                            .fused_invocation_producer => |instruction_id| instruction_id,
                            else => return error.UnsupportedOperation,
                        };
                        if (target != consumer) return error.UnsupportedOperation;
                        try plannedInvocation(output, allocator, program, plan, packs, producer);
                    },
                }
            },
        }
    }
}

fn arguments(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    values: []const ir.ValueId,
    argument_pack: ?ir.ValuePackId,
    has_prefix: bool,
) !void {
    for (values, 0..) |argument, index| {
        if (has_prefix or index != 0) try output.appendSlice(allocator, ", ");
        if (index + 1 < values.len or argument_pack != null)
            try valueUseScalar(output, allocator, program, plan, argument)
        else
            try valueUseRoot(output, allocator, program, plan, argument);
    }
    if (argument_pack) |pack_id| {
        if (has_prefix or values.len != 0) try output.appendSlice(allocator, ", ");
        switch (program.value_packs[pack_id.index()].origin) {
            .varargs => try directVarargPackExpression(output, allocator, program, plan, pack_id),
            else => return error.UnsupportedOperation,
        }
    }
}

fn unary(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, value: ir.Unary, context: ExpressionContext) !void {
    if (value.operator == .bit_not) {
        try runtimeCallStart(output, allocator, plan, .bit32_bnot);
        try valueUseRoot(output, allocator, program, plan, value.operand);
        try output.append(allocator, ')');
        return;
    }
    const operator = switch (value.operator) {
        .logical_not => "not ",
        .negate => "-",
        .length => "#",
        .bit_not => unreachable,
    };
    const wrapped = expressionNeedsParentheses(.{ .unary = value }, context);
    if (wrapped) try output.append(allocator, '(');
    try output.appendSlice(allocator, operator);
    if (value.operator == .negate and valueUseStartsWithMinus(program, plan, value.operand, program.values.len + 1)) {
        try output.append(allocator, '(');
        try valueUseContext(output, allocator, program, plan, value.operand, .root, .implicit_single);
        try output.append(allocator, ')');
    } else {
        try valueUseContext(output, allocator, program, plan, value.operand, .unary_operand, .implicit_single);
    }
    if (wrapped) try output.append(allocator, ')');
}

fn binary(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, value: ir.Binary, context: ExpressionContext) !void {
    if (luau_runtime.bit32Capability(value.operator)) |capability| {
        const is_shift = value.operator == .shift_left or value.operator == .shift_right;
        if (is_shift) {
            switch (value.shift_behavior orelse return error.UnsupportedOperation) {
                .luau_bit32 => try bit32BinaryCall(output, allocator, program, plan, capability, value),
                .zero_saturating => {
                    try output.appendSlice(allocator, "(if ");
                    try valueUseScalar(output, allocator, program, plan, value.right);
                    try output.appendSlice(allocator, " >= 32 then 0 else ");
                    try bit32BinaryCall(output, allocator, program, plan, capability, value);
                    try output.append(allocator, ')');
                },
            }
        } else {
            if (value.shift_behavior != null) return error.UnsupportedOperation;
            try bit32BinaryCall(output, allocator, program, plan, capability, value);
        }
        return;
    }
    const wrapped = expressionNeedsParentheses(.{ .binary = value }, context);
    if (wrapped) try output.append(allocator, '(');
    try valueUseContext(output, allocator, program, plan, value.left, .{ .binary_operand = .{ .operator = value.operator, .side = .left } }, .implicit_single);
    try output.append(allocator, ' ');
    try output.appendSlice(allocator, binaryOperator(value.operator));
    try output.append(allocator, ' ');
    try valueUseContext(output, allocator, program, plan, value.right, .{ .binary_operand = .{ .operator = value.operator, .side = .right } }, .implicit_single);
    if (wrapped) try output.append(allocator, ')');
}

fn bit32BinaryCall(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    capability: luau_runtime.Capability,
    value: ir.Binary,
) !void {
    try runtimeCallStart(output, allocator, plan, capability);
    try valueUseScalar(output, allocator, program, plan, value.left);
    try output.appendSlice(allocator, ", ");
    try valueUseRoot(output, allocator, program, plan, value.right);
    try output.append(allocator, ')');
}

const Precedence = enum(u8) {
    logical_or = 1,
    logical_and = 2,
    comparison = 3,
    concat = 4,
    additive = 5,
    multiplicative = 6,
    unary = 7,
    power = 8,
};

const Associativity = enum {
    left,
    right,
};

fn expressionNeedsParentheses(operation: ir.Operation, context: ExpressionContext) bool {
    const child_precedence = operationPrecedence(operation) orelse return false;
    return switch (context) {
        .grouped => true,
        .root => false,
        .unary_operand => @intFromEnum(child_precedence) < @intFromEnum(Precedence.unary),
        .binary_operand => |parent| blk: {
            const parent_precedence = binaryPrecedence(parent.operator);
            if (@intFromEnum(child_precedence) < @intFromEnum(parent_precedence)) break :blk true;
            if (@intFromEnum(child_precedence) > @intFromEnum(parent_precedence)) break :blk false;
            break :blk switch (binaryAssociativity(parent.operator)) {
                .left => parent.side == .right,
                .right => parent.side == .left,
            };
        },
    };
}

fn operationPrecedence(operation: ir.Operation) ?Precedence {
    return switch (operation) {
        .constant => |value| if (literalStartsWithMinus(value)) .unary else null,
        .unary => |value| if (value.operator == .bit_not) null else .unary,
        .binary => |value| if (luau_runtime.bit32Capability(value.operator) != null) null else binaryPrecedence(value.operator),
        else => null,
    };
}

fn literalStartsWithMinus(value: ir.Literal) bool {
    return switch (value) {
        .integer => |item| item.len != 0 and item[0] == '-',
        .number => |item| std.math.signbit(item),
        else => false,
    };
}

fn binaryPrecedence(operator: ir.BinaryOperator) Precedence {
    return switch (operator) {
        .logical_or => .logical_or,
        .logical_and => .logical_and,
        .equal, .not_equal, .less, .less_equal, .greater, .greater_equal => .comparison,
        .concat => .concat,
        .add, .subtract => .additive,
        .multiply, .divide, .floor_divide, .modulo => .multiplicative,
        .power => .power,
        .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => unreachable,
    };
}

fn binaryAssociativity(operator: ir.BinaryOperator) Associativity {
    return switch (operator) {
        .concat, .power => .right,
        else => .left,
    };
}

fn binaryOperator(operator: ir.BinaryOperator) []const u8 {
    return switch (operator) {
        .add => "+",
        .subtract => "-",
        .multiply => "*",
        .divide => "/",
        .floor_divide => "//",
        .modulo => "%",
        .power => "^",
        .concat => "..",
        .equal => "==",
        .not_equal => "~=",
        .less => "<",
        .less_equal => "<=",
        .greater => ">",
        .greater_equal => ">=",
        .logical_and => "and",
        .logical_or => "or",
        .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => unreachable,
    };
}

pub fn compoundOperator(operator: ir.BinaryOperator) ?[]const u8 {
    return switch (operator) {
        .add => "+=",
        .subtract => "-=",
        .multiply => "*=",
        .divide => "/=",
        .floor_divide => "//=",
        .modulo => "%=",
        .power => "^=",
        .concat => "..=",
        else => null,
    };
}

pub fn literal(output: *std.ArrayList(u8), allocator: std.mem.Allocator, value: ir.Literal) !void {
    switch (value) {
        .nil_value => try output.appendSlice(allocator, "nil"),
        .boolean => |item| try output.appendSlice(allocator, if (item) "true" else "false"),
        .integer => |item| try output.appendSlice(allocator, item),
        .number => |item| try output.print(allocator, "{d}", .{item}),
        .special_number => |item| try output.appendSlice(allocator, switch (item) {
            .nan => "(0 / 0)",
            .positive_infinity => "(1 / 0)",
            .negative_infinity => "(-1 / 0)",
        }),
        .string => |item| try quoted(output, allocator, item),
    }
}

fn quoted(output: *std.ArrayList(u8), allocator: std.mem.Allocator, text: []const u8) !void {
    try output.append(allocator, '"');
    for (text) |byte| switch (byte) {
        '"' => try output.appendSlice(allocator, "\\\""),
        '\\' => try output.appendSlice(allocator, "\\\\"),
        '\n' => try output.appendSlice(allocator, "\\n"),
        '\r' => try output.appendSlice(allocator, "\\r"),
        '\t' => try output.appendSlice(allocator, "\\t"),
        else => if (byte >= 0x20 and byte < 0x7f)
            try output.append(allocator, byte)
        else
            try output.print(allocator, "\\x{x:0>2}", .{byte}),
    };
    try output.append(allocator, '"');
}

pub fn functionName(output: *std.ArrayList(u8), allocator: std.mem.Allocator, names: *const name_plan.Plan, function_id: ir.FunctionId) RenderError!void {
    try output.appendSlice(allocator, names.function(function_id) orelse return error.UnsupportedOperation);
}

pub fn valueName(output: *std.ArrayList(u8), allocator: std.mem.Allocator, names: *const name_plan.Plan, value_id: ir.ValueId) RenderError!void {
    try output.appendSlice(allocator, names.value(value_id) orelse return error.UnsupportedOperation);
}

pub fn valueUseName(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, value_id: ir.ValueId) RenderError!void {
    try valueUseContext(output, allocator, program, plan, value_id, .grouped, .preserve_adjustment);
}

pub fn valueUseRoot(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, value_id: ir.ValueId) RenderError!void {
    try valueUseContext(output, allocator, program, plan, value_id, .root, .preserve_adjustment);
}

pub fn valueUseScalar(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, value_id: ir.ValueId) RenderError!void {
    try valueUseContext(output, allocator, program, plan, value_id, .root, .implicit_single);
}

pub fn valueUseGroupedScalar(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, value_id: ir.ValueId) RenderError!void {
    try valueUseContext(output, allocator, program, plan, value_id, .grouped, .implicit_single);
}

fn valueUseContext(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, value_id: ir.ValueId, context: ExpressionContext, result_context: ResultContext) RenderError!void {
    const lexical_value = place_render.resolveValue(value_id, plan.place_aliases) orelse return error.UnsupportedOperation;
    const resolved = plan.dead.resolveValue(lexical_value);
    if (resolved.index() >= program.values.len) return error.UnsupportedOperation;
    if (plan.value_override) |value_override| {
        if (value_override.contains(resolved)) {
            const wrapped = context != .root;
            if (wrapped) try output.append(allocator, '(');
            try value_override.emit(output, allocator, program, plan, resolved);
            if (wrapped) try output.append(allocator, ')');
            return;
        }
    }
    const defining_instruction = switch (program.values[resolved.index()].origin) {
        .instruction_result => |origin| if (origin.index == 0) origin.instruction else null,
        else => null,
    };
    if (defining_instruction) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return error.UnsupportedOperation;
        const instruction = program.instructions[instruction_id.index()];
        if (plan.fused_values.contains(instruction_id)) {
            if (plan.packs.role(instruction_id) == .ordinary and operationSupportsContext(instruction.operation)) {
                try expressionWithContext(output, allocator, program, plan, instruction.operation, context, result_context);
                return;
            }
            try fusedInstructionExpression(output, allocator, program, plan, instruction, result_context);
            return;
        }
        if (plan.place_reads.contains(instruction_id)) {
            const place_id = switch (instruction.operation) {
                .place_read => |value| value,
                else => return error.UnsupportedOperation,
            };
            try place_render.emitRead(output, allocator, plan.names, program, place_id, plan.place_aliases);
            return;
        }
        if (plan.dead.isInlined(instruction_id)) {
            try expressionWithContext(output, allocator, program, plan, instruction.operation, context, result_context);
            return;
        }
    }
    try valueName(output, allocator, plan.names, resolved);
}

fn operationSupportsContext(operation: ir.Operation) bool {
    return switch (operation) {
        .copy, .unary, .binary => true,
        else => false,
    };
}

fn valueUseStartsWithMinus(program: *const ir.Program, plan: ValuePlan, value_id: ir.ValueId, remaining: usize) bool {
    if (remaining == 0) return true;
    const lexical_value = place_render.resolveValue(value_id, plan.place_aliases) orelse return true;
    const resolved = plan.dead.resolveValue(lexical_value);
    if (resolved.index() >= program.values.len) return true;
    const instruction_id = switch (program.values[resolved.index()].origin) {
        .instruction_result => |origin| if (origin.index == 0) origin.instruction else return false,
        else => return false,
    };
    if (instruction_id.index() >= program.instructions.len) return true;
    if (plan.place_reads.contains(instruction_id)) return false;
    const instruction = program.instructions[instruction_id.index()];
    if (plan.fused_values.contains(instruction_id)) {
        if (plan.packs.role(instruction_id) != .ordinary or !operationSupportsContext(instruction.operation)) return false;
        return operationStartsWithMinus(program, plan, instruction.operation, remaining - 1);
    }
    if (!plan.dead.isInlined(instruction_id)) return false;
    return operationStartsWithMinus(program, plan, instruction.operation, remaining - 1);
}

fn operationStartsWithMinus(program: *const ir.Program, plan: ValuePlan, operation: ir.Operation, remaining: usize) bool {
    return switch (operation) {
        .constant => |value| literalStartsWithMinus(value),
        .copy => |value| valueUseStartsWithMinus(program, plan, value, remaining),
        .unary => |value| value.operator == .negate,
        else => false,
    };
}

pub fn valueUsePostfix(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, value_id: ir.ValueId) RenderError!void {
    const lexical_value = place_render.resolveValue(value_id, plan.place_aliases) orelse return error.UnsupportedOperation;
    const resolved = plan.dead.resolveValue(lexical_value);
    if (resolved.index() >= program.values.len) return error.UnsupportedOperation;
    if (plan.value_override) |value_override| {
        if (value_override.contains(resolved)) {
            try output.append(allocator, '(');
            try value_override.emit(output, allocator, program, plan, resolved);
            try output.append(allocator, ')');
            return;
        }
    }
    const defining_instruction = switch (program.values[resolved.index()].origin) {
        .instruction_result => |origin| if (origin.index == 0) origin.instruction else null,
        else => null,
    };
    if (defining_instruction) |instruction_id| {
        if (plan.fused_values.contains(instruction_id)) {
            const instruction = program.instructions[instruction_id.index()];
            const needs_parentheses = instructionExpressionNeedsPostfixParentheses(instruction, plan.packs.role(instruction_id));
            if (needs_parentheses) try output.append(allocator, '(');
            try fusedInstructionExpression(output, allocator, program, plan, instruction, .preserve_adjustment);
            if (needs_parentheses) try output.append(allocator, ')');
            return;
        }
        if (plan.place_reads.contains(instruction_id)) {
            const place_id = switch (program.instructions[instruction_id.index()].operation) {
                .place_read => |value| value,
                else => return error.UnsupportedOperation,
            };
            try place_render.emitRead(output, allocator, plan.names, program, place_id, plan.place_aliases);
            return;
        }
        if (plan.dead.isInlined(instruction_id)) {
            const instruction = program.instructions[instruction_id.index()];
            const needs_parentheses = instructionExpressionNeedsPostfixParentheses(instruction, plan.packs.role(instruction_id));
            if (needs_parentheses) try output.append(allocator, '(');
            try expression(output, allocator, program, plan, instruction.operation);
            if (needs_parentheses) try output.append(allocator, ')');
            return;
        }
    }
    try valueName(output, allocator, plan.names, resolved);
}

fn valueUsePostfixStartsWithParenthesis(program: *const ir.Program, plan: ValuePlan, value_id: ir.ValueId, remaining: usize) bool {
    if (remaining == 0) return true;
    const lexical_value = place_render.resolveValue(value_id, plan.place_aliases) orelse return true;
    const resolved = plan.dead.resolveValue(lexical_value);
    if (resolved.index() >= program.values.len) return false;
    if (plan.value_override) |value_override| {
        if (value_override.contains(resolved)) return true;
    }
    const defining_instruction = switch (program.values[resolved.index()].origin) {
        .instruction_result => |origin| if (origin.index == 0) origin.instruction else return false,
        else => return false,
    };
    if (defining_instruction.index() >= program.instructions.len) return false;
    if (plan.place_reads.contains(defining_instruction)) return false;
    const instruction = program.instructions[defining_instruction.index()];
    const role = plan.packs.role(defining_instruction);
    if (plan.fused_values.contains(defining_instruction)) {
        if (role == .fused_adjustment) return true;
        return switch (instruction.operation) {
            .call, .namecall, .protected_call, .coroutine_create, .coroutine_resume, .coroutine_yield => true,
            else => instructionExpressionStartsWithParenthesis(program, plan, instruction, role, remaining - 1),
        };
    }
    if (!plan.dead.isInlined(defining_instruction)) return false;
    return instructionExpressionStartsWithParenthesis(program, plan, instruction, role, remaining - 1);
}

fn instructionExpressionStartsWithParenthesis(
    program: *const ir.Program,
    plan: ValuePlan,
    instruction: ir.Instruction,
    role: pack_plan.InstructionRole,
    remaining: usize,
) bool {
    if (instructionExpressionNeedsPostfixParentheses(instruction, role)) return true;
    return switch (instruction.operation) {
        .unary => |unary_value| unary_value.operator != .bit_not,
        .binary => |binary_value| luau_runtime.bit32Capability(binary_value.operator) == null,
        .environment_get => |environment| switch (environment.target) {
            .ambient => false,
            .value => |target| environment.mode == .semantic and valueUsePostfixStartsWithParenthesis(program, plan, target, remaining),
        },
        .table_get => |table| table.mode == .semantic and valueUsePostfixStartsWithParenthesis(program, plan, table.table, remaining),
        .string_interpolate => true,
        else => false,
    };
}

fn fusedInstructionExpression(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    instruction: ir.Instruction,
    result_context: ResultContext,
) RenderError!void {
    switch (plan.packs.role(instruction.id)) {
        .fused_adjustment => |producer_id| {
            if (producer_id.index() >= program.instructions.len) return error.UnsupportedOperation;
            if (result_context == .preserve_adjustment) try output.append(allocator, '(');
            try plannedInvocation(output, allocator, program, plan, plan.packs, program.instructions[producer_id.index()]);
            if (result_context == .preserve_adjustment) try output.append(allocator, ')');
            return;
        },
        .ordinary => {},
        else => return error.UnsupportedOperation,
    }
    switch (instruction.operation) {
        .call,
        .namecall,
        .protected_call,
        .coroutine_create,
        .coroutine_resume,
        .coroutine_yield,
        => {
            if (result_context == .preserve_adjustment) try output.append(allocator, '(');
            try plannedInvocation(output, allocator, program, plan, plan.packs, instruction);
            if (result_context == .preserve_adjustment) try output.append(allocator, ')');
        },
        .make_table_literal => |constructor| try plannedTableConstructor(output, allocator, program, plan, instruction.id, constructor),
        else => try expression(output, allocator, program, plan, instruction.operation),
    }
}

pub fn plannedTableConstructor(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    consumer: ir.InstructionId,
    constructor: ir.TableConstructor,
) RenderError!void {
    try output.append(allocator, '{');
    var wrote_item = false;
    for (constructor.fields, 0..) |field, field_index| {
        if (wrote_item) try output.appendSlice(allocator, ", ") else try output.append(allocator, ' ');
        switch (field) {
            .list => |value_id| if (field_index + 1 < constructor.fields.len or constructor.tail_pack != null)
                try valueUseScalar(output, allocator, program, plan, value_id)
            else
                try valueUseRoot(output, allocator, program, plan, value_id),
            .keyed => |keyed| {
                try semanticConstructorKey(output, allocator, program, plan, keyed.key);
                try output.appendSlice(allocator, " = ");
                try valueUseScalar(output, allocator, program, plan, keyed.value);
            },
        }
        wrote_item = true;
    }
    if (constructor.tail_pack) |pack_id| {
        if (wrote_item) try output.appendSlice(allocator, ", ") else try output.append(allocator, ' ');
        try plannedPackExpression(output, allocator, program, plan, consumer, pack_id);
        wrote_item = true;
    }
    if (wrote_item) try output.append(allocator, ' ');
    try output.append(allocator, '}');
}

fn plannedPackExpression(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    consumer: ir.InstructionId,
    pack_id: ir.ValuePackId,
) RenderError!void {
    if (pack_id.index() >= program.value_packs.len) return error.UnsupportedOperation;
    switch (program.value_packs[pack_id.index()].origin) {
        .varargs => try directVarargPackExpression(output, allocator, program, plan, pack_id),
        .instruction_result => |producer_id| {
            if (producer_id.index() >= program.instructions.len) return error.UnsupportedOperation;
            const producer = program.instructions[producer_id.index()];
            switch (producer.operation) {
                .pack_values => {
                    if (!plan.packs.packValuesServesInstruction(producer_id, consumer)) return error.UnsupportedOperation;
                    try plannedPackValues(output, allocator, program, plan, producer);
                },
                else => {
                    if (plan.packs.storedPackServesInstruction(producer_id, consumer)) {
                        try storedPackExpansion(output, allocator, plan, pack_id);
                        return;
                    }
                    const target = switch (plan.packs.role(producer_id)) {
                        .fused_invocation_producer => |instruction_id| instruction_id,
                        else => return error.UnsupportedOperation,
                    };
                    if (target != consumer) return error.UnsupportedOperation;
                    try plannedInvocation(output, allocator, program, plan, plan.packs, producer);
                },
            }
        },
    }
}

pub fn storedPackExpansion(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    plan: ValuePlan,
    pack_id: ir.ValuePackId,
) RenderError!void {
    const name = plan.names.valuePack(pack_id) orelse return error.UnsupportedOperation;
    try runtimeCallStart(output, allocator, plan, .table_unpack);
    try globalIdentifier(output, allocator, name);
    try output.appendSlice(allocator, ", 1, ");
    try runtimeCallStart(output, allocator, plan, .rawget);
    try globalIdentifier(output, allocator, name);
    try output.appendSlice(allocator, ", 0))");
}

fn instructionExpressionNeedsPostfixParentheses(instruction: ir.Instruction, role: pack_plan.InstructionRole) bool {
    if (role == .fused_adjustment) return false;
    return switch (instruction.operation) {
        .constant, .make_table, .make_table_literal, .copy => true,
        .unary,
        .binary,
        .call,
        .namecall,
        .protected_call,
        .coroutine_create,
        .coroutine_resume,
        .coroutine_yield,
        .environment_get,
        .table_get,
        .string_interpolate,
        .function_ref,
        => false,
        else => true,
    };
}

pub fn placeName(output: *std.ArrayList(u8), allocator: std.mem.Allocator, names: *const name_plan.Plan, place_id: ir.PlaceId) !void {
    try place_render.emitDirectName(output, allocator, names, place_id);
}

pub fn valueList(output: *std.ArrayList(u8), allocator: std.mem.Allocator, names: *const name_plan.Plan, values: []const ir.ValueId) !void {
    for (values, 0..) |value_id, index| {
        if (index != 0) try output.appendSlice(allocator, ", ");
        try valueName(output, allocator, names, value_id);
    }
}

pub fn valueUseList(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, plan: ValuePlan, values: []const ir.ValueId, tail_follows: bool) !void {
    for (values, 0..) |value_id, index| {
        if (index != 0) try output.appendSlice(allocator, ", ");
        if (index + 1 < values.len or tail_follows)
            try valueUseScalar(output, allocator, program, plan, value_id)
        else
            try valueUseRoot(output, allocator, program, plan, value_id);
    }
}

pub fn plannedPackValues(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    plan: ValuePlan,
    producer: ir.Instruction,
) RenderError!void {
    const values = switch (producer.operation) {
        .pack_values => |items| items,
        else => return error.UnsupportedOperation,
    };
    if (values.len == 0) return error.UnsupportedOperation;
    try valueUseList(output, allocator, program, plan, values, false);
}

test "Luau string literal emission preserves arbitrary bytes" {
    var output: std.ArrayList(u8) = .empty;
    defer output.deinit(std.testing.allocator);
    try literal(&output, std.testing.allocator, .{ .string = "\xff\x00\xc3\xa9" });
    try std.testing.expectEqualStrings("\"\\xff\\x00\\xc3\\xa9\"", output.items);
}

test "Luau precedence preserves parser grouping by operand side" {
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const add: ir.Operation = .{ .binary = .{ .operator = .add, .left = left, .right = right } };
    const multiply: ir.Operation = .{ .binary = .{ .operator = .multiply, .left = left, .right = right } };
    const comparison: ir.Operation = .{ .binary = .{ .operator = .less, .left = left, .right = right } };
    const logical_and: ir.Operation = .{ .binary = .{ .operator = .logical_and, .left = left, .right = right } };
    const concat: ir.Operation = .{ .binary = .{ .operator = .concat, .left = left, .right = right } };
    const power: ir.Operation = .{ .binary = .{ .operator = .power, .left = left, .right = right } };
    const negate: ir.Operation = .{ .unary = .{ .operator = .negate, .operand = left } };
    const negative_literal: ir.Operation = .{ .constant = .{ .integer = "-1" } };

    try std.testing.expect(!expressionNeedsParentheses(add, .root));
    try std.testing.expect(expressionNeedsParentheses(add, .grouped));
    try std.testing.expect(expressionNeedsParentheses(add, .unary_operand));
    try std.testing.expect(!expressionNeedsParentheses(power, .unary_operand));

    try std.testing.expect(expressionNeedsParentheses(add, .{ .binary_operand = .{ .operator = .multiply, .side = .left } }));
    try std.testing.expect(!expressionNeedsParentheses(multiply, .{ .binary_operand = .{ .operator = .add, .side = .right } }));
    try std.testing.expect(!expressionNeedsParentheses(comparison, .{ .binary_operand = .{ .operator = .logical_and, .side = .left } }));
    try std.testing.expect(expressionNeedsParentheses(logical_and, .{ .binary_operand = .{ .operator = .less, .side = .right } }));

    try std.testing.expect(!expressionNeedsParentheses(add, .{ .binary_operand = .{ .operator = .subtract, .side = .left } }));
    try std.testing.expect(expressionNeedsParentheses(add, .{ .binary_operand = .{ .operator = .subtract, .side = .right } }));
    try std.testing.expect(expressionNeedsParentheses(concat, .{ .binary_operand = .{ .operator = .concat, .side = .left } }));
    try std.testing.expect(!expressionNeedsParentheses(concat, .{ .binary_operand = .{ .operator = .concat, .side = .right } }));
    try std.testing.expect(expressionNeedsParentheses(power, .{ .binary_operand = .{ .operator = .power, .side = .left } }));
    try std.testing.expect(!expressionNeedsParentheses(power, .{ .binary_operand = .{ .operator = .power, .side = .right } }));
    try std.testing.expect(expressionNeedsParentheses(negate, .{ .binary_operand = .{ .operator = .power, .side = .left } }));
    try std.testing.expect(expressionNeedsParentheses(negative_literal, .{ .binary_operand = .{ .operator = .power, .side = .left } }));
    try std.testing.expect(!expressionNeedsParentheses(negative_literal, .{ .binary_operand = .{ .operator = .multiply, .side = .right } }));
}
