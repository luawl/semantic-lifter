const std = @import("std");
const ir = @import("ir.zig");
const emission_planning = @import("emit_luau_plan.zig");
const render = @import("emit_luau_expr.zig");

pub fn instruction(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    source: ir.Instruction,
    indent: []const u8,
    declare_results: bool,
    values: render.ValuePlan,
) !void {
    if (source.results.len == 0 and render.statementNeedsSeparator(program, values, source.operation)) {
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "do\n");
        const statement_indent = try allocDeeperIndent(allocator, indent);
        defer allocator.free(statement_indent);
        try output.appendSlice(allocator, statement_indent);
        try render.plannedInvocation(output, allocator, program, values, &emission_plan.packs, source);
        try output.append(allocator, '\n');
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "end\n");
        return;
    }
    try output.appendSlice(allocator, indent);
    if (source.results.len != 0) {
        try emitResultNames(output, allocator, emission_plan, source.results, declare_results);
        try output.appendSlice(allocator, " = ");
    }
    try render.plannedInvocation(output, allocator, program, values, &emission_plan.packs, source);
    try output.append(allocator, '\n');
}

pub fn fusedAdjustment(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    adjustment: ir.Instruction,
    producer: ir.Instruction,
    indent: []const u8,
    declare_results: bool,
    values: render.ValuePlan,
) !void {
    return adjustedInvocation(output, allocator, program, emission_plan, adjustment, producer, indent, declare_results, values);
}

pub fn materializedAdjustment(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    adjustment: ir.Instruction,
    producer: ir.Instruction,
    indent: []const u8,
    declare_results: bool,
    values: render.ValuePlan,
) !void {
    return adjustedInvocation(output, allocator, program, emission_plan, adjustment, producer, indent, declare_results, values);
}

pub fn materializedAdjustmentCopy(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    emission_plan: *const emission_planning.Plan,
    adjustment: ir.Instruction,
    primary: ir.Instruction,
    indent: []const u8,
    declare_results: bool,
) !void {
    if (adjustment.results.len == 0) return;
    if (primary.results.len < adjustment.results.len) return error.UnsupportedOperation;
    try output.appendSlice(allocator, indent);
    try emitResultNames(output, allocator, emission_plan, adjustment.results, declare_results);
    try output.appendSlice(allocator, " = ");
    try render.valueList(output, allocator, &emission_plan.names, primary.results[0..adjustment.results.len]);
    try output.append(allocator, '\n');
}

pub fn storedPack(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    producer: ir.Instruction,
    indent: []const u8,
    values: render.ValuePlan,
) !void {
    const pack_id = producer.pack_result orelse return error.UnsupportedOperation;
    if (pack_id.index() >= program.value_packs.len) return error.UnsupportedOperation;
    const statement_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(statement_indent);
    const body_indent = try allocDeeperIndent(allocator, statement_indent);
    defer allocator.free(body_indent);

    try output.appendSlice(allocator, indent);
    try packName(output, allocator, emission_plan, pack_id);
    try output.appendSlice(allocator, " = (function(...)\n");

    try output.appendSlice(allocator, statement_indent);
    try output.appendSlice(allocator, "local __lifter_stored_values_");
    try output.print(allocator, "{d}", .{producer.id.index()});
    try output.appendSlice(allocator, " = {}\n");
    try output.appendSlice(allocator, statement_indent);
    try output.appendSlice(allocator, "local __lifter_stored_count_");
    try output.print(allocator, "{d}", .{producer.id.index()});
    try output.appendSlice(allocator, " = ");
    try render.runtimeCallStart(output, allocator, values, .select);
    try output.appendSlice(allocator, "\"#\", ...)\n");

    try output.appendSlice(allocator, statement_indent);
    try render.runtimeCallStart(output, allocator, values, .rawset);
    try output.appendSlice(allocator, "__lifter_stored_values_");
    try output.print(allocator, "{d}", .{producer.id.index()});
    try output.appendSlice(allocator, ", 0, __lifter_stored_count_");
    try output.print(allocator, "{d})\n", .{producer.id.index()});

    try output.appendSlice(allocator, statement_indent);
    try output.appendSlice(allocator, "for __lifter_stored_index_");
    try output.print(allocator, "{d}", .{producer.id.index()});
    try output.appendSlice(allocator, " = 1, __lifter_stored_count_");
    try output.print(allocator, "{d} do\n", .{producer.id.index()});
    try output.appendSlice(allocator, body_indent);
    try render.runtimeCallStart(output, allocator, values, .rawset);
    try output.appendSlice(allocator, "__lifter_stored_values_");
    try output.print(allocator, "{d}", .{producer.id.index()});
    try output.appendSlice(allocator, ", __lifter_stored_index_");
    try output.print(allocator, "{d}, (", .{producer.id.index()});
    try render.runtimeCallStart(output, allocator, values, .select);
    try output.appendSlice(allocator, "__lifter_stored_index_");
    try output.print(allocator, "{d}, ...)))\n", .{producer.id.index()});
    try output.appendSlice(allocator, statement_indent);
    try output.appendSlice(allocator, "end\n");

    try output.appendSlice(allocator, statement_indent);
    try output.appendSlice(allocator, "return __lifter_stored_values_");
    try output.print(allocator, "{d}\n", .{producer.id.index()});
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end)(");
    try render.plannedInvocation(output, allocator, program, values, &emission_plan.packs, producer);
    try output.appendSlice(allocator, ")\n");
}

pub fn storedAdjustment(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    adjustment: ir.Instruction,
    producer: ir.Instruction,
    indent: []const u8,
    declare_results: bool,
    values: render.ValuePlan,
) !void {
    if (adjustment.results.len == 0) return;
    const pack_id = switch (adjustment.operation) {
        .adjust_pack => |value| value,
        else => return error.UnsupportedOperation,
    };
    if (producer.pack_result != pack_id or pack_id.index() >= program.value_packs.len) return error.UnsupportedOperation;
    try output.appendSlice(allocator, indent);
    try emitResultNames(output, allocator, emission_plan, adjustment.results, declare_results);
    try output.appendSlice(allocator, " = ");
    for (adjustment.results, 0..) |_, index| {
        if (index != 0) try output.appendSlice(allocator, ", ");
        try render.runtimeCallStart(output, allocator, values, .rawget);
        try packName(output, allocator, emission_plan, pack_id);
        try output.print(allocator, ", {d})", .{index + 1});
    }
    try output.append(allocator, '\n');
}

fn adjustedInvocation(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    adjustment: ir.Instruction,
    producer: ir.Instruction,
    indent: []const u8,
    declare_results: bool,
    values: render.ValuePlan,
) !void {
    if (adjustment.results.len == 0 and render.statementNeedsSeparator(program, values, producer.operation)) {
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "do\n");
        const statement_indent = try allocDeeperIndent(allocator, indent);
        defer allocator.free(statement_indent);
        try output.appendSlice(allocator, statement_indent);
        try render.plannedInvocation(output, allocator, program, values, &emission_plan.packs, producer);
        try output.append(allocator, '\n');
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "end\n");
        return;
    }
    try output.appendSlice(allocator, indent);
    if (adjustment.results.len != 0) {
        try emitResultNames(output, allocator, emission_plan, adjustment.results, declare_results);
        try output.appendSlice(allocator, " = ");
    }
    try render.plannedInvocation(output, allocator, program, values, &emission_plan.packs, producer);
    try output.append(allocator, '\n');
}

pub fn directVarargAdjustment(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    adjustment: ir.Instruction,
    indent: []const u8,
    declare_results: bool,
    values: render.ValuePlan,
) !void {
    if (adjustment.results.len == 0) return;
    try output.appendSlice(allocator, indent);
    try emitResultNames(output, allocator, emission_plan, adjustment.results, declare_results);
    try output.appendSlice(allocator, " = ");
    const pack_id = switch (adjustment.operation) {
        .adjust_pack => |value| value,
        else => return error.UnsupportedOperation,
    };
    try render.directVarargPackExpression(output, allocator, program, values, pack_id);
    try output.append(allocator, '\n');
}

pub fn packValuesAdjustment(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    adjustment: ir.Instruction,
    producer: ir.Instruction,
    indent: []const u8,
    declare_results: bool,
    values: render.ValuePlan,
) !void {
    if (adjustment.results.len == 0) return;
    try output.appendSlice(allocator, indent);
    try emitResultNames(output, allocator, emission_plan, adjustment.results, declare_results);
    try output.appendSlice(allocator, " = ");
    try render.plannedPackValues(output, allocator, program, values, producer);
    try output.append(allocator, '\n');
}

fn emitResultNames(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    emission_plan: *const emission_planning.Plan,
    results: []const ir.ValueId,
    declare_results: bool,
) !void {
    const any_storage = for (results) |result| {
        if (emission_plan.names.valueUsesStorage(result)) break true;
    } else false;
    if (declare_results and !any_storage) try output.appendSlice(allocator, "local ");
    try render.valueList(output, allocator, &emission_plan.names, results);
}

pub fn terminator(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    block: ir.Block,
    indent: []const u8,
    values: render.ValuePlan,
) !void {
    try output.appendSlice(allocator, indent);
    switch (emission_plan.packs.terminatorRole(block.id)) {
        .fused_invocation_return => |producer_id| {
            try output.appendSlice(allocator, "return ");
            if (block.terminator == .return_expanded) {
                const prefix = block.terminator.return_expanded.values;
                try render.valueUseList(output, allocator, program, values, prefix, true);
                if (prefix.len != 0) try output.appendSlice(allocator, ", ");
            }
            try render.plannedInvocation(output, allocator, program, values, &emission_plan.packs, program.instructions[producer_id.index()]);
        },
        .fused_pack_values_return => |producer_id| {
            if (producer_id.index() >= program.instructions.len) return error.UnsupportedOperation;
            const producer = program.instructions[producer_id.index()];
            const packed_values = switch (producer.operation) {
                .pack_values => |items| items,
                else => return error.UnsupportedOperation,
            };
            try output.appendSlice(allocator, "return");
            const prefix = switch (block.terminator) {
                .return_pack => &.{},
                .return_expanded => |expanded| expanded.values,
                else => return error.UnsupportedControlFlow,
            };
            if (prefix.len != 0 or packed_values.len != 0) try output.append(allocator, ' ');
            if (prefix.len != 0) {
                try render.valueUseList(output, allocator, program, values, prefix, true);
                if (packed_values.len != 0) try output.appendSlice(allocator, ", ");
            }
            if (packed_values.len != 0) try render.plannedPackValues(output, allocator, program, values, producer);
        },
        .stored_pack_return => |producer_id| {
            if (producer_id.index() >= program.instructions.len) return error.UnsupportedOperation;
            const producer = program.instructions[producer_id.index()];
            const pack_id = producer.pack_result orelse return error.UnsupportedOperation;
            const prefix = switch (block.terminator) {
                .return_pack => &.{},
                .return_expanded => |expanded| if (expanded.pack == pack_id) expanded.values else return error.UnsupportedControlFlow,
                else => return error.UnsupportedControlFlow,
            };
            try output.appendSlice(allocator, "return ");
            if (prefix.len != 0) {
                try render.valueUseList(output, allocator, program, values, prefix, true);
                try output.appendSlice(allocator, ", ");
            }
            try render.storedPackExpansion(output, allocator, values, pack_id);
        },
        .ordinary => switch (block.terminator) {
            .return_values => |returned| {
                try output.appendSlice(allocator, "return");
                if (returned.len != 0) try output.append(allocator, ' ');
                for (returned, 0..) |value, index| {
                    if (index != 0) try output.appendSlice(allocator, ", ");
                    if (index + 1 < returned.len)
                        try render.valueUseScalar(output, allocator, program, values, value)
                    else
                        try render.valueUseRoot(output, allocator, program, values, value);
                }
            },
            .return_pack => |pack_id| {
                try output.appendSlice(allocator, "return ");
                try render.directVarargPackExpression(output, allocator, program, values, pack_id);
            },
            .return_expanded => |expanded| switch (program.value_packs[expanded.pack.index()].origin) {
                .varargs => {
                    try output.appendSlice(allocator, "return ");
                    try render.valueUseList(output, allocator, program, values, expanded.values, true);
                    if (expanded.values.len != 0) try output.appendSlice(allocator, ", ");
                    try render.directVarargPackExpression(output, allocator, program, values, expanded.pack);
                },
                else => return error.UnsupportedControlFlow,
            },
            .throw_error => |throw_error| {
                try render.runtimeCallStart(output, allocator, values, .error_builtin);
                try render.valueUseScalar(output, allocator, program, values, throw_error.value);
                try output.appendSlice(allocator, ", ");
                if (throw_error.dynamic_level) |level| {
                    try render.valueUseScalar(output, allocator, program, values, level);
                    try output.append(allocator, ')');
                } else {
                    try output.print(allocator, "{d})", .{throw_error.level});
                }
            },
            .unreachable_block => {
                try render.runtimeCallStart(output, allocator, values, .error_builtin);
                try output.appendSlice(allocator, "\"unreachable\")");
            },
            else => return error.UnsupportedControlFlow,
        },
    }
    try output.append(allocator, '\n');
}

fn allocDeeperIndent(allocator: std.mem.Allocator, indent: []const u8) ![]u8 {
    const result = try allocator.alloc(u8, indent.len + 2);
    @memcpy(result[0..indent.len], indent);
    @memset(result[indent.len..], ' ');
    return result;
}

fn packName(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    emission_plan: *const emission_planning.Plan,
    pack_id: ir.ValuePackId,
) !void {
    const name = emission_plan.names.valuePack(pack_id) orelse return error.UnsupportedOperation;
    try render.globalIdentifier(output, allocator, name);
}
