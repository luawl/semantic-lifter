const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const diagnostics = @import("diagnostics.zig");
const luau_runtime = @import("luau_runtime.zig");
const pack_plan = @import("pack_plan.zig");
const readable_scope = @import("readable_scope.zig");
const type_validation = @import("validate_types.zig");

pub fn validate(
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    profile: ir.AdmissionProfile,
    scope: ?*const readable_scope.Scope,
) !void {
    const definition_counts = try allocator.alloc(u32, program.value_packs.len);
    defer allocator.free(definition_counts);
    @memset(definition_counts, 0);
    var emission_plan = try pack_plan.Plan.init(allocator, program);
    defer emission_plan.deinit();

    for (program.value_packs, 0..) |pack, pack_index| {
        if (pack.id.index() != pack_index) try report.add(.noncanonical_value_pack_id, pack_index);
        if (!validId(pack.function, program.functions.len)) try report.add(.invalid_value_pack_function, pack_index);
        for (pack.evidence) |evidence_id| {
            if (!validId(evidence_id, program.evidence.len)) try report.add(.invalid_evidence_reference, pack_index);
        }
        if (profile == .readable_luau and (scope == null or scope.?.valuePack(pack.id)) and pack.evidence.len == 0) {
            try report.add(.missing_emission_evidence, pack_index);
        }

        switch (pack.origin) {
            .varargs => |function_id| {
                if (!validId(function_id, program.functions.len) or function_id != pack.function) {
                    try report.add(.invalid_value_pack_origin, pack_index);
                }
            },
            .instruction_result => |instruction_id| {
                if (!validId(instruction_id, program.instructions.len)) {
                    try report.add(.invalid_value_pack_origin, pack_index);
                } else {
                    const instruction = program.instructions[instruction_id.index()];
                    if (!validId(instruction.block, program.blocks.len) or program.blocks[instruction.block.index()].function != pack.function) {
                        try report.add(.invalid_value_pack_origin, pack_index);
                    }
                }
            },
        }
    }

    for (program.functions, 0..) |function, function_index| {
        if (function.vararg_pack) |pack_id| {
            if (!function.is_variadic or !validId(pack_id, program.value_packs.len)) {
                try report.add(.invalid_function_vararg_pack, function_index);
                continue;
            }
            incrementDefinition(definition_counts, pack_id);
            const pack = program.value_packs[pack_id.index()];
            const origin_matches = switch (pack.origin) {
                .varargs => |owner| owner == function.id,
                else => false,
            };
            if (pack.function != function.id or !origin_matches) {
                try report.add(.function_vararg_pack_origin_mismatch, pack_id.index());
            }
            if (!isOpenUnknown(pack.shape)) try report.add(.invalid_value_pack_shape, pack_id.index());
        }
    }

    for (program.instructions, 0..) |instruction, instruction_index| {
        const readable = profile == .readable_luau and (scope == null or scope.?.instruction(instruction.id));
        const function_id = instructionFunction(program, instruction) orelse continue;
        if (instruction.pack_result) |pack_id| {
            if (!validId(pack_id, program.value_packs.len)) {
                try report.add(.invalid_instruction_pack_result, instruction_index);
            } else {
                incrementDefinition(definition_counts, pack_id);
                const pack = program.value_packs[pack_id.index()];
                const origin_matches = switch (pack.origin) {
                    .instruction_result => |producer| producer == instruction.id,
                    else => false,
                };
                if (pack.function != function_id or !origin_matches) {
                    try report.add(.instruction_pack_result_origin_mismatch, pack_id.index());
                }
            }
        }

        if (invocationView(instruction.operation)) |invocation| {
            if (invocation.argument_pack) |pack_id| {
                try validateOperand(report, program, pack_id, function_id, instruction_index);
                if (readable and !isDirectVarargPack(program, function_id, pack_id) and
                    !isRenderableInvocationArgument(program, &emission_plan, instruction.id, pack_id))
                {
                    try report.add(.unsupported_readable_pack_operation, instruction_index);
                }
            }
            switch (invocation.result_arity) {
                .fixed => |count| {
                    if (instruction.results.len != count) try report.add(.invalid_result_arity, instruction_index);
                    if (instruction.pack_result != null) try report.add(.invalid_instruction_pack_result, instruction_index);
                    if (readable and count > luau_runtime.max_local_registers) {
                        try report.add(.unsupported_readable_result_arity, instruction_index);
                    }
                },
                .variadic => {
                    if (instruction.results.len != 0) try report.add(.invalid_result_arity, instruction_index);
                    if (instruction.pack_result == null) try report.add(.invalid_instruction_pack_result, instruction_index);
                    if (instruction.pack_result) |pack_id| {
                        if (validId(pack_id, program.value_packs.len)) {
                            const shape = program.value_packs[pack_id.index()].shape;
                            const shape_valid = switch (invocation.kind) {
                                .ordinary => true,
                                .status_prefix => hasBooleanOpenPrefix(shape),
                            };
                            if (!shape_valid) try report.add(.invalid_value_pack_shape, pack_id.index());
                        }
                    }
                    if (readable and !isFusedProducer(&emission_plan, instruction.id)) {
                        try report.add(.variadic_result_arity, instruction_index);
                    }
                },
            }
        } else switch (instruction.operation) {
            .pack_values => |values| {
                if (values.len == 0) try report.add(.empty_pack_values, instruction_index);
                const pack_id = instruction.pack_result orelse {
                    try report.add(.invalid_instruction_pack_result, instruction_index);
                    continue;
                };
                if (validId(pack_id, program.value_packs.len)) {
                    const pack = program.value_packs[pack_id.index()];
                    if (!packValuesShapeMatches(program, values, pack.shape)) {
                        try report.add(.invalid_value_pack_shape, pack_id.index());
                    }
                    if (!std.mem.eql(ir.EvidenceId, instruction.evidence, pack.evidence)) {
                        try report.add(.pack_values_evidence_mismatch, pack_id.index());
                    }
                }
                if (!pack_plan.isExactPure(instruction.effects)) try report.add(.invalid_pack_values_effects, instruction_index);
                if (readable and !isFusedPackValuesProducer(&emission_plan, instruction.id)) {
                    try report.add(.unsupported_readable_pack_operation, instruction_index);
                }
            },
            .adjust_pack => |pack_id| {
                if (instruction.pack_result != null) try report.add(.invalid_instruction_pack_result, instruction_index);
                try validateOperand(report, program, pack_id, function_id, instruction_index);
                if (validId(pack_id, program.value_packs.len)) try validateAdjustmentTypes(report, program, instruction, program.value_packs[pack_id.index()].shape);
                if (!pack_plan.isExactPure(instruction.effects)) try report.add(.invalid_pack_adjustment_effects, instruction_index);
                if (readable and instruction.results.len > luau_runtime.max_local_registers) {
                    try report.add(.unsupported_readable_result_arity, instruction_index);
                }
                if (readable and !isFusedAdjustment(&emission_plan, instruction.id)) {
                    try report.add(.unsupported_readable_pack_operation, instruction_index);
                }
            },
            .make_table_literal => |constructor| {
                if (instruction.pack_result != null) try report.add(.invalid_instruction_pack_result, instruction_index);
                if (constructor.tail_pack) |pack_id| {
                    try validateOperand(report, program, pack_id, function_id, instruction_index);
                    if (readable and !isRenderableTableTail(program, &emission_plan, instruction.id, pack_id)) {
                        try report.add(.unsupported_readable_pack_operation, instruction_index);
                    }
                }
            },
            .table_set_pack => |operation| {
                if (instruction.pack_result != null) try report.add(.invalid_instruction_pack_result, instruction_index);
                try validateOperand(report, program, operation.pack, function_id, instruction_index);
                if (readable and !isRenderableTableTail(program, &emission_plan, instruction.id, operation.pack)) {
                    try report.add(.unsupported_readable_pack_operation, instruction_index);
                }
            },
            else => if (instruction.pack_result != null) try report.add(.invalid_instruction_pack_result, instruction_index),
        }
    }

    for (program.blocks, 0..) |block, block_index| switch (block.terminator) {
        .return_pack => |pack_id| {
            try validateOperand(report, program, pack_id, block.function, block_index);
            if (profile == .readable_luau and (scope == null or scope.?.block(block.id)) and
                !isDirectVarargPack(program, block.function, pack_id) and
                !isFusedReturn(&emission_plan, block.id))
            {
                try report.add(.unsupported_readable_pack_operation, block_index);
            }
        },
        .return_expanded => |expanded| {
            try validateOperand(report, program, expanded.pack, block.function, block_index);
            if (profile == .readable_luau and (scope == null or scope.?.block(block.id)) and
                !isDirectVarargPack(program, block.function, expanded.pack) and
                !isFusedReturn(&emission_plan, block.id))
            {
                try report.add(.unsupported_readable_pack_operation, block_index);
            }
        },
        else => {},
    };

    for (definition_counts, 0..) |count, pack_index| {
        if (count == 0) try report.add(.missing_value_pack_definition, pack_index);
        if (count > 1) try report.add(.duplicate_value_pack_definition, pack_index);
    }
}

pub fn validateInstructionUse(
    report: *diagnostics.Report,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    instruction_positions: []const ?usize,
    instruction: ir.Instruction,
    position: usize,
) !void {
    if (invocationView(instruction.operation)) |invocation| {
        if (invocation.argument_pack) |pack_id| try validateUse(
            report,
            program,
            analysis,
            instruction_positions,
            program.blocks[instruction.block.index()],
            position,
            pack_id,
            instruction.id.index(),
        );
        return;
    }
    switch (instruction.operation) {
        .adjust_pack => |pack_id| try validateUse(
            report,
            program,
            analysis,
            instruction_positions,
            program.blocks[instruction.block.index()],
            position,
            pack_id,
            instruction.id.index(),
        ),
        .make_table_literal => |constructor| if (constructor.tail_pack) |pack_id| try validateUse(
            report,
            program,
            analysis,
            instruction_positions,
            program.blocks[instruction.block.index()],
            position,
            pack_id,
            instruction.id.index(),
        ),
        .table_set_pack => |operation| try validateUse(
            report,
            program,
            analysis,
            instruction_positions,
            program.blocks[instruction.block.index()],
            position,
            operation.pack,
            instruction.id.index(),
        ),
        else => {},
    }
}

pub fn validateTerminatorUse(
    report: *diagnostics.Report,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    instruction_positions: []const ?usize,
    block: ir.Block,
) !void {
    switch (block.terminator) {
        .return_pack => |pack_id| try validateUse(
            report,
            program,
            analysis,
            instruction_positions,
            block,
            block.instructions.len,
            pack_id,
            block.id.index(),
        ),
        .return_expanded => |expanded| try validateUse(
            report,
            program,
            analysis,
            instruction_positions,
            block,
            block.instructions.len,
            expanded.pack,
            block.id.index(),
        ),
        else => {},
    }
}

fn validateUse(
    report: *diagnostics.Report,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    instruction_positions: []const ?usize,
    use_block: ir.Block,
    use_position: usize,
    pack_id: ir.ValuePackId,
    entity_index: usize,
) !void {
    if (!validId(pack_id, program.value_packs.len)) return;
    const pack = program.value_packs[pack_id.index()];
    if (pack.function != use_block.function) return;

    switch (pack.origin) {
        .varargs => {},
        .instruction_result => |instruction_id| {
            if (!validId(instruction_id, program.instructions.len)) return;
            const definition = program.instructions[instruction_id.index()];
            if (!validId(definition.block, program.blocks.len)) return;
            if (definition.block == use_block.id) {
                const definition_position = instruction_positions[instruction_id.index()] orelse return;
                if (definition_position >= use_position) try report.add(.value_pack_used_before_definition, entity_index);
            } else if (!analysis.dominates(definition.block, use_block.id)) {
                try report.add(.non_dominating_value_pack_use, entity_index);
            }
        },
    }
}

fn isFusedProducer(plan: *const pack_plan.Plan, instruction_id: ir.InstructionId) bool {
    return switch (plan.role(instruction_id)) {
        .fused_invocation_producer, .materialized_invocation_producer, .stored_invocation_producer, .fused_return_producer => true,
        else => false,
    };
}

fn isFusedPackValuesProducer(plan: *const pack_plan.Plan, instruction_id: ir.InstructionId) bool {
    return switch (plan.role(instruction_id)) {
        .fused_pack_values_producer, .materialized_pack_values_producer, .fused_pack_values_return_producer => true,
        else => false,
    };
}

fn isFusedAdjustment(plan: *const pack_plan.Plan, instruction_id: ir.InstructionId) bool {
    return switch (plan.role(instruction_id)) {
        .fused_adjustment,
        .materialized_adjustment,
        .materialized_adjustment_copy,
        .stored_adjustment,
        .direct_vararg_adjustment,
        .fused_pack_values_adjustment,
        => true,
        else => false,
    };
}

fn isFusedReturn(plan: *const pack_plan.Plan, block_id: ir.BlockId) bool {
    return switch (plan.terminatorRole(block_id)) {
        .fused_invocation_return, .fused_pack_values_return, .stored_pack_return => true,
        else => false,
    };
}

fn isRenderableTableTail(
    program: *const ir.Program,
    plan: *const pack_plan.Plan,
    consumer: ir.InstructionId,
    pack_id: ir.ValuePackId,
) bool {
    if (pack_id.index() >= program.value_packs.len) return false;
    const pack = program.value_packs[pack_id.index()];
    switch (pack.origin) {
        .varargs => |function_id| return isDirectVarargPack(program, function_id, pack_id),
        .instruction_result => |producer| return switch (plan.role(producer)) {
            .fused_invocation_producer => |target| target == consumer,
            .stored_invocation_producer => plan.storedPackServesInstruction(producer, consumer),
            .fused_pack_values_producer, .materialized_pack_values_producer => plan.packValuesServesInstruction(producer, consumer),
            else => false,
        },
    }
}

fn isRenderableInvocationArgument(
    program: *const ir.Program,
    plan: *const pack_plan.Plan,
    consumer: ir.InstructionId,
    pack_id: ir.ValuePackId,
) bool {
    if (pack_id.index() >= program.value_packs.len) return false;
    return switch (program.value_packs[pack_id.index()].origin) {
        .varargs => false,
        .instruction_result => |producer| switch (plan.role(producer)) {
            .fused_invocation_producer => |target| target == consumer,
            .stored_invocation_producer => plan.storedPackServesInstruction(producer, consumer),
            .fused_pack_values_producer, .materialized_pack_values_producer => plan.packValuesServesInstruction(producer, consumer),
            else => false,
        },
    };
}

fn validateOperand(
    report: *diagnostics.Report,
    program: *const ir.Program,
    pack_id: ir.ValuePackId,
    function_id: ir.FunctionId,
    entity_index: usize,
) !void {
    if (!validId(pack_id, program.value_packs.len)) {
        try report.add(.invalid_value_pack_operand, entity_index);
        return;
    }
    if (program.value_packs[pack_id.index()].function != function_id) {
        try report.add(.cross_function_value_pack, entity_index);
    }
}

fn isDirectVarargPack(program: *const ir.Program, function_id: ir.FunctionId, pack_id: ir.ValuePackId) bool {
    if (!validId(function_id, program.functions.len) or !validId(pack_id, program.value_packs.len)) return false;
    const function = program.functions[function_id.index()];
    if (!function.is_variadic or function.vararg_pack != pack_id) return false;
    const pack = program.value_packs[pack_id.index()];
    return pack.function == function_id and switch (pack.origin) {
        .varargs => |owner| owner == function_id,
        else => false,
    };
}

fn validateAdjustmentTypes(report: *diagnostics.Report, program: *const ir.Program, instruction: ir.Instruction, shape: ir.PackShape) !void {
    for (instruction.results, 0..) |result_id, index| {
        if (!validId(result_id, program.values.len)) continue;
        const expected: ?ir.ValueType = if (index < shape.prefix.len)
            shape.prefix[index]
        else if (shape.tail == .closed)
            .{ .kind = .nil_value }
        else
            null;
        if (expected) |expected_type| {
            if (!type_validation.isAssignable(program.values[result_id.index()].type, expected_type)) {
                try report.add(.pack_adjustment_type_mismatch, instruction.id.index());
            }
        }
    }
}

fn packValuesShapeMatches(program: *const ir.Program, values: []const ir.ValueId, shape: ir.PackShape) bool {
    if (shape.tail != .closed or shape.prefix.len != values.len) return false;
    for (values, shape.prefix) |value_id, expected| {
        if (!validId(value_id, program.values.len) or !std.meta.eql(program.values[value_id.index()].type, expected)) return false;
    }
    return true;
}

fn isOpenUnknown(shape: ir.PackShape) bool {
    return shape.prefix.len == 0 and shape.tail == .open;
}

fn hasBooleanOpenPrefix(shape: ir.PackShape) bool {
    return shape.tail == .open and shape.prefix.len != 0 and shape.prefix[0].kind == .boolean;
}

const InvocationKind = enum {
    ordinary,
    status_prefix,
};

const InvocationView = struct {
    argument_pack: ?ir.ValuePackId,
    result_arity: ir.ResultArity,
    kind: InvocationKind,
};

fn invocationView(operation: ir.Operation) ?InvocationView {
    return switch (operation) {
        .call => |value| .{ .argument_pack = value.argument_pack, .result_arity = value.result_arity, .kind = .ordinary },
        .namecall => |value| .{ .argument_pack = value.argument_pack, .result_arity = value.result_arity, .kind = .ordinary },
        .protected_call => |value| .{ .argument_pack = value.argument_pack, .result_arity = value.result_arity, .kind = .status_prefix },
        .coroutine_resume => |value| .{ .argument_pack = value.argument_pack, .result_arity = value.result_arity, .kind = .status_prefix },
        .coroutine_yield => |value| .{ .argument_pack = value.argument_pack, .result_arity = value.result_arity, .kind = .ordinary },
        else => null,
    };
}

fn instructionFunction(program: *const ir.Program, instruction: ir.Instruction) ?ir.FunctionId {
    if (!validId(instruction.block, program.blocks.len)) return null;
    return program.blocks[instruction.block.index()].function;
}

fn incrementDefinition(counts: []u32, pack_id: ir.ValuePackId) void {
    if (counts[pack_id.index()] != std.math.maxInt(u32)) counts[pack_id.index()] += 1;
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}

fn withFixedResultArity(operation: ir.Operation, count: u16) ir.Operation {
    return switch (operation) {
        .call => |value| blk: {
            var changed = value;
            changed.result_arity = .{ .fixed = count };
            break :blk .{ .call = changed };
        },
        .namecall => |value| blk: {
            var changed = value;
            changed.result_arity = .{ .fixed = count };
            break :blk .{ .namecall = changed };
        },
        .protected_call => |value| blk: {
            var changed = value;
            changed.result_arity = .{ .fixed = count };
            break :blk .{ .protected_call = changed };
        },
        .coroutine_resume => |value| blk: {
            var changed = value;
            changed.result_arity = .{ .fixed = count };
            break :blk .{ .coroutine_resume = changed };
        },
        .coroutine_yield => |value| blk: {
            var changed = value;
            changed.result_arity = .{ .fixed = count };
            break :blk .{ .coroutine_yield = changed };
        },
        else => unreachable,
    };
}

test "result-bearing invocation families share fixed arity validation" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const result_id = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = result_id,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } },
    }};
    var instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = block_id,
        .operation = undefined,
        .results = &.{result_id},
        .effects = .dynamic_call,
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{instruction_id},
        .terminator = .{ .return_values = &.{result_id} },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "invocation-fixed-arity-matrix",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    const Row = struct {
        operation: ir.Operation,
        kind: InvocationKind,
    };
    const rows = [_]Row{
        .{ .operation = .{ .call = .{ .callee = result_id, .arguments = &.{}, .result_arity = .{ .fixed = 2 } } }, .kind = .ordinary },
        .{ .operation = .{ .namecall = .{ .receiver = result_id, .method = "invoke", .arguments = &.{}, .result_arity = .{ .fixed = 2 } } }, .kind = .ordinary },
        .{ .operation = .{ .protected_call = .{ .callee = result_id, .arguments = &.{}, .result_arity = .{ .fixed = 2 } } }, .kind = .status_prefix },
        .{ .operation = .{ .coroutine_resume = .{ .thread = result_id, .arguments = &.{}, .result_arity = .{ .fixed = 2 } } }, .kind = .status_prefix },
        .{ .operation = .{ .coroutine_yield = .{ .arguments = &.{}, .result_arity = .{ .fixed = 2 } } }, .kind = .ordinary },
    };

    for (rows) |row| {
        const invocation = invocationView(row.operation) orelse return error.TestUnexpectedResult;
        try std.testing.expectEqual(row.kind, invocation.kind);
        instructions[0].operation = row.operation;
        var report = diagnostics.Report.init(std.testing.allocator);
        defer report.deinit();
        try validate(std.testing.allocator, &report, &program, .core, null);
        try std.testing.expectEqual(@as(usize, 1), report.diagnostics.items.len);
        try std.testing.expect(report.contains(.invalid_result_arity));
    }

    const boundary_results = [_]ir.ValueId{result_id} ** luau_runtime.max_local_registers;
    instructions[0].results = &boundary_results;
    for (rows) |row| {
        instructions[0].operation = withFixedResultArity(row.operation, luau_runtime.max_local_registers);
        var report = diagnostics.Report.init(std.testing.allocator);
        defer report.deinit();
        try validate(std.testing.allocator, &report, &program, .readable_luau, null);
        try std.testing.expect(report.isClean());
    }

    const excessive_results = [_]ir.ValueId{result_id} ** (luau_runtime.max_local_registers + 1);
    instructions[0].results = &excessive_results;
    for (rows) |row| {
        instructions[0].operation = withFixedResultArity(row.operation, luau_runtime.max_local_registers + 1);
        var report = diagnostics.Report.init(std.testing.allocator);
        defer report.deinit();
        try validate(std.testing.allocator, &report, &program, .readable_luau, null);
        try std.testing.expectEqual(@as(usize, 1), report.diagnostics.items.len);
        try std.testing.expect(report.contains(.unsupported_readable_result_arity));
    }
}

test "fixed pack projections share the Luau result ceiling" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const result_id = ir.ValueId.fromIndex(0);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const boundary_results = [_]ir.ValueId{result_id} ** luau_runtime.max_local_registers;
    const excessive_results = [_]ir.ValueId{result_id} ** (luau_runtime.max_local_registers + 1);
    const values = [_]ir.Value{.{
        .id = result_id,
        .function = function_id,
        .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } },
    }};
    const packs = [_]ir.ValuePack{.{
        .id = pack_id,
        .function = function_id,
        .origin = .{ .varargs = function_id },
        .evidence = &.{evidence_id},
    }};
    var instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = block_id,
        .operation = .{ .adjust_pack = pack_id },
        .results = &boundary_results,
        .effects = .pure,
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{instruction_id},
        .terminator = .{ .return_values = &.{result_id} },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{block_id},
        .entry_block = block_id,
        .is_variadic = true,
        .vararg_pack = pack_id,
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .dynamic_fixture,
        .locator = "fixture:fixed-pack-projection-limit",
    }};
    const program: ir.Program = .{
        .program_id = "fixed-pack-projection-limit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
        .evidence = &evidence,
    };

    var boundary_report = diagnostics.Report.init(std.testing.allocator);
    defer boundary_report.deinit();
    try validate(std.testing.allocator, &boundary_report, &program, .readable_luau, null);
    try std.testing.expect(boundary_report.isClean());

    instructions[0].results = &excessive_results;
    var excessive_report = diagnostics.Report.init(std.testing.allocator);
    defer excessive_report.deinit();
    try validate(std.testing.allocator, &excessive_report, &program, .readable_luau, null);
    try std.testing.expectEqual(@as(usize, 1), excessive_report.diagnostics.items.len);
    try std.testing.expect(excessive_report.contains(.unsupported_readable_result_arity));
}
