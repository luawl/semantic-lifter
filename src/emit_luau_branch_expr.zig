const std = @import("std");
const ir = @import("ir.zig");
const structure = @import("structure.zig");
const emission_scope = @import("emit_luau_scope.zig");
const emission_planning = @import("emit_luau_plan.zig");
const render = @import("emit_luau_expr.zig");
const place_render = @import("emit_luau_place.zig");

pub const Plan = struct {
    target: ir.ValueId,
    condition: ir.ValueId,
    then_value: ir.ValueId,
    else_value: ir.ValueId,
};

pub const Composition = struct {
    allocator: std.mem.Allocator,
    expressions: std.AutoHashMapUnmanaged(ir.ValueId, Plan),
    absorbed_values: std.AutoHashMapUnmanaged(ir.ValueId, ir.InstructionId),
    absorbed_instructions: []bool,
    rendered_counts: []usize,

    pub fn init(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        emission_plan: *const emission_planning.Plan,
        scopes: *const emission_scope.Plan,
        region: *const structure.Region,
    ) !Composition {
        if (!regionHasJoinedBranch(region)) return initEmptyComposition(allocator);

        var expressions: std.AutoHashMapUnmanaged(ir.ValueId, Plan) = .empty;
        errdefer expressions.deinit(allocator);
        var absorbed_values: std.AutoHashMapUnmanaged(ir.ValueId, ir.InstructionId) = .empty;
        errdefer absorbed_values.deinit(allocator);
        const absorbed_instructions = try allocator.alloc(bool, program.instructions.len);
        errdefer allocator.free(absorbed_instructions);
        @memset(absorbed_instructions, false);
        const rendered_counts = try allocator.alloc(usize, program.values.len);
        errdefer allocator.free(rendered_counts);
        @memset(rendered_counts, 0);

        var uses = try emission_plan.dead.semanticUseCounts(allocator, program);
        defer uses.deinit();
        if (region.nodes.len >= 2) {
            for (region.nodes[0 .. region.nodes.len - 1], region.nodes[1..]) |*producer_node, *consumer_node| {
                const producer_structured = switch (producer_node.*) {
                    .branch => |value| value,
                    else => continue,
                };
                const consumer_block = switch (consumer_node.*) {
                    .branch => |value| value.block,
                    .block => |value| value,
                    else => continue,
                };
                if (producer_structured.join == null or producer_structured.join.? != consumer_block) continue;
                if (consumer_block.index() >= program.blocks.len) continue;
                const producer_group = scopes.nodeContainerScope(producer_node) orelse continue;
                const consumer_group = scopes.nodeContainerScope(consumer_node) orelse continue;
                if (consumer_group != producer_group) continue;
                const consumer_scope = scopes.nodeScope(consumer_node) orelse continue;
                if (scopes.declarationCount(consumer_scope) != 0) continue;

                const producer_branch = blockBranch(program, producer_structured.block) orelse continue;
                const producer = match(program, emission_plan, scopes, producer_branch, producer_structured) orelse continue;
                if (!scopes.valueDeclaredAtSyntheticSite(producer.target)) continue;
                if (producer.target.index() >= uses.values.len or uses.values[producer.target.index()] != 1) continue;
                const can_defer = switch (consumer_node.*) {
                    .branch => |consumer_structured| branchDirectlyConsumes(
                        program,
                        emission_plan,
                        scopes,
                        consumer_structured,
                        producer.target,
                    ),
                    .block => |block_id| blockDirectlyConsumes(
                        program,
                        emission_plan,
                        scopes,
                        block_id,
                        producer.target,
                    ),
                    else => false,
                };
                if (!can_defer) continue;
                try expressions.put(allocator, producer.target, producer);
            }
        }

        for (region.nodes) |*node| {
            const structured = switch (node.*) {
                .branch => |value| value,
                else => continue,
            };
            const branch = blockBranch(program, structured.block) orelse continue;
            const expression_plan = match(program, emission_plan, scopes, branch, structured) orelse continue;
            const absorbed = absorbConditionProducer(
                program,
                emission_plan,
                scopes,
                uses.values,
                expression_plan,
                structured,
            ) orelse continue;
            try absorbed_values.put(allocator, absorbed.value, absorbed.instruction);
            absorbed_instructions[absorbed.instruction.index()] = true;
        }
        return .{
            .allocator = allocator,
            .expressions = expressions,
            .absorbed_values = absorbed_values,
            .absorbed_instructions = absorbed_instructions,
            .rendered_counts = rendered_counts,
        };
    }

    pub fn deinit(self: *Composition) void {
        self.allocator.free(self.rendered_counts);
        self.allocator.free(self.absorbed_instructions);
        self.absorbed_values.deinit(self.allocator);
        self.expressions.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn expression(self: *const Composition, value_id: ir.ValueId) ?Plan {
        return self.expressions.get(value_id);
    }

    pub fn isDeferred(self: *const Composition, value_id: ir.ValueId) bool {
        return self.expression(value_id) != null;
    }

    pub fn isOverridden(self: *const Composition, value_id: ir.ValueId) bool {
        return self.isDeferred(value_id) or self.absorbed_values.contains(value_id);
    }

    pub fn instructionIsAbsorbed(self: *const Composition, instruction_id: ir.InstructionId) bool {
        return instruction_id.index() < self.absorbed_instructions.len and self.absorbed_instructions[instruction_id.index()];
    }

    pub fn markRendered(self: *const Composition, value_id: ir.ValueId) bool {
        if (!self.isOverridden(value_id) or value_id.index() >= self.rendered_counts.len) return false;
        self.rendered_counts[value_id.index()] += 1;
        return true;
    }

    pub fn allRenderedExactlyOnce(self: *const Composition) bool {
        var iterator = self.expressions.keyIterator();
        while (iterator.next()) |value_id| {
            if (value_id.index() >= self.rendered_counts.len or self.rendered_counts[value_id.index()] != 1) return false;
        }
        var absorbed_iterator = self.absorbed_values.keyIterator();
        while (absorbed_iterator.next()) |value_id| {
            if (value_id.index() >= self.rendered_counts.len or self.rendered_counts[value_id.index()] != 1) return false;
        }
        return true;
    }

    pub fn valueOverride(self: *const Composition) render.ValueOverride {
        return .{
            .context = @ptrCast(@constCast(self)),
            .contains_fn = overrideContains,
            .emit_fn = overrideEmit,
        };
    }
};

fn initEmptyComposition(allocator: std.mem.Allocator) !Composition {
    const absorbed_instructions = try allocator.alloc(bool, 0);
    errdefer allocator.free(absorbed_instructions);
    const rendered_counts = try allocator.alloc(usize, 0);
    return .{
        .allocator = allocator,
        .expressions = .empty,
        .absorbed_values = .empty,
        .absorbed_instructions = absorbed_instructions,
        .rendered_counts = rendered_counts,
    };
}

fn regionHasJoinedBranch(region: *const structure.Region) bool {
    for (region.nodes) |node| switch (node) {
        .branch => |branch| if (branch.join != null) return true,
        else => {},
    };
    return false;
}

pub fn markDeclarations(
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    scopes: *emission_scope.Plan,
    region: *const structure.Region,
    is_root: bool,
) void {
    var group_count: usize = 0;
    var counted_group: emission_scope.ScopeId = emission_scope.invalid_scope;
    for (region.nodes) |*node| {
        const group = scopes.nodeContainerScope(node) orelse continue;
        if (group != counted_group) {
            counted_group = group;
            group_count += 1;
        }
    }
    const wraps_groups = group_count > 1;

    for (region.nodes, 0..) |*node, index| {
        const structured = switch (node.*) {
            .branch => |value| value,
            else => continue,
        };
        const join = structured.join orelse continue;
        if ((region.stop != null and region.stop.? == join) or index + 1 >= region.nodes.len or region.nodes[index + 1].blockId() != join) continue;
        const group = scopes.nodeContainerScope(node) orelse continue;
        const join_group = scopes.nodeContainerScope(&region.nodes[index + 1]) orelse continue;
        if (join_group != group) continue;
        const branch = switch (program.blocks[structured.block.index()].terminator) {
            .branch => |value| value,
            else => continue,
        };
        const expression_plan = match(program, emission_plan, scopes, branch, structured) orelse continue;
        const target_scope = scopes.valueScope(expression_plan.target) orelse continue;
        const root_scope_is_physical = is_root and !wraps_groups and target_scope == scopes.rootScope();
        if (target_scope != group and !root_scope_is_physical) continue;
        _ = scopes.markSyntheticValueDeclaration(expression_plan.target, target_scope);
    }

    for (region.nodes) |*node| switch (node.*) {
        .branch => |branch| {
            markDeclarations(program, emission_plan, scopes, branch.then_region, false);
            markDeclarations(program, emission_plan, scopes, branch.else_region, false);
        },
        .loop => |loop| markDeclarations(program, emission_plan, scopes, loop.body_region, false),
        .latch_loop => |loop| markDeclarations(program, emission_plan, scopes, loop.body_region, false),
        .infinite_loop => |loop| {
            markDeclarations(program, emission_plan, scopes, loop.body_region, false);
            if (loop.shared_side_exit) |side_exit| {
                for (side_exit.entries) |entry| markDeclarations(program, emission_plan, scopes, entry.region, false);
            }
        },
        .loop_boundary => |control| {
            markDeclarations(program, emission_plan, scopes, control.body_region, false);
            switch (control.boundary) {
                .side_exit => |side_exit| markDeclarations(program, emission_plan, scopes, side_exit.region, false),
                .side_escape => |side_escape| markDeclarations(program, emission_plan, scopes, side_escape.region, false),
                else => {},
            }
        },
        .block, .loop_control, .loop_terminal => {},
    };
}

fn overrideContains(context: ?*anyopaque, value_id: ir.ValueId) bool {
    const composition: *const Composition = @ptrCast(@alignCast(context orelse return false));
    return composition.isOverridden(value_id);
}

fn overrideEmit(
    context: ?*anyopaque,
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    values: render.ValuePlan,
    value_id: ir.ValueId,
) render.RenderError!void {
    const composition: *const Composition = @ptrCast(@alignCast(context orelse return error.UnsupportedOperation));
    if (!composition.markRendered(value_id)) return error.UnsupportedOperation;
    if (composition.expression(value_id)) |expression_plan| {
        try emitValue(output, allocator, program, values, expression_plan, composition, 0);
        return;
    }
    const instruction_id = composition.absorbed_values.get(value_id) orelse return error.UnsupportedOperation;
    if (instruction_id.index() >= program.instructions.len) return error.UnsupportedOperation;
    const instruction = program.instructions[instruction_id.index()];
    switch (instruction.operation) {
        .call,
        .namecall,
        .protected_call,
        .coroutine_create,
        .coroutine_resume,
        .coroutine_yield,
        => try render.plannedInvocation(output, allocator, program, values, values.packs, instruction),
        .make_table_literal => |constructor| try render.plannedTableConstructor(output, allocator, program, values, instruction.id, constructor),
        else => try render.expressionRoot(output, allocator, program, values, instruction.operation),
    }
}

fn valuesWithComposition(
    emission_plan: *const emission_planning.Plan,
    place_aliases: []const place_render.Alias,
    composition: ?*const Composition,
) render.ValuePlan {
    var values = emission_plan.values(place_aliases);
    if (composition) |value| values.value_override = value.valueOverride();
    return values;
}

pub fn emitAssignment(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    expression_plan: Plan,
    composition: ?*const Composition,
    indent: []const u8,
    place_aliases: []const place_render.Alias,
) (std.mem.Allocator.Error || error{ UnsupportedControlFlow, UnsupportedOperation })!void {
    try output.appendSlice(allocator, indent);
    if (scopes.valueDeclaredAtSyntheticSite(expression_plan.target) and
        !emission_plan.names.valueUsesStorage(expression_plan.target))
    {
        try output.appendSlice(allocator, "local ");
    }
    try render.valueName(output, allocator, &emission_plan.names, expression_plan.target);
    try output.appendSlice(allocator, " = ");
    try emitValue(output, allocator, program, valuesWithComposition(emission_plan, place_aliases, composition), expression_plan, composition, 0);
    try output.append(allocator, '\n');
}

pub fn emitCondition(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    condition: ir.ValueId,
    composition: ?*const Composition,
    negated: bool,
    place_aliases: []const place_render.Alias,
) (std.mem.Allocator.Error || error{ UnsupportedControlFlow, UnsupportedOperation })!void {
    const resolved = emission_plan.dead.resolveValue(condition);
    if (composition) |value| {
        if (value.expression(resolved)) |nested| {
            if (!value.markRendered(resolved)) return error.UnsupportedOperation;
            try output.append(allocator, '(');
            try emitValue(output, allocator, program, valuesWithComposition(emission_plan, place_aliases, composition), nested, composition, 0);
            try output.append(allocator, ')');
            return;
        }
    }
    if (negated)
        try render.valueUseGroupedScalar(output, allocator, program, valuesWithComposition(emission_plan, place_aliases, composition), condition)
    else
        try render.valueUseScalar(output, allocator, program, valuesWithComposition(emission_plan, place_aliases, composition), condition);
}

fn emitValue(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    values: render.ValuePlan,
    expression_plan: Plan,
    composition: ?*const Composition,
    depth: usize,
) render.RenderError!void {
    if (depth > program.values.len) return error.UnsupportedOperation;
    const resolved_condition = values.dead.resolveValue(expression_plan.condition);
    const resolved_then = values.dead.resolveValue(expression_plan.then_value);
    const resolved_else = values.dead.resolveValue(expression_plan.else_value);

    if (resolved_else == resolved_condition) {
        try emitOperand(output, allocator, program, values, expression_plan.condition, composition, depth);
        try output.appendSlice(allocator, " and ");
        try emitOperand(output, allocator, program, values, expression_plan.then_value, composition, depth);
    } else if (resolved_then == resolved_condition) {
        try emitOperand(output, allocator, program, values, expression_plan.condition, composition, depth);
        try output.appendSlice(allocator, " or ");
        try emitOperand(output, allocator, program, values, expression_plan.else_value, composition, depth);
    } else {
        try output.appendSlice(allocator, "if ");
        try emitOperand(output, allocator, program, values, expression_plan.condition, composition, depth);
        try output.appendSlice(allocator, " then ");
        try emitOperand(output, allocator, program, values, expression_plan.then_value, composition, depth);
        try output.appendSlice(allocator, " else ");
        try emitOperand(output, allocator, program, values, expression_plan.else_value, composition, depth);
    }
}

fn emitOperand(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    values: render.ValuePlan,
    value_id: ir.ValueId,
    composition: ?*const Composition,
    depth: usize,
) render.RenderError!void {
    const resolved = values.dead.resolveValue(value_id);
    if (composition) |value| {
        if (value.expression(resolved)) |nested| {
            if (!value.markRendered(resolved)) return error.UnsupportedOperation;
            try output.append(allocator, '(');
            try emitValue(output, allocator, program, values, nested, composition, depth + 1);
            try output.append(allocator, ')');
            return;
        }
    }
    try render.valueUseScalar(output, allocator, program, values, value_id);
}

const AbsorbedCondition = struct {
    value: ir.ValueId,
    instruction: ir.InstructionId,
};

fn absorbConditionProducer(
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    uses: []const usize,
    expression_plan: Plan,
    structured: structure.Branch,
) ?AbsorbedCondition {
    const condition = emission_plan.dead.resolveValue(expression_plan.condition);
    const then_is_condition = emission_plan.dead.resolveValue(expression_plan.then_value) == condition;
    const else_is_condition = emission_plan.dead.resolveValue(expression_plan.else_value) == condition;
    if (then_is_condition == else_is_condition) return null;
    if (condition.index() >= program.values.len or condition.index() >= uses.len or uses[condition.index()] != 2) return null;

    const origin = switch (program.values[condition.index()].origin) {
        .instruction_result => |value| value,
        else => return null,
    };
    if (origin.index != 0 or origin.instruction.index() >= program.instructions.len) return null;
    const instruction = program.instructions[origin.instruction.index()];
    if (instruction.block != structured.block or instruction.results.len != 1 or instruction.results[0] != condition or instruction.pack_result != null) return null;
    if (emission_plan.packs.role(instruction.id) != .ordinary or !emission_plan.instructionMayEmit(instruction)) return null;
    if (!operationIsAbsorbable(instruction.operation)) return null;
    const instruction_scope = scopes.instructionScope(instruction.id) orelse return null;
    if (scopes.declarationCount(instruction_scope) != 0) return null;

    if (structured.block.index() >= program.blocks.len) return null;
    const block = program.blocks[structured.block.index()];
    var found = false;
    for (block.instructions) |instruction_id| {
        if (!found) {
            if (instruction_id == instruction.id) found = true;
            continue;
        }
        if (instruction_id.index() >= program.instructions.len) return null;
        if (emission_plan.dead.contains(instruction_id) and !emission_plan.dead.isInlined(instruction_id)) continue;
        return null;
    }
    if (!found) return null;
    return .{ .value = condition, .instruction = instruction.id };
}

fn operationIsAbsorbable(operation: ir.Operation) bool {
    return switch (operation) {
        .constant, .copy, .unary, .binary, .environment_get, .table_get, .make_table, .make_table_literal, .string_interpolate, .function_ref => true,
        .call => |value| resultArityIsOne(value.result_arity),
        .namecall => |value| resultArityIsOne(value.result_arity),
        .protected_call => |value| resultArityIsOne(value.result_arity),
        .coroutine_create => true,
        .coroutine_resume => |value| resultArityIsOne(value.result_arity),
        .coroutine_yield => |value| resultArityIsOne(value.result_arity),
        else => false,
    };
}

fn resultArityIsOne(arity: ir.ResultArity) bool {
    return switch (arity) {
        .fixed => |count| count == 1,
        .variadic => false,
    };
}

fn branchDirectlyConsumes(
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    structured: structure.Branch,
    target: ir.ValueId,
) bool {
    if (structured.block.index() >= program.blocks.len) return false;
    const block = program.blocks[structured.block.index()];
    if (firstInstructionDirectlyConsumes(program, emission_plan, scopes, block, target)) |result| return result;
    const branch = switch (block.terminator) {
        .branch => |value| value,
        else => return false,
    };
    return emission_plan.dead.resolveValue(branch.condition) == target;
}

fn blockDirectlyConsumes(
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    block_id: ir.BlockId,
    target: ir.ValueId,
) bool {
    if (block_id.index() >= program.blocks.len) return false;
    const block = program.blocks[block_id.index()];
    if (firstInstructionDirectlyConsumes(program, emission_plan, scopes, block, target)) |result| return result;
    return returnDirectlyUses(emission_plan, block.terminator, target);
}

fn firstInstructionDirectlyConsumes(
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    block: ir.Block,
    target: ir.ValueId,
) ?bool {
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return false;
        if (emission_plan.dead.contains(instruction_id) and !emission_plan.dead.isInlined(instruction_id)) continue;
        const instruction = program.instructions[instruction_id.index()];
        if (!instructionRendersWithinBlock(program, emission_plan, scopes, block, instruction_id)) return false;
        const instruction_scope = scopes.instructionScope(instruction_id) orelse return false;
        if (scopes.declarationCount(instruction_scope) != 0) return false;
        return instructionDirectlyUses(emission_plan, instruction.operation, target);
    }
    return null;
}

fn instructionRendersWithinBlock(
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    block: ir.Block,
    first: ir.InstructionId,
) bool {
    var current = first;
    var remaining = program.instructions.len + 1;
    while (remaining != 0) : (remaining -= 1) {
        if (current.index() >= program.instructions.len) return false;
        const instruction = program.instructions[current.index()];
        if (instruction.block != block.id or scopes.instructionIsMovedLiteralInitializer(current)) return false;
        if (emission_plan.instructionMayEmit(instruction)) return true;

        if (emission_plan.fused_values.consumer(current)) |consumer| {
            switch (consumer) {
                .instruction => |instruction_id| {
                    current = instruction_id;
                    continue;
                },
                .terminator => |block_id| return block_id == block.id and terminatorRendersWithinBlock(block.terminator),
            }
        }
        if (emission_plan.place_writes.consumerForProducer(current)) |instruction_id| {
            current = instruction_id;
            continue;
        }
        if (emission_plan.closure_stores.consumerForProducer(current)) |instruction_id| {
            current = instruction_id;
            continue;
        }
        switch (emission_plan.packs.role(current)) {
            .fused_invocation_producer, .fused_pack_values_producer => |instruction_id| {
                current = instruction_id;
                continue;
            },
            .fused_return_producer, .fused_pack_values_return_producer => |block_id| {
                return block_id == block.id and terminatorRendersWithinBlock(block.terminator);
            },
            else => return false,
        }
    }
    return false;
}

fn terminatorRendersWithinBlock(terminator: ir.Terminator) bool {
    return switch (terminator) {
        .branch, .return_values, .return_expanded, .throw_error => true,
        .jump, .return_pack, .unreachable_block => false,
    };
}

fn instructionDirectlyUses(emission_plan: *const emission_planning.Plan, operation: ir.Operation, target: ir.ValueId) bool {
    return switch (operation) {
        .place_write => |value| valueMatches(emission_plan, value.value, target),
        else => invocationDirectlyUses(emission_plan, operation, target),
    };
}

fn invocationDirectlyUses(emission_plan: *const emission_planning.Plan, operation: ir.Operation, target: ir.ValueId) bool {
    return switch (operation) {
        .call => |value| valueMatches(emission_plan, value.callee, target) or valuesContain(emission_plan, value.arguments, target),
        .namecall => |value| valueMatches(emission_plan, value.receiver, target) or valuesContain(emission_plan, value.arguments, target),
        .protected_call => |value| valueMatches(emission_plan, value.callee, target) or
            (value.error_handler != null and valueMatches(emission_plan, value.error_handler.?, target)) or
            valuesContain(emission_plan, value.arguments, target),
        .coroutine_create => |value| valueMatches(emission_plan, value.callee, target),
        .coroutine_resume => |value| valueMatches(emission_plan, value.thread, target) or valuesContain(emission_plan, value.arguments, target),
        .coroutine_yield => |value| valuesContain(emission_plan, value.arguments, target),
        else => false,
    };
}

fn returnDirectlyUses(emission_plan: *const emission_planning.Plan, terminator: ir.Terminator, target: ir.ValueId) bool {
    return switch (terminator) {
        .return_values => |values| valuesContain(emission_plan, values, target),
        .return_expanded => |expanded| valuesContain(emission_plan, expanded.values, target),
        else => false,
    };
}

fn valuesContain(emission_plan: *const emission_planning.Plan, values: []const ir.ValueId, target: ir.ValueId) bool {
    for (values) |value_id| {
        if (valueMatches(emission_plan, value_id, target)) return true;
    }
    return false;
}

fn valueMatches(emission_plan: *const emission_planning.Plan, value_id: ir.ValueId, target: ir.ValueId) bool {
    return emission_plan.dead.resolveValue(value_id) == target;
}

pub fn match(
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    branch: ir.Branch,
    structured: structure.Branch,
) ?Plan {
    if (structured.then_edge_override != null or structured.else_edge_override != null or
        structured.then_shared_reentry != null or structured.else_shared_reentry != null) return null;
    if (branch.then_edge.target == branch.else_edge.target and
        std.mem.eql(ir.ValueId, branch.then_edge.arguments, branch.else_edge.arguments)) return null;
    const join_id = structured.join orelse return null;
    if (join_id.index() >= program.blocks.len) return null;
    const join = program.blocks[join_id.index()];
    if (join.parameters.len != 1 or emission_plan.dead.isValueAlias(join.parameters[0])) return null;
    const then_value = arm(program, emission_plan, scopes, branch.then_edge, structured.then_region, join_id) orelse return null;
    const else_value = arm(program, emission_plan, scopes, branch.else_edge, structured.else_region, join_id) orelse return null;
    return .{
        .target = join.parameters[0],
        .condition = branch.condition,
        .then_value = then_value,
        .else_value = else_value,
    };
}

fn arm(
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    entry: ir.Edge,
    region: *const structure.Region,
    join: ir.BlockId,
) ?ir.ValueId {
    if (region.terminal_projection != null or region.continue_projection != null or region.escape_projection != null) return null;
    if (region.stop == null or region.stop.? != join) return null;
    if (region.nodes.len == 0) {
        if (entry.target != join or entry.arguments.len != 1) return null;
        return entry.arguments[0];
    }
    if (region.nodes.len != 1) return null;
    const node = &region.nodes[0];
    const block_id = switch (node.*) {
        .block => |value| value,
        else => return null,
    };
    if (entry.target != block_id or block_id.index() >= program.blocks.len) return null;
    const block = program.blocks[block_id.index()];
    if (entry.arguments.len != block.parameters.len) return null;
    if (block.instructions.len == 0) {
        const exit = switch (block.terminator) {
            .jump => |value| value,
            else => return null,
        };
        if (exit.target != join or exit.arguments.len != 1) return null;
        return substituteBlockParameter(block.parameters, entry.arguments, exit.arguments[0]);
    }
    if (block.parameters.len != 0) return null;
    const node_scope = scopes.nodeScope(node) orelse return null;
    if (scopes.declarationCount(node_scope) != 0) return null;
    if (scopes.nodeContainerScope(node)) |container| {
        if (scopes.declarationCount(container) != 0) return null;
    }
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return null;
        const instruction = program.instructions[instruction_id.index()];
        if (emission_plan.instructionMayEmit(instruction) and !scopes.instructionIsMovedLiteralInitializer(instruction.id)) return null;
    }
    const exit = switch (block.terminator) {
        .jump => |value| value,
        else => return null,
    };
    if (exit.target != join or exit.arguments.len != 1) return null;
    return exit.arguments[0];
}

fn substituteBlockParameter(parameters: []const ir.ValueId, arguments: []const ir.ValueId, value_id: ir.ValueId) ir.ValueId {
    for (parameters, arguments) |parameter, argument| {
        if (parameter == value_id) return argument;
    }
    return value_id;
}

fn blockBranch(program: *const ir.Program, block_id: ir.BlockId) ?ir.Branch {
    if (block_id.index() >= program.blocks.len) return null;
    return switch (program.blocks[block_id.index()].terminator) {
        .branch => |value| value,
        else => null,
    };
}
