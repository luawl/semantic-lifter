const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const structure = @import("structure.zig");
const runtime_uses = @import("runtime_uses.zig");
const diagnostics = @import("diagnostics.zig");
const iteration_exit_transfer = @import("iteration_exit_transfer.zig");
const iteration_state = @import("iteration_state.zig");

pub const NumericLoop = struct {
    transition: ir.Instruction,
    operation: ir.NumericForNext,
    initial_arguments: []const ir.ValueId,
    body_parameter: ir.ValueId,
    initial_flag_instruction: ?ir.InstructionId,
};

pub const GenericLoop = struct {
    transition: ir.Instruction,
    operation: ir.GenericForNext,
    initial_arguments: []const ir.ValueId,
    body_parameters: []const ir.ValueId,
    initial_flag_instruction: ?ir.InstructionId,
};

pub const Match = union(enum) {
    numeric: NumericLoop,
    generic: GenericLoop,

    pub fn instructionId(self: Match) ir.InstructionId {
        return switch (self) {
            .numeric => |value| value.transition.id,
            .generic => |value| value.transition.id,
        };
    }
};

pub const Acyclic = struct {
    protocol: Match,
    body_region: *const structure.Region,
    body_edge: ir.Edge,
    exit_edge: ir.Edge,
    /// The exit arm's region when the header has no join (the body always returns: the body arm reaches neither the
    /// exit nor the region stop, and the exit arm is written after the loop); `null` for the join form.
    exit_region: ?*const structure.Region = null,
};

pub fn transitionForHeader(program: *const ir.Program, header: ir.Block) ?ir.Instruction {
    if (header.instructions.len != 1 or header.parameters.len != 4) return null;
    const transition_id = header.instructions[0];
    if (transition_id.index() >= program.instructions.len) return null;
    const transition = program.instructions[transition_id.index()];
    if (transition.id != transition_id or transition.block != header.id or transition.results.len == 0) return null;
    const branch = switch (header.terminator) {
        .branch => |value| value,
        else => return null,
    };
    if (branch.condition != transition.results[0]) return null;
    const matches = switch (transition.operation) {
        .numeric_for_next => |operation| transition.results.len == 4 and
            operation.control == header.parameters[0] and
            operation.limit == header.parameters[1] and
            operation.step == header.parameters[2] and
            operation.initial == header.parameters[3],
        .generic_for_next => |operation| operation.variable_count != 0 and
            transition.results.len == @as(usize, operation.variable_count) + 3 and
            operation.iterator == header.parameters[0] and
            operation.state == header.parameters[1] and
            operation.control == header.parameters[2] and
            operation.initial == header.parameters[3],
        else => false,
    };
    return if (matches) transition else null;
}

pub fn matchLoop(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    loop: structure.Loop,
) std.mem.Allocator.Error!?Match {
    if (loop.header.index() >= program.blocks.len or
        loop.body_edge.target.index() >= program.blocks.len or
        loop.exit_edge.target.index() >= program.blocks.len)
    {
        return null;
    }
    const header = program.blocks[loop.header.index()];

    const branch = switch (header.terminator) {
        .branch => |value| value,
        else => return null,
    };
    if (branch.condition.index() >= program.values.len) return null;
    const expected_body = if (loop.continue_on_true) branch.then_edge else branch.else_edge;
    const expected_exit = if (loop.continue_on_true) branch.else_edge else branch.then_edge;
    if (!sameEdge(expected_body, loop.body_edge) or !sameEdge(expected_exit, loop.exit_edge)) return null;

    const body = program.blocks[loop.body_edge.target.index()];
    if (body.function != header.function) return null;
    if (header.function.index() >= program.functions.len) return null;
    const function = program.functions[header.function.index()];
    if (function.id != header.function) return null;
    var analysis = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
        error.InvalidCfg => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    const identity = try allocator.alloc(ir.ValueId, program.values.len);
    defer allocator.free(identity);
    for (identity, 0..) |*value, index| value.* = ir.ValueId.fromIndex(index);
    const excluded = try allocator.alloc(bool, program.instructions.len);
    defer allocator.free(excluded);
    @memset(excluded, false);
    var uses = try runtime_uses.Counts.init(allocator, program, identity, excluded);
    defer uses.deinit();

    return matchLoopWithContext(program, &analysis, &uses, loop);
}

/// Matches a loop using facts owned by the caller. Lexical planning reuses
/// one function analysis and one read-only use-count snapshot instead of
/// rebuilding whole-program CFG/scope state for every loop.
pub fn matchLoopWithContext(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    uses: *const runtime_uses.Counts,
    loop: structure.Loop,
) std.mem.Allocator.Error!?Match {
    if (loop.header.index() >= program.blocks.len or
        loop.body_edge.target.index() >= program.blocks.len or
        loop.exit_edge.target.index() >= program.blocks.len)
    {
        return null;
    }
    const header = program.blocks[loop.header.index()];
    const transition = transitionForHeader(program, header) orelse return null;

    const branch = switch (header.terminator) {
        .branch => |value| value,
        else => return null,
    };
    if (branch.condition.index() >= program.values.len) return null;
    const expected_body = if (loop.continue_on_true) branch.then_edge else branch.else_edge;
    const expected_exit = if (loop.continue_on_true) branch.else_edge else branch.then_edge;
    if (!sameEdge(expected_body, loop.body_edge) or !sameEdge(expected_exit, loop.exit_edge)) return null;

    const body = program.blocks[loop.body_edge.target.index()];
    if (body.function != header.function or analysis.function.id != header.function) return null;
    if (!try iteration_exit_transfer.supportsInvariantArguments(program, analysis, header.id, loop.exit_edge)) return null;

    const incoming = inspectIncomingEdges(program, analysis, loop, transition, uses) orelse return null;
    if (incoming.external_count == 0 or incoming.internal_count == 0) return null;

    return switch (transition.operation) {
        .numeric_for_next => |operation| matchNumeric(program, analysis, loop, header, body, transition, operation, incoming, uses),
        .generic_for_next => |operation| matchGeneric(program, loop, header, body, transition, operation, incoming, uses),
        else => null,
    };
}

pub fn matchAcyclicBranch(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    branch_plan: structure.Branch,
) std.mem.Allocator.Error!?Acyclic {
    const shape = acyclicShape(program, branch_plan) orelse return null;
    const header = program.blocks[branch_plan.block.index()];
    const transition = transitionForHeader(program, header) orelse return null;
    if (header.function.index() >= program.functions.len) return null;
    const function = program.functions[header.function.index()];
    if (function.id != header.function) return null;

    var analysis = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
        error.InvalidCfg => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    if (try analysis.canReach(shape.body_edge.target, header.id)) return null;
    if (shape.exit_region != null) {
        // A header without a join: the body arm must leave the function or never finish, so `for ... do <body> end`
        // followed by the exit arm is the source's own control flow (an always-`break` body stays refused).
        if (try analysis.canReach(shape.body_edge.target, shape.exit_edge.target)) return null;
        if (shape.body_region.stop) |stop| {
            if (try analysis.canReach(shape.body_edge.target, stop)) return null;
        }
    }

    const identity = try allocator.alloc(ir.ValueId, program.values.len);
    defer allocator.free(identity);
    for (identity, 0..) |*value, index| value.* = ir.ValueId.fromIndex(index);
    const excluded = try allocator.alloc(bool, program.instructions.len);
    defer allocator.free(excluded);
    @memset(excluded, false);
    var uses = try runtime_uses.Counts.init(allocator, program, identity, excluded);
    defer uses.deinit();

    const incoming = (try inspectAcyclicIncomingEdges(program, &analysis, header, transition, &uses)) orelse return null;
    const body = program.blocks[shape.body_edge.target.index()];
    const protocol: Match = switch (transition.operation) {
        .numeric_for_next => |operation| matchAcyclicNumeric(
            program,
            header,
            body,
            transition,
            operation,
            shape.body_edge,
            incoming,
            &uses,
        ) orelse return null,
        .generic_for_next => |operation| matchAcyclicGeneric(
            program,
            header,
            body,
            transition,
            operation,
            shape.body_edge,
            incoming,
            &uses,
        ) orelse return null,
        else => return null,
    };
    return .{
        .protocol = protocol,
        .body_region = shape.body_region,
        .body_edge = shape.body_edge,
        .exit_edge = shape.exit_edge,
        .exit_region = shape.exit_region,
    };
}

const AcyclicShape = struct {
    body_region: *const structure.Region,
    body_edge: ir.Edge,
    exit_edge: ir.Edge,
    exit_region: ?*const structure.Region = null,
};

fn acyclicShape(program: *const ir.Program, plan: structure.Branch) ?AcyclicShape {
    if (plan.join == null) {
        // A header without a join. The native protocol branches on the transition's first
        // result with the loop variables on the then edge, so the then arm is the body arm and must be direct; the
        // exit arm may carry an override or a shared re-entry, which the emitter writes like a join-less else arm.
        if (plan.block.index() >= program.blocks.len or
            plan.then_edge_override != null or plan.then_shared_reentry != null)
        {
            return null;
        }
        const branch = switch (program.blocks[plan.block.index()].terminator) {
            .branch => |value| value,
            else => return null,
        };
        const body_region = plan.then_region;
        if (body_region.nodes.len == 0 or body_region.nodes[0].blockId() != branch.then_edge.target or
            body_region.loop_exit != null or body_region.continue_target != null or
            body_region.terminal_projection != null or body_region.continue_projection != null or
            body_region.stop_forwarding != null)
        {
            return null;
        }
        return .{
            .body_region = body_region,
            .body_edge = branch.then_edge,
            .exit_edge = branch.else_edge,
            .exit_region = plan.else_region,
        };
    }
    if (plan.block.index() >= program.blocks.len or plan.join == null or
        plan.then_edge_override != null or plan.else_edge_override != null or
        plan.then_shared_reentry != null or plan.else_shared_reentry != null)
    {
        return null;
    }
    const join = plan.join.?;
    const branch = switch (program.blocks[plan.block.index()].terminator) {
        .branch => |value| value,
        else => return null,
    };
    const then_direct = directJoinRegion(plan.then_region, branch.then_edge, join);
    const else_direct = directJoinRegion(plan.else_region, branch.else_edge, join);
    if (then_direct == else_direct) return null;
    const body_region = if (then_direct) plan.else_region else plan.then_region;
    const body_edge = if (then_direct) branch.else_edge else branch.then_edge;
    const exit_edge = if (then_direct) branch.then_edge else branch.else_edge;
    if (body_edge.target == join or body_region.nodes.len == 0 or body_region.stop != join or
        body_region.loop_exit != null or body_region.continue_target != null or
        body_region.terminal_projection != null or body_region.continue_projection != null or
        body_region.stop_forwarding != null or body_region.nodes[0].blockId() != body_edge.target)
    {
        return null;
    }
    return .{ .body_region = body_region, .body_edge = body_edge, .exit_edge = exit_edge };
}

fn directJoinRegion(region: *const structure.Region, edge: ir.Edge, join: ir.BlockId) bool {
    return edge.target == join and region.nodes.len == 0 and region.stop == join and
        region.loop_exit == null and region.continue_target == null and
        region.terminal_projection == null and region.continue_projection == null and
        region.stop_forwarding == null;
}

fn inspectAcyclicIncomingEdges(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    header: ir.Block,
    transition: ir.Instruction,
    uses: *const runtime_uses.Counts,
) std.mem.Allocator.Error!?Incoming {
    if (!allExactUses(uses, header.parameters, 1)) return null;
    var incoming: Incoming = .{};
    for (program.blocks) |source| {
        if (source.function != header.function or !analysis.isReachable(source.id)) continue;
        switch (source.terminator) {
            .jump => |edge| if (!try inspectAcyclicIncomingEdge(program, analysis, header, transition, source.id, edge, &incoming)) return null,
            .branch => |branch| {
                if (!try inspectAcyclicIncomingEdge(program, analysis, header, transition, source.id, branch.then_edge, &incoming)) return null;
                if (!try inspectAcyclicIncomingEdge(program, analysis, header, transition, source.id, branch.else_edge, &incoming)) return null;
            },
            else => {},
        }
    }
    return if (incoming.external_count == 0) null else incoming;
}

fn inspectAcyclicIncomingEdge(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    header: ir.Block,
    transition: ir.Instruction,
    source: ir.BlockId,
    edge: ir.Edge,
    incoming: *Incoming,
) std.mem.Allocator.Error!bool {
    if (edge.target != header.id) return true;
    if (edge.arguments.len != 4 or !isBooleanLiteral(program, edge.arguments[3], externalInitialValue(transition)) or
        try analysis.canReach(header.id, source))
    {
        return false;
    }
    if (incoming.external_arguments) |arguments| {
        if (!std.mem.eql(ir.ValueId, arguments, edge.arguments)) return false;
    } else {
        incoming.external_arguments = edge.arguments;
    }
    incoming.external_count += 1;
    return true;
}

fn matchAcyclicNumeric(
    program: *const ir.Program,
    header: ir.Block,
    body: ir.Block,
    transition: ir.Instruction,
    operation: ir.NumericForNext,
    body_edge: ir.Edge,
    incoming: Incoming,
    uses: *const runtime_uses.Counts,
) ?Match {
    const initial_arguments = incoming.external_arguments orelse return null;
    if (initial_arguments.len != 4 or transition.results.len != 4 or
        body.parameters.len != 1 or body_edge.arguments.len != 1 or
        body_edge.arguments[0] != transition.results[3] or
        operation.control != header.parameters[0] or operation.limit != header.parameters[1] or
        operation.step != header.parameters[2] or operation.initial != header.parameters[3] or
        !resultsHaveExactUses(uses, transition.results, &.{ 1, 0, 0, 1 }))
    {
        return null;
    }
    return .{ .numeric = .{
        .transition = transition,
        .operation = operation,
        .initial_arguments = initial_arguments,
        .body_parameter = body.parameters[0],
        .initial_flag_instruction = initialFlagInstruction(program, uses, incoming, externalInitialValue(transition)),
    } };
}

fn matchAcyclicGeneric(
    program: *const ir.Program,
    header: ir.Block,
    body: ir.Block,
    transition: ir.Instruction,
    operation: ir.GenericForNext,
    body_edge: ir.Edge,
    incoming: Incoming,
    uses: *const runtime_uses.Counts,
) ?Match {
    const initial_arguments = incoming.external_arguments orelse return null;
    const variable_count = @as(usize, operation.variable_count);
    if (initial_arguments.len != 4 or variable_count == 0 or
        transition.results.len != variable_count + 3 or body.parameters.len != variable_count or
        body_edge.arguments.len != variable_count or operation.iterator != header.parameters[0] or
        operation.state != header.parameters[1] or operation.control != header.parameters[2] or
        operation.initial != header.parameters[3])
    {
        return null;
    }
    for (body_edge.arguments, transition.results[3..]) |argument, result| {
        if (argument != result) return null;
    }
    for (transition.results, 0..) |result, index| {
        const expected: usize = if (index == 0 or index >= 3) 1 else 0;
        if (result.index() >= uses.values.len or uses.values[result.index()] != expected) return null;
    }
    return .{ .generic = .{
        .transition = transition,
        .operation = operation,
        .initial_arguments = initial_arguments,
        .body_parameters = body.parameters,
        .initial_flag_instruction = initialFlagInstruction(program, uses, incoming, externalInitialValue(transition)),
    } };
}

pub fn validateFunction(
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    plan: *const structure.Plan,
) !void {
    const recognized = try allocator.alloc(bool, program.instructions.len);
    defer allocator.free(recognized);
    @memset(recognized, false);
    try markRecognized(allocator, program, plan.root, recognized);

    for (analysis.function.blocks) |block_id| {
        if (!analysis.isReachable(block_id) or block_id.index() >= program.blocks.len) continue;
        for (program.blocks[block_id.index()].instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) continue;
            const instruction = program.instructions[instruction_id.index()];
            switch (instruction.operation) {
                .numeric_for_next => |operation| if (!recognized[instruction_id.index()] and operation.mode != .semantic_normalized) {
                    try report.add(.unsupported_readable_iteration_protocol, instruction_id.index());
                },
                .generic_for_next => if (!recognized[instruction_id.index()]) {
                    try report.add(.unsupported_readable_iteration_protocol, instruction_id.index());
                },
                else => {},
            }
        }
    }
}

const Incoming = struct {
    external_count: usize = 0,
    internal_count: usize = 0,
    external_arguments: ?[]const ir.ValueId = null,
};

fn inspectIncomingEdges(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    loop: structure.Loop,
    transition: ir.Instruction,
    uses: *const runtime_uses.Counts,
) ?Incoming {
    var result: Incoming = .{};
    const header = program.blocks[loop.header.index()];
    if (!allExactUses(uses, header.parameters, 1)) return null;

    for (program.blocks) |source| {
        if (source.function != header.function or !analysis.isReachable(source.id)) continue;
        switch (source.terminator) {
            .jump => |edge| if (!inspectIncomingEdge(program, analysis, loop, transition, source.id, edge, &result)) return null,
            .branch => |branch| {
                if (!inspectIncomingEdge(program, analysis, loop, transition, source.id, branch.then_edge, &result)) return null;
                if (!inspectIncomingEdge(program, analysis, loop, transition, source.id, branch.else_edge, &result)) return null;
            },
            else => {},
        }
    }
    return result;
}

fn inspectIncomingEdge(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    loop: structure.Loop,
    transition: ir.Instruction,
    source: ir.BlockId,
    edge: ir.Edge,
    incoming: *Incoming,
) bool {
    if (edge.target != loop.header) return true;
    if (edge.arguments.len != 4) return false;
    const internal = regionContainsBlock(loop.body_region, source);
    if (!internal) {
        if (!isBooleanLiteral(program, edge.arguments[3], externalInitialValue(transition))) return false;
        if (incoming.external_arguments) |arguments| {
            if (!std.mem.eql(ir.ValueId, arguments, edge.arguments)) return false;
        } else {
            incoming.external_arguments = edge.arguments;
        }
        incoming.external_count += 1;
        return true;
    }

    const path_count = internalTransitionPathCount(program, analysis, loop, transition, source, edge) orelse return false;
    incoming.internal_count += path_count;
    return true;
}

fn internalTransitionPathCount(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    loop: structure.Loop,
    transition: ir.Instruction,
    source_id: ir.BlockId,
    edge: ir.Edge,
) ?usize {
    if (iteration_state.transitionStateMatches(program, transition, edge.arguments)) return 1;
    return forwardingTransitionPathCount(program, analysis, loop, transition, source_id, edge, edge.arguments, 0);
}

fn forwardingTransitionPathCount(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    loop: structure.Loop,
    transition: ir.Instruction,
    forwarding_id: ir.BlockId,
    expected_outgoing: ir.Edge,
    final_arguments: []const ir.ValueId,
    depth: usize,
) ?usize {
    if (depth >= program.blocks.len or forwarding_id.index() >= program.blocks.len or final_arguments.len != 4) return null;
    const forwarding = program.blocks[forwarding_id.index()];
    if (forwarding.id != forwarding_id or forwarding.instructions.len != 0 or forwarding.parameters.len < final_arguments.len) return null;
    const outgoing = switch (forwarding.terminator) {
        .jump => |value| value,
        else => return null,
    };
    if (!sameEdge(outgoing, expected_outgoing)) return null;

    var count: usize = 0;
    for (program.blocks) |predecessor| {
        if (predecessor.function != forwarding.function or !analysis.isReachable(predecessor.id)) continue;
        switch (predecessor.terminator) {
            .jump => |candidate| {
                const added = forwardingPredecessorPathCount(
                    program,
                    analysis,
                    loop,
                    transition,
                    forwarding,
                    predecessor.id,
                    candidate,
                    final_arguments,
                    depth,
                ) orelse return null;
                count = std.math.add(usize, count, added) catch return null;
            },
            .branch => |branch| {
                const then_added = forwardingPredecessorPathCount(
                    program,
                    analysis,
                    loop,
                    transition,
                    forwarding,
                    predecessor.id,
                    branch.then_edge,
                    final_arguments,
                    depth,
                ) orelse return null;
                count = std.math.add(usize, count, then_added) catch return null;
                const else_added = forwardingPredecessorPathCount(
                    program,
                    analysis,
                    loop,
                    transition,
                    forwarding,
                    predecessor.id,
                    branch.else_edge,
                    final_arguments,
                    depth,
                ) orelse return null;
                count = std.math.add(usize, count, else_added) catch return null;
            },
            else => {},
        }
    }
    return if (count == 0) null else count;
}

fn forwardingPredecessorPathCount(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    loop: structure.Loop,
    transition: ir.Instruction,
    forwarding: ir.Block,
    predecessor: ir.BlockId,
    incoming: ir.Edge,
    final_arguments: []const ir.ValueId,
    depth: usize,
) ?usize {
    if (incoming.target != forwarding.id) return 0;
    if (predecessor == forwarding.id or !regionContainsBlock(loop.body_region, predecessor) or
        incoming.arguments.len != forwarding.parameters.len)
    {
        return null;
    }
    var resolved: [4]ir.ValueId = undefined;
    for (final_arguments, 0..) |argument, index| {
        resolved[index] = if (parameterIndex(forwarding.parameters, argument)) |parameter_index|
            incoming.arguments[parameter_index]
        else
            argument;
    }
    if (iteration_state.transitionStateMatches(program, transition, &resolved)) return 1;
    return forwardingTransitionPathCount(
        program,
        analysis,
        loop,
        transition,
        predecessor,
        incoming,
        &resolved,
        depth + 1,
    );
}

fn externalInitialValue(transition: ir.Instruction) bool {
    return switch (transition.operation) {
        .numeric_for_next => |operation| operation.mode == .luau_numeric,
        .generic_for_next => true,
        else => true,
    };
}

fn parameterIndex(parameters: []const ir.ValueId, target: ir.ValueId) ?usize {
    for (parameters, 0..) |parameter, index| if (parameter == target) return index;
    return null;
}

fn matchNumeric(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    loop: structure.Loop,
    header: ir.Block,
    body: ir.Block,
    transition: ir.Instruction,
    operation: ir.NumericForNext,
    incoming: Incoming,
    uses: *const runtime_uses.Counts,
) ?Match {
    const initial_arguments = incoming.external_arguments orelse return null;
    if (initial_arguments.len != 4) return null;
    if (transition.results.len != 4 or body.parameters.len != 1 or loop.body_edge.arguments.len != 1) return null;
    if (operation.control != header.parameters[0] or operation.limit != header.parameters[1] or
        operation.step != header.parameters[2] or operation.initial != header.parameters[3])
    {
        return null;
    }
    if (loop.body_edge.arguments[0] != transition.results[3]) return null;
    const expected = [_]usize{ 1, incoming.internal_count, incoming.internal_count, incoming.internal_count + 1 };
    for (transition.results, expected, 0..) |result, count, index| {
        if (result.index() >= uses.values.len) return null;
        if (index == 1 or index == 2) {
            if (!numericNormalizedUsesAreCloneable(
                program,
                analysis,
                loop,
                header,
                result,
                uses.values[result.index()],
                count,
                initial_arguments[index],
            )) return null;
        } else if (uses.values[result.index()] != count) return null;
    }
    return .{ .numeric = .{
        .transition = transition,
        .operation = operation,
        .initial_arguments = initial_arguments,
        .body_parameter = body.parameters[0],
        .initial_flag_instruction = initialFlagInstruction(program, uses, incoming, externalInitialValue(transition)),
    } };
}

fn numericNormalizedUsesAreCloneable(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    loop: structure.Loop,
    header: ir.Block,
    result: ir.ValueId,
    total_uses: usize,
    expected_inside_uses: usize,
    initial_value: ir.ValueId,
) bool {
    if (total_uses == expected_inside_uses) return true;
    if (total_uses < expected_inside_uses or !valueIsStaticNumeric(program, initial_value)) return false;

    var inside_uses: usize = 0;
    for (analysis.function.blocks) |block_id| {
        if (!analysis.isReachable(block_id) or block_id.index() >= program.blocks.len) continue;
        if (block_id != header.id and !regionContainsBlock(loop.body_region, block_id)) continue;
        inside_uses = std.math.add(usize, inside_uses, blockValueUseCount(program, program.blocks[block_id.index()], result)) catch return false;
    }
    return inside_uses == expected_inside_uses;
}

pub fn valueIsStaticNumeric(program: *const ir.Program, value_id: ir.ValueId) bool {
    if (value_id.index() >= program.values.len) return false;
    const value = program.values[value_id.index()];
    return value.id == value_id and switch (value.type.kind) {
        .number => true,
        .integer => value.type.bit_width == 0,
        else => false,
    };
}

fn blockValueUseCount(program: *const ir.Program, block: ir.Block, target: ir.ValueId) usize {
    var count: usize = 0;
    const visitor = ValueUseCounter{ .target = target, .count = &count };
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) continue;
        runtime_uses.visitOperationUses(program.instructions[instruction_id.index()].operation, visitor);
    }
    runtime_uses.visitTerminatorUses(block.terminator, visitor);
    return count;
}

const ValueUseCounter = struct {
    target: ir.ValueId,
    count: *usize,

    pub fn value(self: ValueUseCounter, value_id: ir.ValueId) void {
        if (value_id == self.target and self.count.* != std.math.maxInt(usize)) self.count.* += 1;
    }

    pub fn pack(_: ValueUseCounter, _: ir.ValuePackId) void {}
    pub fn place(_: ValueUseCounter, _: ir.PlaceId) void {}
};

fn matchGeneric(
    program: *const ir.Program,
    loop: structure.Loop,
    header: ir.Block,
    body: ir.Block,
    transition: ir.Instruction,
    operation: ir.GenericForNext,
    incoming: Incoming,
    uses: *const runtime_uses.Counts,
) ?Match {
    const initial_arguments = incoming.external_arguments orelse return null;
    if (initial_arguments.len != 4) return null;
    const variable_count = @as(usize, operation.variable_count);
    if (variable_count == 0 or transition.results.len != variable_count + 3 or
        body.parameters.len != variable_count or loop.body_edge.arguments.len != variable_count)
    {
        return null;
    }
    if (operation.iterator != header.parameters[0] or operation.state != header.parameters[1] or
        operation.control != header.parameters[2] or operation.initial != header.parameters[3])
    {
        return null;
    }
    for (loop.body_edge.arguments, transition.results[3..]) |argument, result| {
        if (argument != result) return null;
    }
    for (transition.results, 0..) |result, index| {
        const expected: usize = if (index == 0)
            1
        else if (index == 1 or index == 2)
            incoming.internal_count
        else if (index == 3)
            incoming.internal_count + 1
        else
            1;
        if (result.index() >= uses.values.len or uses.values[result.index()] != expected) return null;
    }
    return .{ .generic = .{
        .transition = transition,
        .operation = operation,
        .initial_arguments = initial_arguments,
        .body_parameters = body.parameters,
        .initial_flag_instruction = initialFlagInstruction(program, uses, incoming, externalInitialValue(transition)),
    } };
}

fn markRecognized(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    region: *const structure.Region,
    recognized: []bool,
) !void {
    for (region.nodes) |node| switch (node) {
        .block, .loop_control, .loop_terminal => {},
        .branch => |branch| {
            if (try matchAcyclicBranch(allocator, program, branch)) |match| {
                const id = match.protocol.instructionId();
                if (id.index() < recognized.len) recognized[id.index()] = true;
            }
            try markRecognized(allocator, program, branch.then_region, recognized);
            try markRecognized(allocator, program, branch.else_region, recognized);
        },
        .loop => |loop| {
            if (try matchLoop(allocator, program, loop)) |match| {
                const id = match.instructionId();
                if (id.index() < recognized.len) recognized[id.index()] = true;
            }
            try markRecognized(allocator, program, loop.body_region, recognized);
        },
        .latch_loop => |loop| try markRecognized(allocator, program, loop.body_region, recognized),
        .infinite_loop => |loop| {
            try markRecognized(allocator, program, loop.body_region, recognized);
            if (loop.shared_side_exit) |side_exit| {
                for (side_exit.entries) |entry| try markRecognized(allocator, program, entry.region, recognized);
            }
        },
        .loop_boundary => |control| {
            try markRecognized(allocator, program, control.body_region, recognized);
            switch (control.boundary) {
                .side_exit => |exit| try markRecognized(allocator, program, exit.region, recognized),
                .side_escape => |escape| try markRecognized(allocator, program, escape.region, recognized),
                else => {},
            }
        },
    };
}

fn allExactUses(uses: *const runtime_uses.Counts, values: []const ir.ValueId, expected: usize) bool {
    for (values) |value| {
        if (value.index() >= uses.values.len or uses.values[value.index()] != expected) return false;
    }
    return true;
}

fn resultsHaveExactUses(uses: *const runtime_uses.Counts, values: []const ir.ValueId, expected: []const usize) bool {
    if (values.len != expected.len) return false;
    for (values, expected) |value, count| {
        if (value.index() >= uses.values.len or uses.values[value.index()] != count) return false;
    }
    return true;
}

fn initialFlagInstruction(
    program: *const ir.Program,
    uses: *const runtime_uses.Counts,
    incoming: Incoming,
    expected: bool,
) ?ir.InstructionId {
    const arguments = incoming.external_arguments orelse return null;
    if (arguments.len != 4) return null;
    const value_id = arguments[3];
    if (value_id.index() >= uses.values.len or uses.values[value_id.index()] != incoming.external_count or
        value_id.index() >= program.values.len)
    {
        return null;
    }
    const origin = switch (program.values[value_id.index()].origin) {
        .instruction_result => |value| value,
        else => return null,
    };
    if (origin.index != 0 or origin.instruction.index() >= program.instructions.len) return null;
    const instruction = program.instructions[origin.instruction.index()];
    if (instruction.id != origin.instruction or instruction.results.len != 1 or
        instruction.results[0] != value_id or instruction.pack_result != null or
        !std.meta.eql(instruction.effects, ir.EffectSummary.pure))
    {
        return null;
    }
    return switch (instruction.operation) {
        .constant => |literal| switch (literal) {
            .boolean => |value| if (value == expected) instruction.id else null,
            else => null,
        },
        else => null,
    };
}

fn isBooleanLiteral(program: *const ir.Program, value_id: ir.ValueId, expected: bool) bool {
    if (value_id.index() >= program.values.len) return false;
    const origin = switch (program.values[value_id.index()].origin) {
        .instruction_result => |value| value,
        else => return false,
    };
    if (origin.index != 0 or origin.instruction.index() >= program.instructions.len) return false;
    return switch (program.instructions[origin.instruction.index()].operation) {
        .constant => |literal| switch (literal) {
            .boolean => |value| value == expected,
            else => false,
        },
        else => false,
    };
}

fn regionContainsBlock(region: *const structure.Region, target: ir.BlockId) bool {
    for (region.nodes) |node| {
        if (node.blockId() == target) return true;
        const nested = switch (node) {
            .block, .loop_control, .loop_terminal => false,
            .branch => |branch| regionContainsBlock(branch.then_region, target) or regionContainsBlock(branch.else_region, target),
            .loop => |loop| regionContainsBlock(loop.body_region, target),
            .latch_loop => |loop| regionContainsBlock(loop.body_region, target),
            .infinite_loop => |loop| regionContainsBlock(loop.body_region, target) or
                (loop.shared_side_exit != null and containsAnySharedSideEntry(loop.shared_side_exit.?, target)),
            .loop_boundary => |control| regionContainsBlock(control.body_region, target) or switch (control.boundary) {
                .side_exit => |exit| regionContainsBlock(exit.region, target),
                .side_escape => |escape| regionContainsBlock(escape.region, target),
                else => false,
            },
        };
        if (nested) return true;
    }
    return false;
}

fn containsAnySharedSideEntry(side_exit: structure.SharedSideExit, target: ir.BlockId) bool {
    for (side_exit.entries) |entry| if (regionContainsBlock(entry.region, target)) return true;
    return false;
}

fn sameEdge(left: ir.Edge, right: ir.Edge) bool {
    return left.target == right.target and std.mem.eql(ir.ValueId, left.arguments, right.arguments);
}

const numeric_test_fixture = struct {
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_header = ir.BlockId.fromIndex(1);
    const b_body = ir.BlockId.fromIndex(2);
    const b_exit = ir.BlockId.fromIndex(3);
    const i_control = ir.InstructionId.fromIndex(0);
    const i_limit = ir.InstructionId.fromIndex(1);
    const i_step = ir.InstructionId.fromIndex(2);
    const i_true = ir.InstructionId.fromIndex(3);
    const i_false = ir.InstructionId.fromIndex(4);
    const i_next = ir.InstructionId.fromIndex(5);
    const i_leak = ir.InstructionId.fromIndex(6);
    const v_control = ir.ValueId.fromIndex(0);
    const v_limit = ir.ValueId.fromIndex(1);
    const v_step = ir.ValueId.fromIndex(2);
    const v_true = ir.ValueId.fromIndex(3);
    const v_false = ir.ValueId.fromIndex(4);
    const v_header_control = ir.ValueId.fromIndex(5);
    const v_header_limit = ir.ValueId.fromIndex(6);
    const v_header_step = ir.ValueId.fromIndex(7);
    const v_header_initial = ir.ValueId.fromIndex(8);
    const v_has = ir.ValueId.fromIndex(9);
    const v_normalized_limit = ir.ValueId.fromIndex(10);
    const v_normalized_step = ir.ValueId.fromIndex(11);
    const v_index = ir.ValueId.fromIndex(12);
    const v_body_index = ir.ValueId.fromIndex(13);

    const values = [_]ir.Value{
        .{ .id = v_control, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_control, .index = 0 } } },
        .{ .id = v_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_limit, .index = 0 } } },
        .{ .id = v_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_step, .index = 0 } } },
        .{ .id = v_true, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
        .{ .id = v_false, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_false, .index = 0 } } },
        .{ .id = v_header_control, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 0 } } },
        .{ .id = v_header_limit, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 1 } } },
        .{ .id = v_header_step, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 2 } } },
        .{ .id = v_header_initial, .function = f, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_header, .index = 3 } } },
        .{ .id = v_has, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 0 } } },
        .{ .id = v_normalized_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 1 } } },
        .{ .id = v_normalized_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 2 } } },
        .{ .id = v_index, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 3 } } },
        .{ .id = v_body_index, .function = f, .type = .number, .origin = .{ .block_parameter = .{ .block = b_body, .index = 0 } } },
    };

    const instructions = [_]ir.Instruction{
        .{ .id = i_control, .block = b_entry, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_control}, .effects = .pure },
        .{ .id = i_limit, .block = b_entry, .operation = .{ .constant = .{ .integer = "3" } }, .results = &.{v_limit}, .effects = .pure },
        .{ .id = i_step, .block = b_entry, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_step}, .effects = .pure },
        .{ .id = i_true, .block = b_entry, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure },
        .{ .id = i_false, .block = b_entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{v_false}, .effects = .pure },
        .{
            .id = i_next,
            .block = b_header,
            .operation = .{ .numeric_for_next = .{
                .control = v_header_control,
                .limit = v_header_limit,
                .step = v_header_step,
                .initial = v_header_initial,
            } },
            .results = &.{ v_has, v_normalized_limit, v_normalized_step, v_index },
            .effects = .numeric_for_next,
        },
    };

    const blocks = [_]ir.Block{
        .{
            .id = b_entry,
            .function = f,
            .instructions = &.{ i_control, i_limit, i_step, i_true, i_false },
            .terminator = .{ .jump = .{ .target = b_header, .arguments = &.{ v_control, v_limit, v_step, v_true } } },
        },
        .{
            .id = b_header,
            .function = f,
            .parameters = &.{ v_header_control, v_header_limit, v_header_step, v_header_initial },
            .instructions = &.{i_next},
            .terminator = .{ .branch = .{
                .condition = v_has,
                .then_edge = .{ .target = b_body, .arguments = &.{v_index} },
                .else_edge = .{ .target = b_exit },
            } },
        },
        .{
            .id = b_body,
            .function = f,
            .parameters = &.{v_body_index},
            .terminator = .{ .jump = .{ .target = b_header, .arguments = &.{ v_index, v_normalized_limit, v_normalized_step, v_false } } },
        },
        .{ .id = b_exit, .function = f, .terminator = .{ .return_values = &.{} } },
    };

    const functions = [_]ir.Function{.{
        .id = f,
        .blocks = &.{ b_entry, b_header, b_body, b_exit },
        .entry_block = b_entry,
    }};

    const program: ir.Program = .{
        .program_id = "numeric-iteration-protocol-test",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
};

fn firstLoop(plan: *const structure.Plan) ?structure.Loop {
    for (plan.root.nodes) |node| switch (node) {
        .loop => |loop| return loop,
        else => {},
    };
    return null;
}

fn firstBranch(plan: *const structure.Plan) ?structure.Branch {
    for (plan.root.nodes) |node| switch (node) {
        .branch => |branch| return branch,
        else => {},
    };
    return null;
}

test "numeric iteration protocol accepts canonical hidden state" {
    const fixture = numeric_test_fixture;
    var analysis = try cfg.Analysis.init(std.testing.allocator, &fixture.program, fixture.functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const loop = firstLoop(&plan) orelse return error.TestUnexpectedResult;
    const matched = (try matchLoop(std.testing.allocator, &fixture.program, loop)) orelse return error.TestUnexpectedResult;
    const numeric = switch (matched) {
        .numeric => |value| value,
        else => return error.TestUnexpectedResult,
    };
    try std.testing.expectEqualSlices(ir.ValueId, &.{ fixture.v_control, fixture.v_limit, fixture.v_step, fixture.v_true }, numeric.initial_arguments);
    try std.testing.expectEqual(fixture.v_body_index, numeric.body_parameter);
    try std.testing.expectEqual(fixture.i_true, numeric.initial_flag_instruction.?);
}

test "semantic normalized numeric iteration advances from canonical false state" {
    const fixture = numeric_test_fixture;
    var values = fixture.values;
    values[fixture.v_normalized_limit.index()].type = .dynamic;
    values[fixture.v_normalized_step.index()].type = .dynamic;
    values[fixture.v_index.index()].type = .dynamic;
    values[fixture.v_body_index.index()].type = .dynamic;

    var instructions = fixture.instructions;
    instructions[fixture.i_next.index()].operation.numeric_for_next.mode = .semantic_normalized;
    instructions[fixture.i_next.index()].effects = .dynamic_call;
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].terminator.jump.arguments = &.{
        fixture.v_control,
        fixture.v_limit,
        fixture.v_step,
        fixture.v_false,
    };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.blocks = &blocks;

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, fixture.functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const loop = firstLoop(&plan) orelse return error.TestUnexpectedResult;
    const matched = (try matchLoop(std.testing.allocator, &program, loop)) orelse return error.TestUnexpectedResult;
    const numeric = switch (matched) {
        .numeric => |value| value,
        else => return error.TestUnexpectedResult,
    };
    try std.testing.expectEqual(ir.NumericForMode.semantic_normalized, numeric.operation.mode);
    try std.testing.expect(numeric.initial_flag_instruction == null);
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    try std.testing.expect(report.isClean());

    blocks[fixture.b_entry.index()].terminator.jump.arguments = &.{
        fixture.v_control,
        fixture.v_limit,
        fixture.v_step,
        fixture.v_true,
    };
    var changed_analysis = try cfg.Analysis.init(std.testing.allocator, &program, fixture.functions[0]);
    defer changed_analysis.deinit();
    var changed_plan = try structure.Plan.init(std.testing.allocator, &changed_analysis);
    defer changed_plan.deinit();
    const changed_loop = firstLoop(&changed_plan) orelse return error.TestUnexpectedResult;
    try std.testing.expect((try matchLoop(std.testing.allocator, &program, changed_loop)) == null);
}

test "acyclic numeric iteration owns one transition and rejects hidden state" {
    const fixture = numeric_test_fixture;
    var blocks = fixture.blocks;
    blocks[fixture.b_body.index()].terminator = .{ .jump = .{ .target = fixture.b_exit } };
    var program = fixture.program;
    program.blocks = &blocks;

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, fixture.functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const branch = firstBranch(&plan) orelse return error.TestUnexpectedResult;
    const acyclic = (try matchAcyclicBranch(std.testing.allocator, &program, branch)) orelse return error.TestUnexpectedResult;
    const numeric = switch (acyclic.protocol) {
        .numeric => |value| value,
        else => return error.TestUnexpectedResult,
    };
    try std.testing.expectEqual(fixture.b_body, acyclic.body_edge.target);
    try std.testing.expectEqual(fixture.b_exit, acyclic.exit_edge.target);
    try std.testing.expectEqual(fixture.v_body_index, numeric.body_parameter);
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    try std.testing.expect(report.isClean());

    blocks[fixture.b_entry.index()].terminator.jump.arguments = &.{ fixture.v_control, fixture.v_limit, fixture.v_step, fixture.v_false };
    try std.testing.expect((try matchAcyclicBranch(std.testing.allocator, &program, branch)) == null);

    blocks[fixture.b_entry.index()] = fixture.blocks[fixture.b_entry.index()];
    var instructions: [fixture.instructions.len + 1]ir.Instruction = undefined;
    @memcpy(instructions[0..fixture.instructions.len], &fixture.instructions);
    instructions[fixture.i_leak.index()] = .{
        .id = fixture.i_leak,
        .block = fixture.b_body,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "leaked_normalized_limit",
            .value = fixture.v_normalized_limit,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
    };
    blocks[fixture.b_body.index()].instructions = &.{fixture.i_leak};
    program.instructions = &instructions;
    try std.testing.expect((try matchAcyclicBranch(std.testing.allocator, &program, branch)) == null);
}

test "numeric normalized state may escape only through static outside aliases" {
    const fixture = numeric_test_fixture;
    var blocks = fixture.blocks;
    blocks[fixture.b_exit.index()].terminator = .{ .return_values = &.{ fixture.v_normalized_limit, fixture.v_normalized_step } };
    var program = fixture.program;
    program.blocks = &blocks;

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, fixture.functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const loop = firstLoop(&plan) orelse return error.TestUnexpectedResult;
    try std.testing.expect((try matchLoop(std.testing.allocator, &program, loop)) != null);

    var dynamic_values = fixture.values;
    dynamic_values[fixture.v_limit.index()].type = .dynamic;
    program.values = &dynamic_values;
    try std.testing.expect((try matchLoop(std.testing.allocator, &program, loop)) == null);

    program.values = &fixture.values;
    blocks[fixture.b_exit.index()].terminator = .{ .return_values = &.{fixture.v_index} };
    try std.testing.expect((try matchLoop(std.testing.allocator, &program, loop)) == null);

    var instructions: [fixture.instructions.len + 1]ir.Instruction = undefined;
    @memcpy(instructions[0..fixture.instructions.len], &fixture.instructions);
    instructions[fixture.i_leak.index()] = .{
        .id = fixture.i_leak,
        .block = fixture.b_body,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "inside_limit",
            .value = fixture.v_normalized_limit,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
    };
    blocks = fixture.blocks;
    blocks[fixture.b_body.index()].instructions = &.{fixture.i_leak};
    blocks[fixture.b_exit.index()].terminator = .{ .return_values = &.{fixture.v_normalized_limit} };
    program.blocks = &blocks;
    program.instructions = &instructions;
    try std.testing.expect((try matchLoop(std.testing.allocator, &program, loop)) == null);
}

test "numeric iteration retains an initial flag with another runtime use" {
    const fixture = numeric_test_fixture;
    var instructions: [fixture.instructions.len + 1]ir.Instruction = undefined;
    @memcpy(instructions[0..fixture.instructions.len], &fixture.instructions);
    instructions[fixture.instructions.len] = .{
        .id = fixture.i_leak,
        .block = fixture.b_body,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "observed_initial_flag",
            .value = fixture.v_true,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
    };
    var blocks = fixture.blocks;
    blocks[fixture.b_body.index()].instructions = &.{fixture.i_leak};
    var program = fixture.program;
    program.instructions = &instructions;
    program.blocks = &blocks;

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, fixture.functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const loop = firstLoop(&plan) orelse return error.TestUnexpectedResult;
    const matched = (try matchLoop(std.testing.allocator, &program, loop)) orelse return error.TestUnexpectedResult;
    const numeric = switch (matched) {
        .numeric => |value| value,
        else => return error.TestUnexpectedResult,
    };
    try std.testing.expect(numeric.initial_flag_instruction == null);
}

test "numeric iteration protocol accepts only identical converged external state" {
    const fixture = numeric_test_fixture;
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].terminator = .{ .branch = .{
        .condition = fixture.v_true,
        .then_edge = .{ .target = fixture.b_header, .arguments = &.{ fixture.v_control, fixture.v_limit, fixture.v_step, fixture.v_true } },
        .else_edge = .{ .target = fixture.b_header, .arguments = &.{ fixture.v_control, fixture.v_limit, fixture.v_step, fixture.v_true } },
    } };
    var program = fixture.program;
    program.blocks = &blocks;

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, fixture.functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const loop = firstLoop(&plan) orelse return error.TestUnexpectedResult;
    try std.testing.expect((try matchLoop(std.testing.allocator, &program, loop)) != null);

    blocks[fixture.b_entry.index()].terminator.branch.else_edge.arguments = &.{ fixture.v_limit, fixture.v_limit, fixture.v_step, fixture.v_true };
    var divergent_analysis = try cfg.Analysis.init(std.testing.allocator, &program, fixture.functions[0]);
    defer divergent_analysis.deinit();
    var divergent_plan = try structure.Plan.init(std.testing.allocator, &divergent_analysis);
    defer divergent_plan.deinit();
    const divergent_loop = firstLoop(&divergent_plan) orelse return error.TestUnexpectedResult;
    try std.testing.expect((try matchLoop(std.testing.allocator, &program, divergent_loop)) == null);
}

test "numeric iteration protocol composes multiple forwarding latches" {
    const fixture = numeric_test_fixture;
    const first_forwarding = ir.BlockId.fromIndex(fixture.blocks.len);
    const second_forwarding = ir.BlockId.fromIndex(fixture.blocks.len + 1);
    const first_control = ir.ValueId.fromIndex(fixture.values.len);
    const first_limit = ir.ValueId.fromIndex(fixture.values.len + 1);
    const first_step = ir.ValueId.fromIndex(fixture.values.len + 2);
    const first_initial = ir.ValueId.fromIndex(fixture.values.len + 3);
    const first_extra = ir.ValueId.fromIndex(fixture.values.len + 4);
    const second_limit = ir.ValueId.fromIndex(fixture.values.len + 5);
    const second_control = ir.ValueId.fromIndex(fixture.values.len + 6);
    const second_step = ir.ValueId.fromIndex(fixture.values.len + 7);
    const second_initial = ir.ValueId.fromIndex(fixture.values.len + 8);
    const values = fixture.values ++ [_]ir.Value{
        .{ .id = first_control, .function = fixture.f, .type = .number, .origin = .{ .block_parameter = .{ .block = first_forwarding, .index = 0 } } },
        .{ .id = first_limit, .function = fixture.f, .type = .number, .origin = .{ .block_parameter = .{ .block = first_forwarding, .index = 1 } } },
        .{ .id = first_step, .function = fixture.f, .type = .number, .origin = .{ .block_parameter = .{ .block = first_forwarding, .index = 2 } } },
        .{ .id = first_initial, .function = fixture.f, .type = .boolean, .origin = .{ .block_parameter = .{ .block = first_forwarding, .index = 3 } } },
        .{ .id = first_extra, .function = fixture.f, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = first_forwarding, .index = 4 } } },
        .{ .id = second_limit, .function = fixture.f, .type = .number, .origin = .{ .block_parameter = .{ .block = second_forwarding, .index = 0 } } },
        .{ .id = second_control, .function = fixture.f, .type = .number, .origin = .{ .block_parameter = .{ .block = second_forwarding, .index = 1 } } },
        .{ .id = second_step, .function = fixture.f, .type = .number, .origin = .{ .block_parameter = .{ .block = second_forwarding, .index = 2 } } },
        .{ .id = second_initial, .function = fixture.f, .type = .boolean, .origin = .{ .block_parameter = .{ .block = second_forwarding, .index = 3 } } },
    };
    var blocks = fixture.blocks ++ [_]ir.Block{
        .{
            .id = first_forwarding,
            .function = fixture.f,
            .parameters = &.{ first_control, first_limit, first_step, first_initial, first_extra },
            .terminator = .{ .jump = .{
                .target = second_forwarding,
                .arguments = &.{ first_limit, first_control, first_step, first_initial },
            } },
        },
        .{
            .id = second_forwarding,
            .function = fixture.f,
            .parameters = &.{ second_limit, second_control, second_step, second_initial },
            .terminator = .{ .jump = .{
                .target = fixture.b_header,
                .arguments = &.{ second_control, second_limit, second_step, second_initial },
            } },
        },
    };
    blocks[fixture.b_body.index()].terminator = .{ .jump = .{
        .target = first_forwarding,
        .arguments = &.{ fixture.v_index, fixture.v_normalized_limit, fixture.v_normalized_step, fixture.v_false, fixture.v_true },
    } };
    var functions = fixture.functions;
    functions[0].blocks = &.{ fixture.b_entry, fixture.b_header, fixture.b_body, first_forwarding, second_forwarding, fixture.b_exit };
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.values = &values;

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const loop = firstLoop(&plan) orelse return error.TestUnexpectedResult;
    try std.testing.expect((try matchLoop(std.testing.allocator, &program, loop)) != null);

    blocks[second_forwarding.index()].terminator.jump.arguments = &.{ second_limit, second_control, second_step, second_initial };
    var changed_analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer changed_analysis.deinit();
    var changed_plan = try structure.Plan.init(std.testing.allocator, &changed_analysis);
    defer changed_plan.deinit();
    const changed_loop = firstLoop(&changed_plan) orelse return error.TestUnexpectedResult;
    try std.testing.expect((try matchLoop(std.testing.allocator, &program, changed_loop)) == null);
}

test "numeric iteration protocol rejects observable hidden state" {
    const fixture = numeric_test_fixture;
    var instructions: [fixture.instructions.len + 1]ir.Instruction = undefined;
    @memcpy(instructions[0..fixture.instructions.len], &fixture.instructions);
    instructions[fixture.instructions.len] = .{
        .id = fixture.i_leak,
        .block = fixture.b_body,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "leaked_limit",
            .value = fixture.v_normalized_limit,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
    };
    var blocks = fixture.blocks;
    blocks[fixture.b_body.index()].instructions = &.{fixture.i_leak};
    var program = fixture.program;
    program.instructions = &instructions;
    program.blocks = &blocks;

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, fixture.functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const loop = firstLoop(&plan) orelse return error.TestUnexpectedResult;
    try std.testing.expect((try matchLoop(std.testing.allocator, &program, loop)) == null);
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    try std.testing.expect(report.contains(.unsupported_readable_iteration_protocol));
}

test "acyclic iteration whose body always returns is recognized without an enclosing stop" {
    // The body returns, so neither arm reaches a join and the header branch is
    // planned with `join = null` at the root. The acyclic matcher still recognizes the transition (the body arm is
    // the edge that carries the loop variable; the exit arm is emitted after the loop), and admission is clean.
    const fixture = numeric_test_fixture;
    var blocks = fixture.blocks;
    blocks[fixture.b_body.index()].terminator = .{ .return_values = &.{fixture.v_body_index} };
    var program = fixture.program;
    program.blocks = &blocks;

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, fixture.functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const branch = firstBranch(&plan) orelse return error.TestUnexpectedResult;
    try std.testing.expect(branch.join == null);
    const acyclic = (try matchAcyclicBranch(std.testing.allocator, &program, branch)) orelse return error.TestUnexpectedResult;
    const numeric = switch (acyclic.protocol) {
        .numeric => |value| value,
        else => return error.TestUnexpectedResult,
    };
    try std.testing.expectEqual(fixture.b_body, acyclic.body_edge.target);
    try std.testing.expectEqual(fixture.b_exit, acyclic.exit_edge.target);
    try std.testing.expectEqual(fixture.v_body_index, numeric.body_parameter);
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    try std.testing.expect(report.isClean());
}
