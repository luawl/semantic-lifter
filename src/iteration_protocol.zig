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

/// A native iteration header planned as a loop boundary whose boundary arm is the iteration body
/// (a loop boundary inside a loop body): the body edge is the header's then edge, the exit edge its else edge.
pub const AcyclicBoundary = struct {
    protocol: Match,
    body_edge: ir.Edge,
    exit_edge: ir.Edge,
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
    var exit_region = shape.exit_region;
    if (shape.exit_region) |region| {
        var reaches_exit = try analysis.canReach(shape.body_edge.target, shape.exit_edge.target);
        if (shape.body_region.stop) |stop| reaches_exit = reaches_exit or try analysis.canReach(shape.body_edge.target, stop);
        if (reaches_exit) {
            // Form A of an always-breaking body: the exit arm goes straight to the stop the body also ends at (the bytecode's
            // loop exit is the enclosing `if` join). That stop is the loop's exit, as a join would be: join form.
            if (!exitArmIsStop(branch_plan, shape, region)) return null;
            exit_region = null;
        } else if (shape.enclosed) return null; // the join-less form stays outside loop bodies
    }
    if (shape.enclosed or (shape.exit_region != null and exit_region == null)) {
        // Forms A and B: until it reaches the loop's exit block, the body stays in its region (no back edge to the
        // header; no `break`, `continue` or escape of an enclosing construct, which would bind to the native `for`).
        if (!try bodyStaysInRegion(allocator, &analysis, shape.body_region, shape.body_edge.target, shape.exit_edge.target)) return null;
        // A nested escape to the loop's exit block is written by the body region's own
        // `repeat ... until true` wrapper, which declares and consumes its flag inside the `for`. What a native `for`
        // cannot carry is a `continue` (or an enclosing loop's `break`), which would bind to it, so only a body whose
        // nested transfer the writer would write that way stays refused.
        if (try bodyHasUnwrittenTransfer(allocator, program, shape.body_region, shape.exit_edge.target)) return null;
    } else if (try analysis.canReach(shape.body_edge.target, header.id)) return null;

    const identity = try allocator.alloc(ir.ValueId, program.values.len);
    defer allocator.free(identity);
    for (identity, 0..) |*value, index| value.* = ir.ValueId.fromIndex(index);
    const excluded = try allocator.alloc(bool, program.instructions.len);
    defer allocator.free(excluded);
    @memset(excluded, false);
    var uses = try runtime_uses.Counts.init(allocator, program, identity, excluded);
    defer uses.deinit();

    const entry_test: AcyclicEntryTest = if (shape.enclosed) .{ .reachability_avoiding = shape.exit_edge.target } else .reachability;
    const incoming = (try inspectAcyclicIncomingEdges(program, &analysis, header, transition, &uses, entry_test)) orelse return null;
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
        .exit_region = exit_region,
    };
}

/// Inside an enclosing loop body the planner places a header whose body always returns at
/// a loop boundary, with the body arm (the enclosing loop's continuation) on the else edge and the iteration body as
/// the boundary arm on the then edge, the one with the loop bindings. That body is a terminal block or a side-exit
/// region that never comes back to the header, the exit arm or the region's stop, so `for ... do <body> end`
/// followed by the exit arm is the source's own control flow.
pub fn matchAcyclicLoopBoundary(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    control: structure.LoopBoundaryControl,
) !?AcyclicBoundary {
    if (control.body_on_true or control.block.index() >= program.blocks.len) return null;
    const header = program.blocks[control.block.index()];
    const branch = switch (header.terminator) {
        .branch => |value| value,
        else => return null,
    };
    if (!sameEdge(control.body_edge, branch.else_edge)) return null;
    const transition = transitionForHeader(program, header) orelse return null;
    switch (transition.operation) {
        // That mode is exempt from the admission check and keeps its `if` form.
        .numeric_for_next => |operation| if (operation.mode == .semantic_normalized) return null,
        .generic_for_next => {},
        else => return null,
    }
    const body_edge = branch.then_edge;
    var side_region: ?*const structure.Region = null;
    switch (control.boundary) {
        .terminal => |terminal| if (!sameEdge(terminal.edge, body_edge) or terminal.block != body_edge.target) return null,
        .side_exit => |side_exit| {
            const region = side_exit.region;
            if (!sameEdge(side_exit.entry_edge, body_edge) or
                region.nodes.len == 0 or region.nodes[0].blockId() != body_edge.target or
                region.loop_exit != null or region.continue_target != null or
                region.terminal_projection != null or region.continue_projection != null or
                region.escape_projection != null or region.stop_forwarding != null)
            {
                return null;
            }
            const free_targets = try structure.regionFreeTargetsAlloc(allocator, region);
            defer allocator.free(free_targets);
            if (free_targets.len != 0) return null;
            side_region = region;
        },
        else => return null,
    }
    if (header.function.index() >= program.functions.len) return null;
    const function = program.functions[header.function.index()];
    if (function.id != header.function) return null;

    var analysis = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
        error.InvalidCfg => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    if (try analysis.canReach(body_edge.target, header.id)) return null;
    if (try analysis.canReach(body_edge.target, branch.else_edge.target)) return null;
    if (side_region) |region| {
        if (region.stop) |stop| {
            if (try analysis.canReach(body_edge.target, stop)) return null;
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

    const incoming = (try inspectAcyclicIncomingEdges(program, &analysis, header, transition, &uses, .dominance)) orelse return null;
    const body = program.blocks[body_edge.target.index()];
    const protocol: Match = switch (transition.operation) {
        .numeric_for_next => |operation| matchAcyclicNumeric(
            program,
            header,
            body,
            transition,
            operation,
            body_edge,
            incoming,
            &uses,
        ) orelse return null,
        .generic_for_next => |operation| matchAcyclicGeneric(
            program,
            header,
            body,
            transition,
            operation,
            body_edge,
            incoming,
            &uses,
        ) orelse return null,
        else => return null,
    };
    return .{ .protocol = protocol, .body_edge = body_edge, .exit_edge = branch.else_edge };
}

const AcyclicShape = struct {
    body_region: *const structure.Region,
    body_edge: ir.Edge,
    exit_edge: ir.Edge,
    exit_region: ?*const structure.Region = null,
    /// The arm regions carry an enclosing loop's `loop_exit` or `continue_target`.
    enclosed: bool = false,
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
            .enclosed = body_region.loop_exit != null or body_region.continue_target != null,
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
        body_region.terminal_projection != null or body_region.continue_projection != null or
        body_region.stop_forwarding != null or body_region.nodes[0].blockId() != body_edge.target)
    {
        return null;
    }
    return .{
        .body_region = body_region,
        .body_edge = body_edge,
        .exit_edge = exit_edge,
        .enclosed = body_region.loop_exit != null or body_region.continue_target != null,
    };
}

fn directJoinRegion(region: *const structure.Region, edge: ir.Edge, join: ir.BlockId) bool {
    // An inherited `loop_exit` or `continue_target` is inert here: the region is empty and the join form never
    // emits it.
    return edge.target == join and region.nodes.len == 0 and region.stop == join and
        region.terminal_projection == null and region.continue_projection == null and
        region.stop_forwarding == null;
}

/// Form A of an always-breaking body: the exit arm of a header planned without a join is empty and goes straight to the
/// stop that the body region also ends at, so that stop is the loop's exit block.
fn exitArmIsStop(plan: structure.Branch, shape: AcyclicShape, region: *const structure.Region) bool {
    const stop = region.stop orelse return false;
    const body_stop = shape.body_region.stop orelse return false;
    return stop == body_stop and stop == shape.exit_edge.target and region.nodes.len == 0 and
        plan.else_edge_override == null and plan.else_shared_reentry == null and
        region.terminal_projection == null and region.continue_projection == null and
        region.escape_projection == null and region.stop_forwarding == null;
}

/// Every block the body reaches before the loop's exit block lies in the body region. The
/// header is never in that region, so a back edge fails the walk. A function-terminating block
/// the region writes inline (`regionHoldsTerminalBlock`: a `.terminal` boundary's block, a `.loop_terminal`'s terminal
/// block) counts as inside; it has no successor, so the walk gains no path, and a body that may also return is admitted.
fn bodyStaysInRegion(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    region: *const structure.Region,
    start: ir.BlockId,
    exit: ir.BlockId,
) std.mem.Allocator.Error!bool {
    const visited = try allocator.alloc(bool, analysis.program.blocks.len);
    defer allocator.free(visited);
    @memset(visited, false);
    var pending: std.ArrayList(ir.BlockId) = .empty;
    defer pending.deinit(allocator);
    try pending.append(allocator, start);
    while (pending.pop()) |block_id| {
        if (block_id == exit) continue;
        if (block_id.index() >= visited.len) return false;
        if (visited[block_id.index()]) continue;
        visited[block_id.index()] = true;
        if (!regionContainsBlock(region, block_id) and !regionHoldsTerminalBlock(region, block_id)) return false;
        for (0..analysis.successorCount(block_id)) |successor_index| {
            try pending.append(allocator, analysis.successorAt(block_id, successor_index) orelse return false);
        }
    }
    return true;
}

/// A function-terminating block the region writes inline: the boundary block of a `.terminal`
/// loop boundary (emitOwnedTerminalArm) or the terminal block of a `.loop_terminal` node, at any depth.
fn regionHoldsTerminalBlock(region: *const structure.Region, target: ir.BlockId) bool {
    for (region.nodes) |node| {
        const held = switch (node) {
            .block, .loop_control => false,
            .loop_terminal => |control| control.terminal_block == target,
            .branch => |branch| regionHoldsTerminalBlock(branch.then_region, target) or
                regionHoldsTerminalBlock(branch.else_region, target),
            .loop => |loop| regionHoldsTerminalBlock(loop.body_region, target),
            .latch_loop => |loop| regionHoldsTerminalBlock(loop.body_region, target),
            .infinite_loop => |loop| regionHoldsTerminalBlock(loop.body_region, target),
            .loop_boundary => |control| regionHoldsTerminalBlock(control.body_region, target) or switch (control.boundary) {
                .terminal => |terminal| terminal.block == target,
                else => false,
            },
        };
        if (held) return true;
    }
    return false;
}

/// Inside an enclosed body a nested escape (to the loop's exit block X or to an inner join) is
/// written by the escaping region's own `repeat ... until true` wrapper and re-raised after each wrapper up to the
/// region whose stop is the target (emitRegionWithPredeclaredBlock, emitRegionEscapePropagation); for X that region is
/// the body region, so its flag is declared and consumed inside the `for`. What the writer cannot carry inside a
/// native `for` is a `continue`.
fn bodyHasUnwrittenTransfer(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    body: *const structure.Region,
    exit: ir.BlockId,
) std.mem.Allocator.Error!bool {
    // Without a loop exit the writer sets an escape flag but writes no `break` after it (emitRegionWithPredeclaredBlock,
    // emitRegionBodyWithPredeclaredBlock): the nested-transfer rule stays (form A at an `if`-arm tail or in a side-exit region).
    if (body.loop_exit == null) return bodyHasNestedTransfer(program, body, exit);
    // The writer's precondition: nothing has to be propagated past the `for` (implied by bodyStaysInRegion).
    const free_targets = try structure.regionFreeTargetsAlloc(allocator, body);
    defer allocator.free(free_targets);
    if (free_targets.len != 0) return true;
    return regionWritesContinue(program, body, exit);
}

/// Whether the region writer would write, in this region or below it, a `continue` (or an
/// enclosing loop's `break`), which inside a native `for` would bind to the `for`. The edge-override test of the nested-transfer walk is
/// not repeated: an override replaces the effective edge and writes no transfer (emit_luau_branch_stmt.zig; known
/// by code reading, not modelled here).
fn regionWritesContinue(program: *const ir.Program, region: *const structure.Region, exit: ir.BlockId) bool {
    if (region.continue_projection != null) return true; // a `continue` statement or flag
    if (region.stop) |stop| {
        // Consumed as `if <flag> then continue end` after the region's wrapper (emitRegionEscapePropagation): a
        // loop-boundary body that also breaks from a nested branch, or a nested break whose exit edges are forwarded to the
        // enclosing loop header.
        if (region.continue_target != null and region.continue_target.? == stop and
            structure.regionHasNestedEscapeTo(region, stop)) return true;
    }
    for (region.nodes) |node| switch (node) {
        .block, .loop_terminal => {}, // a .loop_terminal falls through to the region stop (emitLoopTerminalControl)
        .loop_control => return true, // writes the enclosing loop's exit as a `break` (confinement excludes it already)
        .branch => |branch| if (regionWritesContinue(program, branch.then_region, exit) or
            regionWritesContinue(program, branch.else_region, exit)) return true,
        .loop, .latch_loop, .infinite_loop => if (walk.node(program, node, exit)) return true, // the strict nested-transfer walk
        .loop_boundary => |control| {
            // Only a `.terminal` boundary whose body stops at this region's stop (`.parent_stop`, no `continue`:
            // transparent_stop.zig, emitLoopBoundaryBodyImpl).
            if (control.boundary != .terminal) return true;
            const stop = region.stop orelse return true;
            if (control.body_region.stop == null or control.body_region.stop.? != stop) return true;
            if (regionWritesContinue(program, control.body_region, exit)) return true;
        },
    };
    return false;
}

/// A branch nested below the body region that joins or escapes to the
/// loop's exit block is written as an escape flag. `bodyHasUnwrittenTransfer` keeps this rule
/// for a body without an inherited `loop_exit`, where the writer sets that flag but writes no `break` after it. A
/// nested region counts when it carries an escape or continue projection, or holds a `.branch` whose join is the exit
/// block or whose branch edge (or its edge override) targets it. The body region's own top-level branches count only
/// through their arm regions: a top-level branch joining at the exit block is the body's ordinary shape.
fn bodyHasNestedTransfer(program: *const ir.Program, region: *const structure.Region, exit: ir.BlockId) bool {
    if (structure.regionHasNestedEscapeTo(region, exit)) return true;
    for (region.nodes) |value| {
        if (walk.node(program, value, exit)) return true;
    }
    return false;
}

/// The nested-transfer walk of `bodyHasNestedTransfer`, hoisted to file scope so that
/// `regionWritesContinue` keeps it for nested real loops.
const walk = struct {
    /// The regions one node holds, each checked as a nested region.
    fn node(source: *const ir.Program, value: structure.Node, target: ir.BlockId) bool {
        return switch (value) {
            .block, .loop_control, .loop_terminal => false,
            .branch => |branch| nested(source, branch.then_region, target) or nested(source, branch.else_region, target),
            .loop => |loop| nested(source, loop.body_region, target),
            .latch_loop => |loop| nested(source, loop.body_region, target),
            .infinite_loop => |loop| infinite: {
                if (nested(source, loop.body_region, target)) break :infinite true;
                const side_exit = loop.shared_side_exit orelse break :infinite false;
                for (side_exit.entries) |entry| {
                    if (nested(source, entry.region, target)) break :infinite true;
                }
                break :infinite false;
            },
            .loop_boundary => |control| nested(source, control.body_region, target) or switch (control.boundary) {
                .side_exit => |side| nested(source, side.region, target),
                .side_escape => |side| nested(source, side.region, target),
                else => false,
            },
        };
    }

    fn nested(source: *const ir.Program, nested_region: *const structure.Region, target: ir.BlockId) bool {
        if (nested_region.escape_projection != null or nested_region.continue_projection != null) return true;
        for (nested_region.nodes) |value| {
            switch (value) {
                .branch => |branch| {
                    if (branch.join != null and branch.join.? == target) return true;
                    if (branch.then_edge_override) |override| {
                        if (override.edge().target == target) return true;
                    }
                    if (branch.else_edge_override) |override| {
                        if (override.edge().target == target) return true;
                    }
                    if (branch.block.index() < source.blocks.len) {
                        switch (source.blocks[branch.block.index()].terminator) {
                            .branch => |edges| if (edges.then_edge.target == target or edges.else_edge.target == target) return true,
                            else => {},
                        }
                    }
                },
                else => {},
            }
            if (node(source, value, target)) return true;
        }
        return false;
    }
};

/// Which entry edges into an acyclic header count as edges that continue the iteration.
/// `matchAcyclicBranch` keeps the reachability test; `matchAcyclicLoopBoundary` takes the dominance test.
/// For an enclosed `.branch` header (form B, and form A inside a loop body) `matchAcyclicBranch`
/// passes `.reachability_avoiding` with the loop's exit block instead.
const AcyclicEntryTest = union(enum) { reachability, dominance, reachability_avoiding: ir.BlockId };

fn inspectAcyclicIncomingEdges(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    header: ir.Block,
    transition: ir.Instruction,
    uses: *const runtime_uses.Counts,
    entry_test: AcyclicEntryTest,
) std.mem.Allocator.Error!?Incoming {
    if (!allExactUses(uses, header.parameters, 1)) return null;
    var incoming: Incoming = .{};
    for (program.blocks) |source| {
        if (source.function != header.function or !analysis.isReachable(source.id)) continue;
        switch (source.terminator) {
            .jump => |edge| if (!try inspectAcyclicIncomingEdge(program, analysis, header, transition, source.id, edge, entry_test, &incoming)) return null,
            .branch => |branch| {
                if (!try inspectAcyclicIncomingEdge(program, analysis, header, transition, source.id, branch.then_edge, entry_test, &incoming)) return null;
                if (!try inspectAcyclicIncomingEdge(program, analysis, header, transition, source.id, branch.else_edge, entry_test, &incoming)) return null;
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
    entry_test: AcyclicEntryTest,
    incoming: *Incoming,
) std.mem.Allocator.Error!bool {
    if (edge.target != header.id) return true;
    // `.reachability` (`matchAcyclicBranch`): an entry whose source the header can reach is taken for a back edge, so
    // a `.branch` header that reaches its own preheader through an enclosing loop stays refused. `.dominance`
    // (`matchAcyclicLoopBoundary`): only a back edge into the header (a source the header dominates) continues the
    // iteration; an entry that the header reaches only through an enclosing loop re-enters the `for` statement from
    // the top. Both matchers refuse a body that reaches the header, and `matchLoop`'s `inspectIncomingEdge` makes the
    // same split by body-region membership. `.reachability_avoiding` (an enclosed `.branch` header): the header is
    // entered again only on the enclosing loop's next trip, through the loop's exit block, so a source the header
    // reaches only through that block starts the `for` statement again, where the initial-literal and same-arguments
    // checks still apply; `canReachAvoiding` is false when its target is the avoided block, so an entry from the exit
    // block itself is refused by name.
    if (edge.arguments.len != 4 or !isBooleanLiteral(program, edge.arguments[3], externalInitialValue(transition)) or
        switch (entry_test) {
            .reachability => try analysis.canReach(header.id, source),
            .dominance => analysis.dominates(header.id, source),
            .reachability_avoiding => |exit| source == exit or try analysis.canReachAvoiding(header.id, source, exit),
        })
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
    return forwardingTransitionPathCount(program, analysis, loop, transition, source_id, edge, edge.arguments, 0, null);
}

/// Marks in `forwarders` (one flag per block) each pure forwarding block the match of `loop` walks on the header's
/// re-entry path: a block of the loop body with no instructions and a jump toward the header that passes the
/// transition state on through its parameters (`forwardingTransitionPathCount`). Call it only for a loop the match
/// accepted, so that the walk succeeds on every internal edge into the header. A block whose edge into the header
/// carries the transition state itself, such as a join that only feeds a branch expression, is no forwarder, and
/// a forwarder on the entry path is no internal edge's source.
pub fn markReentryForwarders(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    loop: structure.Loop,
    transition: ir.Instruction,
    forwarders: []bool,
) void {
    if (loop.header.index() >= program.blocks.len) return;
    const header = program.blocks[loop.header.index()];
    for (program.blocks) |source| {
        if (source.function != header.function or !analysis.isReachable(source.id)) continue;
        if (!regionContainsBlock(loop.body_region, source.id)) continue;
        switch (source.terminator) {
            .jump => |edge| markForwardersOnEdge(program, analysis, loop, transition, source.id, edge, forwarders),
            .branch => |branch| {
                markForwardersOnEdge(program, analysis, loop, transition, source.id, branch.then_edge, forwarders);
                markForwardersOnEdge(program, analysis, loop, transition, source.id, branch.else_edge, forwarders);
            },
            else => {},
        }
    }
}

fn markForwardersOnEdge(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    loop: structure.Loop,
    transition: ir.Instruction,
    source: ir.BlockId,
    edge: ir.Edge,
    forwarders: []bool,
) void {
    if (edge.target != loop.header or edge.arguments.len != 4) return;
    if (iteration_state.transitionStateMatches(program, transition, edge.arguments)) return;
    _ = forwardingTransitionPathCount(program, analysis, loop, transition, source, edge, edge.arguments, 0, forwarders);
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
    forwarders: ?[]bool,
) ?usize {
    if (depth >= program.blocks.len or forwarding_id.index() >= program.blocks.len or final_arguments.len != 4) return null;
    const forwarding = program.blocks[forwarding_id.index()];
    if (forwarding.id != forwarding_id or forwarding.instructions.len != 0 or forwarding.parameters.len < final_arguments.len) return null;
    const outgoing = switch (forwarding.terminator) {
        .jump => |value| value,
        else => return null,
    };
    if (!sameEdge(outgoing, expected_outgoing)) return null;
    if (forwarders) |marks| {
        if (forwarding_id.index() < marks.len) marks[forwarding_id.index()] = true;
    }

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
                    forwarders,
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
                    forwarders,
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
                    forwarders,
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
    forwarders: ?[]bool,
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
        forwarders,
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
            if (try matchAcyclicLoopBoundary(allocator, program, control)) |match| {
                const id = match.protocol.instructionId();
                if (id.index() < recognized.len) recognized[id.index()] = true;
            }
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

test "a numeric loop marks exactly the forwarding blocks its match walks on the re-entry path" {
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

    // The body reaches the header through two forwarding blocks, the first with a parameter it does not pass on: the
    // match walks both, and only those two are marked.
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const loop = firstLoop(&plan) orelse return error.TestUnexpectedResult;
    const matched = (try matchLoop(std.testing.allocator, &program, loop)) orelse return error.TestUnexpectedResult;
    var marks = [_]bool{false} ** 6;
    markReentryForwarders(&program, &analysis, loop, matched.numeric.transition, &marks);
    try std.testing.expectEqualSlices(bool, &.{ false, false, false, false, true, true }, &marks);

    // The canonical loop's body enters the header with the transition state itself: no block is a forwarder.
    var canonical_analysis = try cfg.Analysis.init(std.testing.allocator, &fixture.program, fixture.functions[0]);
    defer canonical_analysis.deinit();
    var canonical_plan = try structure.Plan.init(std.testing.allocator, &canonical_analysis);
    defer canonical_plan.deinit();
    const canonical_loop = firstLoop(&canonical_plan) orelse return error.TestUnexpectedResult;
    const canonical = (try matchLoop(std.testing.allocator, &fixture.program, canonical_loop)) orelse return error.TestUnexpectedResult;
    var canonical_marks = [_]bool{false} ** 4;
    markReentryForwarders(&fixture.program, &canonical_analysis, canonical_loop, canonical.numeric.transition, &canonical_marks);
    try std.testing.expectEqualSlices(bool, &.{ false, false, false, false }, &canonical_marks);
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

test "acyclic iteration planned as a loop boundary inside an enclosing loop is recognized when its body always returns" {
    // A numeric loop whose body always returns, inside a `while` body (a shape the source frontend produces).
    // The planner places its header at a `.loop_boundary` of the enclosing loop body whose boundary arm (the then
    // edge, which carries the loop variable) is the returning body; readable admission recognizes the transition
    // there. The header reaches its own preheader only around the enclosing loop, never through a back edge.
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_while = ir.BlockId.fromIndex(1);
    const b_pre = ir.BlockId.fromIndex(2);
    const b_header = ir.BlockId.fromIndex(3);
    const b_body = ir.BlockId.fromIndex(4);
    const b_next = ir.BlockId.fromIndex(5);
    const b_done = ir.BlockId.fromIndex(6);
    const i_cond = ir.InstructionId.fromIndex(0);
    const i_control = ir.InstructionId.fromIndex(1);
    const i_limit = ir.InstructionId.fromIndex(2);
    const i_step = ir.InstructionId.fromIndex(3);
    const i_true = ir.InstructionId.fromIndex(4);
    const i_false = ir.InstructionId.fromIndex(5);
    const i_next = ir.InstructionId.fromIndex(6);
    const v_left = ir.ValueId.fromIndex(0);
    const v_right = ir.ValueId.fromIndex(1);
    const v_cond = ir.ValueId.fromIndex(2);
    const v_control = ir.ValueId.fromIndex(3);
    const v_limit = ir.ValueId.fromIndex(4);
    const v_step = ir.ValueId.fromIndex(5);
    const v_true = ir.ValueId.fromIndex(6);
    const v_false = ir.ValueId.fromIndex(7);
    const v_header_control = ir.ValueId.fromIndex(8);
    const v_header_limit = ir.ValueId.fromIndex(9);
    const v_header_step = ir.ValueId.fromIndex(10);
    const v_header_initial = ir.ValueId.fromIndex(11);
    const v_has = ir.ValueId.fromIndex(12);
    const v_normalized_limit = ir.ValueId.fromIndex(13);
    const v_normalized_step = ir.ValueId.fromIndex(14);
    const v_index = ir.ValueId.fromIndex(15);
    const v_body_index = ir.ValueId.fromIndex(16);

    const values = [_]ir.Value{
        .{ .id = v_left, .function = f, .type = .number, .origin = .{ .parameter = 0 } },
        .{ .id = v_right, .function = f, .type = .number, .origin = .{ .parameter = 1 } },
        .{ .id = v_cond, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_cond, .index = 0 } } },
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
        .{ .id = i_cond, .block = b_while, .operation = .{ .binary = .{ .operator = .less, .left = v_left, .right = v_right } }, .results = &.{v_cond}, .effects = .pure },
        .{ .id = i_control, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_control}, .effects = .pure },
        .{ .id = i_limit, .block = b_pre, .operation = .{ .constant = .{ .integer = "3" } }, .results = &.{v_limit}, .effects = .pure },
        .{ .id = i_step, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_step}, .effects = .pure },
        .{ .id = i_true, .block = b_pre, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure },
        .{ .id = i_false, .block = b_pre, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{v_false}, .effects = .pure },
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
        .{ .id = b_entry, .function = f, .terminator = .{ .jump = .{ .target = b_while } } },
        .{
            .id = b_while,
            .function = f,
            .instructions = &.{i_cond},
            .terminator = .{ .branch = .{
                .condition = v_cond,
                .then_edge = .{ .target = b_pre },
                .else_edge = .{ .target = b_done },
            } },
        },
        .{
            .id = b_pre,
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
                .else_edge = .{ .target = b_next },
            } },
        },
        .{ .id = b_body, .function = f, .parameters = &.{v_body_index}, .terminator = .{ .return_values = &.{v_body_index} } },
        .{ .id = b_next, .function = f, .terminator = .{ .jump = .{ .target = b_while } } },
        .{ .id = b_done, .function = f, .terminator = .{ .return_values = &.{} } },
    };

    const functions = [_]ir.Function{.{
        .id = f,
        .parameters = &.{ v_left, v_right },
        .blocks = &.{ b_entry, b_while, b_pre, b_header, b_body, b_next, b_done },
        .entry_block = b_entry,
    }};

    const program: ir.Program = .{
        .program_id = "acyclic-iteration-loop-boundary-test",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    // (a) The planner's decision: the root holds the `while` loop, whose body holds the header as a loop boundary;
    // its body arm is the else edge (the enclosing loop's continuation) and its boundary is the returning block.
    const loop = firstLoop(&plan) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(b_while, loop.header);
    var boundary: ?structure.LoopBoundaryControl = null;
    for (loop.body_region.nodes) |node| switch (node) {
        .loop_boundary => |value| boundary = value,
        else => {},
    };
    const control = boundary orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(b_header, control.block);
    try std.testing.expect(!control.body_on_true);
    try std.testing.expectEqual(b_next, control.body_edge.target);
    const terminal = switch (control.boundary) {
        .terminal => |value| value,
        else => return error.TestUnexpectedResult,
    };
    try std.testing.expectEqual(b_body, terminal.block);

    // (b) Readable admission recognizes the transition at the loop boundary.
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    try std.testing.expect(report.isClean());

    // (c) The loop-boundary matcher returns the numeric protocol, with the then edge as the body edge.
    const acyclic = (try matchAcyclicLoopBoundary(std.testing.allocator, &program, control)) orelse return error.TestUnexpectedResult;
    const numeric = switch (acyclic.protocol) {
        .numeric => |value| value,
        else => return error.TestUnexpectedResult,
    };
    try std.testing.expectEqual(v_body_index, numeric.body_parameter);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ v_control, v_limit, v_step, v_true }, numeric.initial_arguments);
    try std.testing.expectEqual(b_body, acyclic.body_edge.target);
    try std.testing.expectEqual(b_next, acyclic.exit_edge.target);

    // A `semantic_normalized` transition is exempt from the check, before and after; the copy enters from that
    // mode's canonical false state with the types and effects the semantic normalized test above gives it.
    var semantic_values = values;
    semantic_values[v_normalized_limit.index()].type = .dynamic;
    semantic_values[v_normalized_step.index()].type = .dynamic;
    semantic_values[v_index.index()].type = .dynamic;
    semantic_values[v_body_index.index()].type = .dynamic;
    var semantic_instructions = instructions;
    semantic_instructions[i_next.index()].operation.numeric_for_next.mode = .semantic_normalized;
    semantic_instructions[i_next.index()].effects = .dynamic_call;
    const semantic_entry_arguments = [_]ir.ValueId{ v_control, v_limit, v_step, v_false };
    var semantic_blocks = blocks;
    semantic_blocks[b_pre.index()].terminator.jump.arguments = &semantic_entry_arguments;
    var semantic = program;
    semantic.values = &semantic_values;
    semantic.instructions = &semantic_instructions;
    semantic.blocks = &semantic_blocks;
    var semantic_analysis = try cfg.Analysis.init(std.testing.allocator, &semantic, functions[0]);
    defer semantic_analysis.deinit();
    var semantic_plan = try structure.Plan.init(std.testing.allocator, &semantic_analysis);
    defer semantic_plan.deinit();
    var semantic_report = diagnostics.Report.init(std.testing.allocator);
    defer semantic_report.deinit();
    try validateFunction(std.testing.allocator, &semantic_report, &semantic, &semantic_analysis, &semantic_plan);
    try std.testing.expect(semantic_report.isClean());
    const semantic_loop = firstLoop(&semantic_plan) orelse return error.TestUnexpectedResult;
    var semantic_boundary: ?structure.LoopBoundaryControl = null;
    for (semantic_loop.body_region.nodes) |node| switch (node) {
        .loop_boundary => |value| semantic_boundary = value,
        else => {},
    };
    const semantic_control = semantic_boundary orelse return error.TestUnexpectedResult;
    try std.testing.expect((try matchAcyclicLoopBoundary(std.testing.allocator, &semantic, semantic_control)) == null);

    // A body that continues the enclosing loop instead of returning stays reported, before and after.
    var looping_blocks = blocks;
    looping_blocks[b_body.index()].terminator = .{ .jump = .{ .target = b_while } };
    var looping = program;
    looping.blocks = &looping_blocks;
    var looping_analysis = try cfg.Analysis.init(std.testing.allocator, &looping, functions[0]);
    defer looping_analysis.deinit();
    var looping_plan = try structure.Plan.init(std.testing.allocator, &looping_analysis);
    defer looping_plan.deinit();
    var looping_report = diagnostics.Report.init(std.testing.allocator);
    defer looping_report.deinit();
    try validateFunction(std.testing.allocator, &looping_report, &looping, &looping_analysis, &looping_plan);
    var reported = false;
    for (looping_report.diagnostics.items) |diagnostic| {
        if (diagnostic.code == .unsupported_readable_iteration_protocol and diagnostic.entity_index != null and
            diagnostic.entity_index.? == i_next.index()) reported = true;
    }
    try std.testing.expect(reported);
}

test "acyclic iteration in a loop body is recognized when its body only breaks" {
    // Form B: a numeric loop whose body always breaks, inside a `while` body (the source frontend's
    // shape). The header has its own exit block as join, and its arm regions carry the `while` loop's exit and
    // continue target, which no edge of the body uses. The header reaches its preheader again only through that
    // exit block, on the `while` loop's next trip.
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_while = ir.BlockId.fromIndex(1);
    const b_pre = ir.BlockId.fromIndex(2);
    const b_header = ir.BlockId.fromIndex(3);
    const b_body = ir.BlockId.fromIndex(4);
    const b_exit = ir.BlockId.fromIndex(5);
    const b_done = ir.BlockId.fromIndex(6);
    const i_control = ir.InstructionId.fromIndex(0);
    const i_limit = ir.InstructionId.fromIndex(1);
    const i_step = ir.InstructionId.fromIndex(2);
    const i_true = ir.InstructionId.fromIndex(3);
    const i_next = ir.InstructionId.fromIndex(4);
    const v_flag = ir.ValueId.fromIndex(0);
    const v_control = ir.ValueId.fromIndex(1);
    const v_limit = ir.ValueId.fromIndex(2);
    const v_step = ir.ValueId.fromIndex(3);
    const v_true = ir.ValueId.fromIndex(4);
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
        .{ .id = v_flag, .function = f, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = v_control, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_control, .index = 0 } } },
        .{ .id = v_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_limit, .index = 0 } } },
        .{ .id = v_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_step, .index = 0 } } },
        .{ .id = v_true, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
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
        .{ .id = i_control, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_control}, .effects = .pure },
        .{ .id = i_limit, .block = b_pre, .operation = .{ .constant = .{ .integer = "3" } }, .results = &.{v_limit}, .effects = .pure },
        .{ .id = i_step, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_step}, .effects = .pure },
        .{ .id = i_true, .block = b_pre, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure },
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
        .{ .id = b_entry, .function = f, .terminator = .{ .jump = .{ .target = b_while } } },
        .{
            .id = b_while,
            .function = f,
            .terminator = .{ .branch = .{
                .condition = v_flag,
                .then_edge = .{ .target = b_pre },
                .else_edge = .{ .target = b_done },
            } },
        },
        .{
            .id = b_pre,
            .function = f,
            .instructions = &.{ i_control, i_limit, i_step, i_true },
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
        .{ .id = b_body, .function = f, .parameters = &.{v_body_index}, .terminator = .{ .jump = .{ .target = b_exit } } },
        .{ .id = b_exit, .function = f, .terminator = .{ .jump = .{ .target = b_while } } },
        .{ .id = b_done, .function = f, .terminator = .{ .return_values = &.{} } },
    };

    const functions = [_]ir.Function{.{
        .id = f,
        .parameters = &.{v_flag},
        .blocks = &.{ b_entry, b_while, b_pre, b_header, b_body, b_exit, b_done },
        .entry_block = b_entry,
    }};

    const program: ir.Program = .{
        .program_id = "acyclic-iteration-break-in-loop-test",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    // (a) The planner's decision: the `while` loop's body holds the header as a branch joining at its exit block.
    const loop = firstLoop(&plan) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(b_while, loop.header);
    var found: ?structure.Branch = null;
    for (loop.body_region.nodes) |node| switch (node) {
        .branch => |value| {
            if (value.block == b_header) found = value;
        },
        else => {},
    };
    const branch = found orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(?ir.BlockId, b_exit), branch.join);

    // (b) The acyclic matcher takes the join form: the then edge is the body, the else edge leaves to the join.
    const acyclic = (try matchAcyclicBranch(std.testing.allocator, &program, branch)) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(b_body, acyclic.body_edge.target);
    try std.testing.expectEqual(b_exit, acyclic.exit_edge.target);
    try std.testing.expect(acyclic.exit_region == null);

    // (c) Readable admission recognizes the transition.
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    try std.testing.expect(report.isClean());
}

test "acyclic iteration in a loop body stays refused when its body also breaks the enclosing loop" {
    // The previous test's program with a body that may also leave the `while` loop: its edge to the `while` loop's
    // exit block lies outside the body region, and a `break` written there would bind to the native `for`. The
    // transition stays reported, whatever node the planner makes of the header.
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_while = ir.BlockId.fromIndex(1);
    const b_pre = ir.BlockId.fromIndex(2);
    const b_header = ir.BlockId.fromIndex(3);
    const b_body = ir.BlockId.fromIndex(4);
    const b_exit = ir.BlockId.fromIndex(5);
    const b_done = ir.BlockId.fromIndex(6);
    const i_control = ir.InstructionId.fromIndex(0);
    const i_limit = ir.InstructionId.fromIndex(1);
    const i_step = ir.InstructionId.fromIndex(2);
    const i_true = ir.InstructionId.fromIndex(3);
    const i_next = ir.InstructionId.fromIndex(4);
    const v_flag = ir.ValueId.fromIndex(0);
    const v_control = ir.ValueId.fromIndex(1);
    const v_limit = ir.ValueId.fromIndex(2);
    const v_step = ir.ValueId.fromIndex(3);
    const v_true = ir.ValueId.fromIndex(4);
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
        .{ .id = v_flag, .function = f, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = v_control, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_control, .index = 0 } } },
        .{ .id = v_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_limit, .index = 0 } } },
        .{ .id = v_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_step, .index = 0 } } },
        .{ .id = v_true, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
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
        .{ .id = i_control, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_control}, .effects = .pure },
        .{ .id = i_limit, .block = b_pre, .operation = .{ .constant = .{ .integer = "3" } }, .results = &.{v_limit}, .effects = .pure },
        .{ .id = i_step, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_step}, .effects = .pure },
        .{ .id = i_true, .block = b_pre, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure },
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
        .{ .id = b_entry, .function = f, .terminator = .{ .jump = .{ .target = b_while } } },
        .{
            .id = b_while,
            .function = f,
            .terminator = .{ .branch = .{
                .condition = v_flag,
                .then_edge = .{ .target = b_pre },
                .else_edge = .{ .target = b_done },
            } },
        },
        .{
            .id = b_pre,
            .function = f,
            .instructions = &.{ i_control, i_limit, i_step, i_true },
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
            .terminator = .{ .branch = .{
                .condition = v_flag,
                .then_edge = .{ .target = b_exit },
                .else_edge = .{ .target = b_done },
            } },
        },
        .{ .id = b_exit, .function = f, .terminator = .{ .jump = .{ .target = b_while } } },
        .{ .id = b_done, .function = f, .terminator = .{ .return_values = &.{} } },
    };

    const functions = [_]ir.Function{.{
        .id = f,
        .parameters = &.{v_flag},
        .blocks = &.{ b_entry, b_while, b_pre, b_header, b_body, b_exit, b_done },
        .entry_block = b_entry,
    }};

    const program: ir.Program = .{
        .program_id = "acyclic-iteration-break-enclosing-loop-test",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    var reported = false;
    for (report.diagnostics.items) |diagnostic| {
        if (diagnostic.code == .unsupported_readable_iteration_protocol and diagnostic.entity_index != null and
            diagnostic.entity_index.? == i_next.index()) reported = true;
    }
    try std.testing.expect(reported);
}

test "join-less acyclic iteration whose exit is the region stop is recognized when its body breaks to it" {
    // Form A: a numeric loop whose body always breaks, as the last statement of an `if` arm
    // (the disassembly frontend's shape). The loop's exit edge goes straight to the stop of the region holding the header
    // (the `if` join), so the planner gives the header no join; the body ends at that stop too, which is then the
    // loop's exit block as a join would be.
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_pre = ir.BlockId.fromIndex(1);
    const b_header = ir.BlockId.fromIndex(2);
    const b_body = ir.BlockId.fromIndex(3);
    const b_stop = ir.BlockId.fromIndex(4);
    const i_control = ir.InstructionId.fromIndex(0);
    const i_limit = ir.InstructionId.fromIndex(1);
    const i_step = ir.InstructionId.fromIndex(2);
    const i_true = ir.InstructionId.fromIndex(3);
    const i_next = ir.InstructionId.fromIndex(4);
    const v_flag = ir.ValueId.fromIndex(0);
    const v_control = ir.ValueId.fromIndex(1);
    const v_limit = ir.ValueId.fromIndex(2);
    const v_step = ir.ValueId.fromIndex(3);
    const v_true = ir.ValueId.fromIndex(4);
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
        .{ .id = v_flag, .function = f, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = v_control, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_control, .index = 0 } } },
        .{ .id = v_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_limit, .index = 0 } } },
        .{ .id = v_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_step, .index = 0 } } },
        .{ .id = v_true, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
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
        .{ .id = i_control, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_control}, .effects = .pure },
        .{ .id = i_limit, .block = b_pre, .operation = .{ .constant = .{ .integer = "3" } }, .results = &.{v_limit}, .effects = .pure },
        .{ .id = i_step, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_step}, .effects = .pure },
        .{ .id = i_true, .block = b_pre, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure },
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
            .terminator = .{ .branch = .{
                .condition = v_flag,
                .then_edge = .{ .target = b_pre },
                .else_edge = .{ .target = b_stop },
            } },
        },
        .{
            .id = b_pre,
            .function = f,
            .instructions = &.{ i_control, i_limit, i_step, i_true },
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
                .else_edge = .{ .target = b_stop },
            } },
        },
        .{ .id = b_body, .function = f, .parameters = &.{v_body_index}, .terminator = .{ .jump = .{ .target = b_stop } } },
        .{ .id = b_stop, .function = f, .terminator = .{ .return_values = &.{} } },
    };

    const functions = [_]ir.Function{.{
        .id = f,
        .parameters = &.{v_flag},
        .blocks = &.{ b_entry, b_pre, b_header, b_body, b_stop },
        .entry_block = b_entry,
    }};

    const program: ir.Program = .{
        .program_id = "acyclic-iteration-break-to-stop-test",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    // (a) The planner's decision: the `if` arm holds the header as a branch without a join.
    const outer = firstBranch(&plan) orelse return error.TestUnexpectedResult;
    var found: ?structure.Branch = null;
    for (outer.then_region.nodes) |node| switch (node) {
        .branch => |value| {
            if (value.block == b_header) found = value;
        },
        else => {},
    };
    const branch = found orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(?ir.BlockId, null), branch.join);

    // (b) The acyclic matcher takes the join form with the region stop as the loop's exit block.
    const acyclic = (try matchAcyclicBranch(std.testing.allocator, &program, branch)) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(b_stop, acyclic.exit_edge.target);
    try std.testing.expect(acyclic.exit_region == null);

    // (c) Readable admission recognizes the transition.
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    try std.testing.expect(report.isClean());
}

test "join-less acyclic iteration whose exit arm is not empty stays refused when its body breaks to the stop" {
    // The previous test's program with a block on the exit arm before the stop: written after the loop, that arm
    // would also run after the body's `break`, so the header stays refused.
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_pre = ir.BlockId.fromIndex(1);
    const b_header = ir.BlockId.fromIndex(2);
    const b_body = ir.BlockId.fromIndex(3);
    const b_after = ir.BlockId.fromIndex(4);
    const b_stop = ir.BlockId.fromIndex(5);
    const i_control = ir.InstructionId.fromIndex(0);
    const i_limit = ir.InstructionId.fromIndex(1);
    const i_step = ir.InstructionId.fromIndex(2);
    const i_true = ir.InstructionId.fromIndex(3);
    const i_next = ir.InstructionId.fromIndex(4);
    const i_after = ir.InstructionId.fromIndex(5);
    const v_flag = ir.ValueId.fromIndex(0);
    const v_control = ir.ValueId.fromIndex(1);
    const v_limit = ir.ValueId.fromIndex(2);
    const v_step = ir.ValueId.fromIndex(3);
    const v_true = ir.ValueId.fromIndex(4);
    const v_header_control = ir.ValueId.fromIndex(5);
    const v_header_limit = ir.ValueId.fromIndex(6);
    const v_header_step = ir.ValueId.fromIndex(7);
    const v_header_initial = ir.ValueId.fromIndex(8);
    const v_has = ir.ValueId.fromIndex(9);
    const v_normalized_limit = ir.ValueId.fromIndex(10);
    const v_normalized_step = ir.ValueId.fromIndex(11);
    const v_index = ir.ValueId.fromIndex(12);
    const v_body_index = ir.ValueId.fromIndex(13);
    const v_after = ir.ValueId.fromIndex(14);

    const values = [_]ir.Value{
        .{ .id = v_flag, .function = f, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = v_control, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_control, .index = 0 } } },
        .{ .id = v_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_limit, .index = 0 } } },
        .{ .id = v_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_step, .index = 0 } } },
        .{ .id = v_true, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
        .{ .id = v_header_control, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 0 } } },
        .{ .id = v_header_limit, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 1 } } },
        .{ .id = v_header_step, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 2 } } },
        .{ .id = v_header_initial, .function = f, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_header, .index = 3 } } },
        .{ .id = v_has, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 0 } } },
        .{ .id = v_normalized_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 1 } } },
        .{ .id = v_normalized_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 2 } } },
        .{ .id = v_index, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 3 } } },
        .{ .id = v_body_index, .function = f, .type = .number, .origin = .{ .block_parameter = .{ .block = b_body, .index = 0 } } },
        .{ .id = v_after, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_after, .index = 0 } } },
    };

    const instructions = [_]ir.Instruction{
        .{ .id = i_control, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_control}, .effects = .pure },
        .{ .id = i_limit, .block = b_pre, .operation = .{ .constant = .{ .integer = "3" } }, .results = &.{v_limit}, .effects = .pure },
        .{ .id = i_step, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_step}, .effects = .pure },
        .{ .id = i_true, .block = b_pre, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure },
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
        .{ .id = i_after, .block = b_after, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{v_after}, .effects = .pure },
    };

    const blocks = [_]ir.Block{
        .{
            .id = b_entry,
            .function = f,
            .terminator = .{ .branch = .{
                .condition = v_flag,
                .then_edge = .{ .target = b_pre },
                .else_edge = .{ .target = b_stop },
            } },
        },
        .{
            .id = b_pre,
            .function = f,
            .instructions = &.{ i_control, i_limit, i_step, i_true },
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
                .else_edge = .{ .target = b_after },
            } },
        },
        .{ .id = b_body, .function = f, .parameters = &.{v_body_index}, .terminator = .{ .jump = .{ .target = b_stop } } },
        .{ .id = b_after, .function = f, .instructions = &.{i_after}, .terminator = .{ .jump = .{ .target = b_stop } } },
        .{ .id = b_stop, .function = f, .terminator = .{ .return_values = &.{} } },
    };

    const functions = [_]ir.Function{.{
        .id = f,
        .parameters = &.{v_flag},
        .blocks = &.{ b_entry, b_pre, b_header, b_body, b_after, b_stop },
        .entry_block = b_entry,
    }};

    const program: ir.Program = .{
        .program_id = "acyclic-iteration-exit-arm-before-stop-test",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const outer = firstBranch(&plan) orelse return error.TestUnexpectedResult;
    var found: ?structure.Branch = null;
    for (outer.then_region.nodes) |node| switch (node) {
        .branch => |value| {
            if (value.block == b_header) found = value;
        },
        else => {},
    };
    const branch = found orelse return error.TestUnexpectedResult;
    try std.testing.expect((try matchAcyclicBranch(std.testing.allocator, &program, branch)) == null);

    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    var reported = false;
    for (report.diagnostics.items) |diagnostic| {
        if (diagnostic.code == .unsupported_readable_iteration_protocol and diagnostic.entity_index != null and
            diagnostic.entity_index.? == i_next.index()) reported = true;
    }
    try std.testing.expect(reported);
}

test "acyclic iteration in a loop body is recognized when its body breaks from a nested branch" {
    // A numeric loop inside a `while` body whose body leaves the loop from a nested
    // branch as well as at its end (`if a then if b then break end <code> end <code> break`). The nested `break` to the
    // loop's exit block X is written by the body region's own `repeat ... until true` wrapper, which declares and
    // consumes its flag inside the `for`, so nothing has to be carried past the native loop.
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_while = ir.BlockId.fromIndex(1);
    const b_pre = ir.BlockId.fromIndex(2);
    const b_header = ir.BlockId.fromIndex(3);
    const b_body = ir.BlockId.fromIndex(4);
    const b_nested = ir.BlockId.fromIndex(5);
    const b_inner = ir.BlockId.fromIndex(6);
    const b_tail = ir.BlockId.fromIndex(7);
    const b_exit = ir.BlockId.fromIndex(8);
    const b_done = ir.BlockId.fromIndex(9);
    const i_control = ir.InstructionId.fromIndex(0);
    const i_limit = ir.InstructionId.fromIndex(1);
    const i_step = ir.InstructionId.fromIndex(2);
    const i_true = ir.InstructionId.fromIndex(3);
    const i_next = ir.InstructionId.fromIndex(4);
    const i_inner = ir.InstructionId.fromIndex(5);
    const i_tail = ir.InstructionId.fromIndex(6);
    const v_flag = ir.ValueId.fromIndex(0);
    const v_a = ir.ValueId.fromIndex(1);
    const v_b = ir.ValueId.fromIndex(2);
    const v_control = ir.ValueId.fromIndex(3);
    const v_limit = ir.ValueId.fromIndex(4);
    const v_step = ir.ValueId.fromIndex(5);
    const v_true = ir.ValueId.fromIndex(6);
    const v_header_control = ir.ValueId.fromIndex(7);
    const v_header_limit = ir.ValueId.fromIndex(8);
    const v_header_step = ir.ValueId.fromIndex(9);
    const v_header_initial = ir.ValueId.fromIndex(10);
    const v_has = ir.ValueId.fromIndex(11);
    const v_normalized_limit = ir.ValueId.fromIndex(12);
    const v_normalized_step = ir.ValueId.fromIndex(13);
    const v_index = ir.ValueId.fromIndex(14);
    const v_body_index = ir.ValueId.fromIndex(15);
    const v_inner = ir.ValueId.fromIndex(16);
    const v_tail = ir.ValueId.fromIndex(17);

    const values = [_]ir.Value{
        .{ .id = v_flag, .function = f, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = v_a, .function = f, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = v_b, .function = f, .type = .boolean, .origin = .{ .parameter = 2 } },
        .{ .id = v_control, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_control, .index = 0 } } },
        .{ .id = v_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_limit, .index = 0 } } },
        .{ .id = v_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_step, .index = 0 } } },
        .{ .id = v_true, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
        .{ .id = v_header_control, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 0 } } },
        .{ .id = v_header_limit, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 1 } } },
        .{ .id = v_header_step, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 2 } } },
        .{ .id = v_header_initial, .function = f, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_header, .index = 3 } } },
        .{ .id = v_has, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 0 } } },
        .{ .id = v_normalized_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 1 } } },
        .{ .id = v_normalized_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 2 } } },
        .{ .id = v_index, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 3 } } },
        .{ .id = v_body_index, .function = f, .type = .number, .origin = .{ .block_parameter = .{ .block = b_body, .index = 0 } } },
        .{ .id = v_inner, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_inner, .index = 0 } } },
        .{ .id = v_tail, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_tail, .index = 0 } } },
    };

    const instructions = [_]ir.Instruction{
        .{ .id = i_control, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_control}, .effects = .pure },
        .{ .id = i_limit, .block = b_pre, .operation = .{ .constant = .{ .integer = "3" } }, .results = &.{v_limit}, .effects = .pure },
        .{ .id = i_step, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_step}, .effects = .pure },
        .{ .id = i_true, .block = b_pre, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure },
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
        .{ .id = i_inner, .block = b_inner, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{v_inner}, .effects = .pure },
        .{ .id = i_tail, .block = b_tail, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{v_tail}, .effects = .pure },
    };

    const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f, .terminator = .{ .jump = .{ .target = b_while } } },
        .{
            .id = b_while,
            .function = f,
            .terminator = .{ .branch = .{
                .condition = v_flag,
                .then_edge = .{ .target = b_pre },
                .else_edge = .{ .target = b_done },
            } },
        },
        .{
            .id = b_pre,
            .function = f,
            .instructions = &.{ i_control, i_limit, i_step, i_true },
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
            .terminator = .{ .branch = .{
                .condition = v_a,
                .then_edge = .{ .target = b_nested },
                .else_edge = .{ .target = b_tail },
            } },
        },
        .{
            .id = b_nested,
            .function = f,
            .terminator = .{ .branch = .{
                .condition = v_b,
                .then_edge = .{ .target = b_exit },
                .else_edge = .{ .target = b_inner },
            } },
        },
        .{ .id = b_inner, .function = f, .instructions = &.{i_inner}, .terminator = .{ .jump = .{ .target = b_tail } } },
        .{ .id = b_tail, .function = f, .instructions = &.{i_tail}, .terminator = .{ .jump = .{ .target = b_exit } } },
        .{ .id = b_exit, .function = f, .terminator = .{ .jump = .{ .target = b_while } } },
        .{ .id = b_done, .function = f, .terminator = .{ .return_values = &.{} } },
    };

    const functions = [_]ir.Function{.{
        .id = f,
        .parameters = &.{ v_flag, v_a, v_b },
        .blocks = &.{ b_entry, b_while, b_pre, b_header, b_body, b_nested, b_inner, b_tail, b_exit, b_done },
        .entry_block = b_entry,
    }};

    const program: ir.Program = .{
        .program_id = "acyclic-iteration-nested-break-in-loop-test",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    // (a) The planner's decision: the `while` loop's body holds the header as a branch joining at its exit block.
    const loop = firstLoop(&plan) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(b_while, loop.header);
    var found: ?structure.Branch = null;
    for (loop.body_region.nodes) |node| switch (node) {
        .branch => |value| {
            if (value.block == b_header) found = value;
        },
        else => {},
    };
    const branch = found orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(?ir.BlockId, b_exit), branch.join);

    // (b) The acyclic matcher takes the join form: the then edge is the body, the else edge leaves to the join.
    const acyclic = (try matchAcyclicBranch(std.testing.allocator, &program, branch)) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(b_body, acyclic.body_edge.target);
    try std.testing.expectEqual(b_exit, acyclic.exit_edge.target);
    try std.testing.expect(acyclic.exit_region == null);

    // (c) Readable admission recognizes the transition.
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    try std.testing.expect(report.isClean());
}

test "acyclic iteration in a loop body is recognized when its body may return" {
    // A numeric loop inside a `while` body whose body returns on one path and breaks on
    // the other (`if a then return end <code> break`). The planner places the body block at a `.terminal` loop
    // boundary; the region writes that boundary's return block inline, and it has no successor, so until the loop's
    // exit block the body still stays in its region.
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_while = ir.BlockId.fromIndex(1);
    const b_pre = ir.BlockId.fromIndex(2);
    const b_header = ir.BlockId.fromIndex(3);
    const b_body = ir.BlockId.fromIndex(4);
    const b_return = ir.BlockId.fromIndex(5);
    const b_tail = ir.BlockId.fromIndex(6);
    const b_exit = ir.BlockId.fromIndex(7);
    const b_done = ir.BlockId.fromIndex(8);
    const i_control = ir.InstructionId.fromIndex(0);
    const i_limit = ir.InstructionId.fromIndex(1);
    const i_step = ir.InstructionId.fromIndex(2);
    const i_true = ir.InstructionId.fromIndex(3);
    const i_next = ir.InstructionId.fromIndex(4);
    const i_return = ir.InstructionId.fromIndex(5);
    const i_tail = ir.InstructionId.fromIndex(6);
    const v_flag = ir.ValueId.fromIndex(0);
    const v_a = ir.ValueId.fromIndex(1);
    const v_control = ir.ValueId.fromIndex(2);
    const v_limit = ir.ValueId.fromIndex(3);
    const v_step = ir.ValueId.fromIndex(4);
    const v_true = ir.ValueId.fromIndex(5);
    const v_header_control = ir.ValueId.fromIndex(6);
    const v_header_limit = ir.ValueId.fromIndex(7);
    const v_header_step = ir.ValueId.fromIndex(8);
    const v_header_initial = ir.ValueId.fromIndex(9);
    const v_has = ir.ValueId.fromIndex(10);
    const v_normalized_limit = ir.ValueId.fromIndex(11);
    const v_normalized_step = ir.ValueId.fromIndex(12);
    const v_index = ir.ValueId.fromIndex(13);
    const v_body_index = ir.ValueId.fromIndex(14);
    const v_return = ir.ValueId.fromIndex(15);
    const v_tail = ir.ValueId.fromIndex(16);

    const values = [_]ir.Value{
        .{ .id = v_flag, .function = f, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = v_a, .function = f, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = v_control, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_control, .index = 0 } } },
        .{ .id = v_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_limit, .index = 0 } } },
        .{ .id = v_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_step, .index = 0 } } },
        .{ .id = v_true, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
        .{ .id = v_header_control, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 0 } } },
        .{ .id = v_header_limit, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 1 } } },
        .{ .id = v_header_step, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 2 } } },
        .{ .id = v_header_initial, .function = f, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_header, .index = 3 } } },
        .{ .id = v_has, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 0 } } },
        .{ .id = v_normalized_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 1 } } },
        .{ .id = v_normalized_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 2 } } },
        .{ .id = v_index, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 3 } } },
        .{ .id = v_body_index, .function = f, .type = .number, .origin = .{ .block_parameter = .{ .block = b_body, .index = 0 } } },
        .{ .id = v_return, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_return, .index = 0 } } },
        .{ .id = v_tail, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_tail, .index = 0 } } },
    };

    const instructions = [_]ir.Instruction{
        .{ .id = i_control, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_control}, .effects = .pure },
        .{ .id = i_limit, .block = b_pre, .operation = .{ .constant = .{ .integer = "3" } }, .results = &.{v_limit}, .effects = .pure },
        .{ .id = i_step, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_step}, .effects = .pure },
        .{ .id = i_true, .block = b_pre, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure },
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
        .{ .id = i_return, .block = b_return, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{v_return}, .effects = .pure },
        .{ .id = i_tail, .block = b_tail, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{v_tail}, .effects = .pure },
    };

    const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f, .terminator = .{ .jump = .{ .target = b_while } } },
        .{
            .id = b_while,
            .function = f,
            .terminator = .{ .branch = .{
                .condition = v_flag,
                .then_edge = .{ .target = b_pre },
                .else_edge = .{ .target = b_done },
            } },
        },
        .{
            .id = b_pre,
            .function = f,
            .instructions = &.{ i_control, i_limit, i_step, i_true },
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
            .terminator = .{ .branch = .{
                .condition = v_a,
                .then_edge = .{ .target = b_return },
                .else_edge = .{ .target = b_tail },
            } },
        },
        .{ .id = b_return, .function = f, .instructions = &.{i_return}, .terminator = .{ .return_values = &.{} } },
        .{ .id = b_tail, .function = f, .instructions = &.{i_tail}, .terminator = .{ .jump = .{ .target = b_exit } } },
        .{ .id = b_exit, .function = f, .terminator = .{ .jump = .{ .target = b_while } } },
        .{ .id = b_done, .function = f, .terminator = .{ .return_values = &.{} } },
    };

    const functions = [_]ir.Function{.{
        .id = f,
        .parameters = &.{ v_flag, v_a },
        .blocks = &.{ b_entry, b_while, b_pre, b_header, b_body, b_return, b_tail, b_exit, b_done },
        .entry_block = b_entry,
    }};

    const program: ir.Program = .{
        .program_id = "acyclic-iteration-return-or-break-in-loop-test",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    // (a) The planner's decision: the `while` loop's body holds the header as a branch joining at its exit block, and
    // the body arm holds the body block as a loop boundary whose boundary is the returning block.
    const loop = firstLoop(&plan) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(b_while, loop.header);
    var found: ?structure.Branch = null;
    for (loop.body_region.nodes) |node| switch (node) {
        .branch => |value| {
            if (value.block == b_header) found = value;
        },
        else => {},
    };
    const branch = found orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(?ir.BlockId, b_exit), branch.join);
    var boundary: ?structure.LoopBoundaryControl = null;
    for (branch.then_region.nodes) |node| switch (node) {
        .loop_boundary => |value| {
            if (value.block == b_body) boundary = value;
        },
        else => {},
    };
    const control = boundary orelse return error.TestUnexpectedResult;
    switch (control.boundary) {
        .terminal => |terminal| try std.testing.expectEqual(b_return, terminal.block),
        else => return error.TestUnexpectedResult,
    }

    // (b) The acyclic matcher takes the join form: the then edge is the body, the else edge leaves to the join.
    const acyclic = (try matchAcyclicBranch(std.testing.allocator, &program, branch)) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(b_body, acyclic.body_edge.target);
    try std.testing.expectEqual(b_exit, acyclic.exit_edge.target);
    try std.testing.expect(acyclic.exit_region == null);

    // (c) Readable admission recognizes the transition.
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    try std.testing.expect(report.isClean());
}

test "acyclic iteration in a loop body stays refused when a loop-boundary body owns an escape to its own continue target" {
    // The previous test's program whose non-returning path also breaks from a nested
    // branch (`if a then return end if b then if c then break end <code> end <code> break`). The loop boundary's body
    // region stops at the loop's exit block, which is also its continue target, and owns an escape to it: its wrapper
    // is consumed by a `continue`, which would bind to the native `for`. The transition stays reported, whatever node
    // the planner makes of the header.
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_while = ir.BlockId.fromIndex(1);
    const b_pre = ir.BlockId.fromIndex(2);
    const b_header = ir.BlockId.fromIndex(3);
    const b_body = ir.BlockId.fromIndex(4);
    const b_return = ir.BlockId.fromIndex(5);
    const b_outer = ir.BlockId.fromIndex(6);
    const b_nested = ir.BlockId.fromIndex(7);
    const b_inner = ir.BlockId.fromIndex(8);
    const b_tail = ir.BlockId.fromIndex(9);
    const b_exit = ir.BlockId.fromIndex(10);
    const b_done = ir.BlockId.fromIndex(11);
    const i_control = ir.InstructionId.fromIndex(0);
    const i_limit = ir.InstructionId.fromIndex(1);
    const i_step = ir.InstructionId.fromIndex(2);
    const i_true = ir.InstructionId.fromIndex(3);
    const i_next = ir.InstructionId.fromIndex(4);
    const i_return = ir.InstructionId.fromIndex(5);
    const i_inner = ir.InstructionId.fromIndex(6);
    const i_tail = ir.InstructionId.fromIndex(7);
    const v_flag = ir.ValueId.fromIndex(0);
    const v_a = ir.ValueId.fromIndex(1);
    const v_b = ir.ValueId.fromIndex(2);
    const v_c = ir.ValueId.fromIndex(3);
    const v_control = ir.ValueId.fromIndex(4);
    const v_limit = ir.ValueId.fromIndex(5);
    const v_step = ir.ValueId.fromIndex(6);
    const v_true = ir.ValueId.fromIndex(7);
    const v_header_control = ir.ValueId.fromIndex(8);
    const v_header_limit = ir.ValueId.fromIndex(9);
    const v_header_step = ir.ValueId.fromIndex(10);
    const v_header_initial = ir.ValueId.fromIndex(11);
    const v_has = ir.ValueId.fromIndex(12);
    const v_normalized_limit = ir.ValueId.fromIndex(13);
    const v_normalized_step = ir.ValueId.fromIndex(14);
    const v_index = ir.ValueId.fromIndex(15);
    const v_body_index = ir.ValueId.fromIndex(16);
    const v_return = ir.ValueId.fromIndex(17);
    const v_inner = ir.ValueId.fromIndex(18);
    const v_tail = ir.ValueId.fromIndex(19);

    const values = [_]ir.Value{
        .{ .id = v_flag, .function = f, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = v_a, .function = f, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = v_b, .function = f, .type = .boolean, .origin = .{ .parameter = 2 } },
        .{ .id = v_c, .function = f, .type = .boolean, .origin = .{ .parameter = 3 } },
        .{ .id = v_control, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_control, .index = 0 } } },
        .{ .id = v_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_limit, .index = 0 } } },
        .{ .id = v_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_step, .index = 0 } } },
        .{ .id = v_true, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
        .{ .id = v_header_control, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 0 } } },
        .{ .id = v_header_limit, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 1 } } },
        .{ .id = v_header_step, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 2 } } },
        .{ .id = v_header_initial, .function = f, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_header, .index = 3 } } },
        .{ .id = v_has, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 0 } } },
        .{ .id = v_normalized_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 1 } } },
        .{ .id = v_normalized_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 2 } } },
        .{ .id = v_index, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 3 } } },
        .{ .id = v_body_index, .function = f, .type = .number, .origin = .{ .block_parameter = .{ .block = b_body, .index = 0 } } },
        .{ .id = v_return, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_return, .index = 0 } } },
        .{ .id = v_inner, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_inner, .index = 0 } } },
        .{ .id = v_tail, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_tail, .index = 0 } } },
    };

    const instructions = [_]ir.Instruction{
        .{ .id = i_control, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_control}, .effects = .pure },
        .{ .id = i_limit, .block = b_pre, .operation = .{ .constant = .{ .integer = "3" } }, .results = &.{v_limit}, .effects = .pure },
        .{ .id = i_step, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_step}, .effects = .pure },
        .{ .id = i_true, .block = b_pre, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure },
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
        .{ .id = i_return, .block = b_return, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{v_return}, .effects = .pure },
        .{ .id = i_inner, .block = b_inner, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{v_inner}, .effects = .pure },
        .{ .id = i_tail, .block = b_tail, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{v_tail}, .effects = .pure },
    };

    const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f, .terminator = .{ .jump = .{ .target = b_while } } },
        .{
            .id = b_while,
            .function = f,
            .terminator = .{ .branch = .{
                .condition = v_flag,
                .then_edge = .{ .target = b_pre },
                .else_edge = .{ .target = b_done },
            } },
        },
        .{
            .id = b_pre,
            .function = f,
            .instructions = &.{ i_control, i_limit, i_step, i_true },
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
            .terminator = .{ .branch = .{
                .condition = v_a,
                .then_edge = .{ .target = b_return },
                .else_edge = .{ .target = b_outer },
            } },
        },
        .{ .id = b_return, .function = f, .instructions = &.{i_return}, .terminator = .{ .return_values = &.{} } },
        .{
            .id = b_outer,
            .function = f,
            .terminator = .{ .branch = .{
                .condition = v_b,
                .then_edge = .{ .target = b_nested },
                .else_edge = .{ .target = b_tail },
            } },
        },
        .{
            .id = b_nested,
            .function = f,
            .terminator = .{ .branch = .{
                .condition = v_c,
                .then_edge = .{ .target = b_exit },
                .else_edge = .{ .target = b_inner },
            } },
        },
        .{ .id = b_inner, .function = f, .instructions = &.{i_inner}, .terminator = .{ .jump = .{ .target = b_tail } } },
        .{ .id = b_tail, .function = f, .instructions = &.{i_tail}, .terminator = .{ .jump = .{ .target = b_exit } } },
        .{ .id = b_exit, .function = f, .terminator = .{ .jump = .{ .target = b_while } } },
        .{ .id = b_done, .function = f, .terminator = .{ .return_values = &.{} } },
    };

    const functions = [_]ir.Function{.{
        .id = f,
        .parameters = &.{ v_flag, v_a, v_b, v_c },
        .blocks = &.{ b_entry, b_while, b_pre, b_header, b_body, b_return, b_outer, b_nested, b_inner, b_tail, b_exit, b_done },
        .entry_block = b_entry,
    }};

    const program: ir.Program = .{
        .program_id = "acyclic-iteration-boundary-escape-to-continue-target-test",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    var reported = false;
    for (report.diagnostics.items) |diagnostic| {
        if (diagnostic.code == .unsupported_readable_iteration_protocol and diagnostic.entity_index != null and
            diagnostic.entity_index.? == i_next.index()) reported = true;
    }
    try std.testing.expect(reported);
}

test "acyclic iteration in a loop body stays refused when the loop's exit is the enclosing loop header and its body owns an escape to it" {
    // On the conformance path: the nested-break program with the loop's exit edge, the
    // nested `break` and the body's last edge going straight to the `while` header, as `resolve-ir` forwards them. The
    // body region then stops at its own continue target and owns an escape to it, which is consumed by a `continue`
    // that would bind to the native `for`. The transition stays reported, whatever node the planner makes of the
    // header.
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_while = ir.BlockId.fromIndex(1);
    const b_pre = ir.BlockId.fromIndex(2);
    const b_header = ir.BlockId.fromIndex(3);
    const b_body = ir.BlockId.fromIndex(4);
    const b_nested = ir.BlockId.fromIndex(5);
    const b_inner = ir.BlockId.fromIndex(6);
    const b_tail = ir.BlockId.fromIndex(7);
    const b_done = ir.BlockId.fromIndex(8);
    const i_control = ir.InstructionId.fromIndex(0);
    const i_limit = ir.InstructionId.fromIndex(1);
    const i_step = ir.InstructionId.fromIndex(2);
    const i_true = ir.InstructionId.fromIndex(3);
    const i_next = ir.InstructionId.fromIndex(4);
    const i_inner = ir.InstructionId.fromIndex(5);
    const i_tail = ir.InstructionId.fromIndex(6);
    const v_flag = ir.ValueId.fromIndex(0);
    const v_a = ir.ValueId.fromIndex(1);
    const v_b = ir.ValueId.fromIndex(2);
    const v_control = ir.ValueId.fromIndex(3);
    const v_limit = ir.ValueId.fromIndex(4);
    const v_step = ir.ValueId.fromIndex(5);
    const v_true = ir.ValueId.fromIndex(6);
    const v_header_control = ir.ValueId.fromIndex(7);
    const v_header_limit = ir.ValueId.fromIndex(8);
    const v_header_step = ir.ValueId.fromIndex(9);
    const v_header_initial = ir.ValueId.fromIndex(10);
    const v_has = ir.ValueId.fromIndex(11);
    const v_normalized_limit = ir.ValueId.fromIndex(12);
    const v_normalized_step = ir.ValueId.fromIndex(13);
    const v_index = ir.ValueId.fromIndex(14);
    const v_body_index = ir.ValueId.fromIndex(15);
    const v_inner = ir.ValueId.fromIndex(16);
    const v_tail = ir.ValueId.fromIndex(17);

    const values = [_]ir.Value{
        .{ .id = v_flag, .function = f, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = v_a, .function = f, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = v_b, .function = f, .type = .boolean, .origin = .{ .parameter = 2 } },
        .{ .id = v_control, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_control, .index = 0 } } },
        .{ .id = v_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_limit, .index = 0 } } },
        .{ .id = v_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_step, .index = 0 } } },
        .{ .id = v_true, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
        .{ .id = v_header_control, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 0 } } },
        .{ .id = v_header_limit, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 1 } } },
        .{ .id = v_header_step, .function = f, .origin = .{ .block_parameter = .{ .block = b_header, .index = 2 } } },
        .{ .id = v_header_initial, .function = f, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_header, .index = 3 } } },
        .{ .id = v_has, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 0 } } },
        .{ .id = v_normalized_limit, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 1 } } },
        .{ .id = v_normalized_step, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 2 } } },
        .{ .id = v_index, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 3 } } },
        .{ .id = v_body_index, .function = f, .type = .number, .origin = .{ .block_parameter = .{ .block = b_body, .index = 0 } } },
        .{ .id = v_inner, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_inner, .index = 0 } } },
        .{ .id = v_tail, .function = f, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_tail, .index = 0 } } },
    };

    const instructions = [_]ir.Instruction{
        .{ .id = i_control, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_control}, .effects = .pure },
        .{ .id = i_limit, .block = b_pre, .operation = .{ .constant = .{ .integer = "3" } }, .results = &.{v_limit}, .effects = .pure },
        .{ .id = i_step, .block = b_pre, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_step}, .effects = .pure },
        .{ .id = i_true, .block = b_pre, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_true}, .effects = .pure },
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
        .{ .id = i_inner, .block = b_inner, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{v_inner}, .effects = .pure },
        .{ .id = i_tail, .block = b_tail, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{v_tail}, .effects = .pure },
    };

    const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f, .terminator = .{ .jump = .{ .target = b_while } } },
        .{
            .id = b_while,
            .function = f,
            .terminator = .{ .branch = .{
                .condition = v_flag,
                .then_edge = .{ .target = b_pre },
                .else_edge = .{ .target = b_done },
            } },
        },
        .{
            .id = b_pre,
            .function = f,
            .instructions = &.{ i_control, i_limit, i_step, i_true },
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
                .else_edge = .{ .target = b_while },
            } },
        },
        .{
            .id = b_body,
            .function = f,
            .parameters = &.{v_body_index},
            .terminator = .{ .branch = .{
                .condition = v_a,
                .then_edge = .{ .target = b_nested },
                .else_edge = .{ .target = b_tail },
            } },
        },
        .{
            .id = b_nested,
            .function = f,
            .terminator = .{ .branch = .{
                .condition = v_b,
                .then_edge = .{ .target = b_while },
                .else_edge = .{ .target = b_inner },
            } },
        },
        .{ .id = b_inner, .function = f, .instructions = &.{i_inner}, .terminator = .{ .jump = .{ .target = b_tail } } },
        .{ .id = b_tail, .function = f, .instructions = &.{i_tail}, .terminator = .{ .jump = .{ .target = b_while } } },
        .{ .id = b_done, .function = f, .terminator = .{ .return_values = &.{} } },
    };

    const functions = [_]ir.Function{.{
        .id = f,
        .parameters = &.{ v_flag, v_a, v_b },
        .blocks = &.{ b_entry, b_while, b_pre, b_header, b_body, b_nested, b_inner, b_tail, b_done },
        .entry_block = b_entry,
    }};

    const program: ir.Program = .{
        .program_id = "acyclic-iteration-escape-to-enclosing-header-test",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    var reported = false;
    for (report.diagnostics.items) |diagnostic| {
        if (diagnostic.code == .unsupported_readable_iteration_protocol and diagnostic.entity_index != null and
            diagnostic.entity_index.? == i_next.index()) reported = true;
    }
    try std.testing.expect(reported);
}
