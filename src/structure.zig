const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const cfg_edge = @import("cfg_edge.zig");
const control_flow = @import("control_flow.zig");
const forwarding_history_cut = @import("forwarding_history_cut.zig");
const loop_continue_shape = @import("loop_continue_shape.zig");
const loop_exit_shape = @import("loop_exit_shape.zig");
const loop_side_exit = @import("loop_side_exit.zig");
const node_split = @import("node_split.zig");
const natural_loop = @import("natural_loop.zig");
const proof_effect_closure = @import("proof_effect_closure.zig");
const runtime_uses = @import("runtime_uses.zig");
const shared_control_shape = @import("shared_control_shape.zig");
const structural_overlap = @import("structural_overlap.zig");
const luau_runtime = @import("luau_runtime.zig");

pub const BuildError = error{UnsupportedShape} || std.mem.Allocator.Error;

pub const Collision = struct {
    block: ir.BlockId,
    previous: ?ir.BlockId,
    incoming: ?ir.CfgEdgeRef,
    reason: CollisionReason,
    owner_context: ?CollisionContext = null,
    incoming_context: ?CollisionContext = null,
    incoming_group: []ir.CfgEdgeRef = &.{},
    unvisited_frontiers: []UnvisitedFrontier = &.{},

    pub fn deinit(self: *Collision, allocator: std.mem.Allocator) void {
        if (self.incoming_group.len != 0) allocator.free(self.incoming_group);
        for (self.unvisited_frontiers) |frontier| {
            allocator.free(frontier.incoming);
            if (frontier.incoming_contexts.len != 0) allocator.free(frontier.incoming_contexts);
            allocator.free(frontier.closure);
        }
        if (self.unvisited_frontiers.len != 0) allocator.free(self.unvisited_frontiers);
        self.* = undefined;
    }
};

pub const CollisionContext = struct {
    start: ir.BlockId,
    stop: ?ir.BlockId,
    loop_exit: ?ir.BlockId,
    continue_target: ?ir.BlockId,
    parameter_arguments: ?[]const ir.ValueId = null,
};

pub const UnvisitedFrontier = struct {
    block: ir.BlockId,
    incoming: []ir.CfgEdgeRef,
    closure: []ir.BlockId,
    // Contexts are aligned with incoming.  Keeping them at the frontier
    // prevents the normalizer from turning an authenticated visit into an
    // unknown collision arm during batched cloning.
    incoming_contexts: []?CollisionContext = &.{},
};

pub const CollisionReason = enum {
    already_owned,
    outside_region,
    unvisited_loop_member,
    unvisited_reachable,
};

pub const Region = struct {
    nodes: []Node,
    stop: ?ir.BlockId,
    loop_exit: ?ir.BlockId,
    continue_target: ?ir.BlockId = null,
    // A validated CFG may be structurally irreducible even after all
    // authenticated normalization.  The arbitrary form keeps the complete
    // block graph available to the emitter without inventing ownership.
    arbitrary_cfg: bool = false,
    terminal_projection: ?TerminalProjection = null,
    continue_projection: ?ContinueProjection = null,
    escape_projection: ?EscapeProjection = null,
    stop_forwarding: ?ir.BlockId = null,
};

pub const TerminalProjection = struct {
    terminal: ir.BlockId,
    edge: ?ir.Edge,
};

pub const ContinueProjection = struct {
    target: ir.BlockId,
    edge: ?ir.Edge,
    forwarding: ?control_flow.ForwardingPath = null,
};

pub const EscapeProjection = struct {
    target: ir.BlockId,
    edge: ?ir.Edge,
};

pub const Branch = struct {
    block: ir.BlockId,
    then_region: *Region,
    else_region: *Region,
    join: ?ir.BlockId,
    then_edge_override: ?EdgeOverride = null,
    else_edge_override: ?EdgeOverride = null,
    then_shared_reentry: ?loop_continue_shape.SharedPaths.EntryRef = null,
    else_shared_reentry: ?loop_continue_shape.SharedPaths.EntryRef = null,
};

pub const EdgeOverride = union(enum) {
    forwarding: control_flow.ForwardingPath,
    history_cut: forwarding_history_cut.Cut,

    pub fn edge(self: EdgeOverride) ir.Edge {
        return switch (self) {
            .forwarding => |path| path.edge,
            .history_cut => |cut| cut.edge,
        };
    }
};

pub const Loop = struct {
    header: ir.BlockId,
    body_region: *Region,
    body_edge: ir.Edge,
    exit_edge: ir.Edge,
    exit_is_escape: bool = false,
    continue_on_true: bool,
};

pub const LatchLoop = struct {
    header: ir.BlockId,
    body_region: *Region,
    exit: ir.BlockId,
    exit_is_escape: bool = false,
    latch_count: usize,
    shared_reentries: ?*loop_continue_shape.SharedPaths = null,
    shared_exits: ?*loop_exit_shape.SharedPaths = null,
};

pub const InfiniteLoop = struct {
    header: ir.BlockId,
    body_region: *Region,
    exit: ?ir.BlockId = null,
    exit_is_escape: bool = false,
    shared_side_exit: ?SharedSideExit = null,
};

pub const SharedSideEntry = struct {
    entry: ir.BlockId,
    region: *Region,
};

pub const SharedSideExit = struct {
    entries: []SharedSideEntry,
};

fn ownSharedSideRegions(
    allocator: std.mem.Allocator,
    entries: []SharedSideEntry,
) BuildError!?SharedSideExit {
    if (entries.len == 0) {
        allocator.free(entries);
        return null;
    }
    for (entries) |side| {
        if (side.region.nodes.len == 0) {
            for (entries) |owned| destroyRegion(allocator, owned.region);
            allocator.free(entries);
            return null;
        }
        if (side.region.nodes[0].blockId() != side.entry) {
            for (entries) |owned| destroyRegion(allocator, owned.region);
            allocator.free(entries);
            return error.UnsupportedShape;
        }
    }
    return .{ .entries = entries };
}

test "shared side ownership rejects empty and mismatched regions" {
    const allocator = std.testing.allocator;
    const entry = ir.BlockId.fromIndex(0);

    const empty = try allocator.alloc(SharedSideEntry, 0);
    try std.testing.expect(try ownSharedSideRegions(allocator, empty) == null);

    const mismatched_region = try allocator.create(Region);
    const mismatched_nodes = try allocator.alloc(Node, 1);
    mismatched_nodes[0] = .{ .block = ir.BlockId.fromIndex(1) };
    mismatched_region.* = .{ .nodes = mismatched_nodes, .stop = ir.BlockId.fromIndex(2), .loop_exit = null };
    const mismatched = try allocator.alloc(SharedSideEntry, 1);
    mismatched[0] = .{ .entry = entry, .region = mismatched_region };
    try std.testing.expectError(error.UnsupportedShape, ownSharedSideRegions(allocator, mismatched));

    const owned_region = try allocator.create(Region);
    const owned_nodes = try allocator.alloc(Node, 1);
    owned_nodes[0] = .{ .block = entry };
    owned_region.* = .{ .nodes = owned_nodes, .stop = ir.BlockId.fromIndex(2), .loop_exit = null };
    const owned = try allocator.alloc(SharedSideEntry, 1);
    owned[0] = .{ .entry = entry, .region = owned_region };
    const side = (try ownSharedSideRegions(allocator, owned)).?;
    try std.testing.expectEqual(entry, side.entries[0].entry);
    destroySharedSideExit(allocator, side);
}

test "shared side escape projection shadows its owned entry" {
    const allocator = std.testing.allocator;
    const outer = ir.BlockId.fromIndex(1);
    const entry = ir.BlockId.fromIndex(2);
    const inner = ir.BlockId.fromIndex(3);
    var inner_target = Builder.EscapeTarget{ .block = inner, .parent = null };
    var entry_target = Builder.EscapeTarget{ .block = entry, .parent = &inner_target };
    var outer_target = Builder.EscapeTarget{ .block = outer, .parent = &entry_target };

    var projection = try Builder.shadowEscapeTargetsAlloc(allocator, &outer_target, entry);
    defer projection.deinit(allocator);
    try std.testing.expect(projection.targets != null);
    try std.testing.expectEqual(outer, projection.targets.?.block);
    try std.testing.expect(projection.targets.?.parent != null);
    try std.testing.expectEqual(inner, projection.targets.?.parent.?.block);
    try std.testing.expect(projection.targets.?.parent.?.parent == null);
}

test "nested loop escape chain retains enclosing and outer targets" {
    const outer = ir.BlockId.fromIndex(10);
    const enclosing = ir.BlockId.fromIndex(11);
    const unrelated = ir.BlockId.fromIndex(12);
    var outer_target = Builder.EscapeTarget{ .block = outer, .parent = null };
    var enclosing_target: Builder.EscapeTarget = undefined;

    const chain = Builder.prependEscapeTarget(&enclosing_target, enclosing, &outer_target);
    try std.testing.expect(Builder.isEscapeTarget(chain, enclosing));
    try std.testing.expect(Builder.isEscapeTarget(chain, outer));
    try std.testing.expect(!Builder.isEscapeTarget(chain, unrelated));
}

test "loop free-target analysis owns ordinary loop exits" {
    const header = ir.BlockId.fromIndex(10);
    const exit = ir.BlockId.fromIndex(11);
    var body_nodes = [_]Node{.{ .block = header }};
    var body = Region{
        .nodes = &body_nodes,
        .stop = header,
        .loop_exit = exit,
        .continue_target = header,
    };
    var root_nodes = [_]Node{.{ .infinite_loop = .{
        .header = header,
        .body_region = &body,
        .exit = exit,
    } }};
    var root = Region{ .nodes = &root_nodes, .stop = null, .loop_exit = null };

    const ordinary_targets = try regionFreeTargetsAlloc(std.testing.allocator, &root);
    defer std.testing.allocator.free(ordinary_targets);
    try std.testing.expectEqual(@as(usize, 0), ordinary_targets.len);

    root_nodes[0].infinite_loop.exit_is_escape = true;
    const escaping_targets = try regionFreeTargetsAlloc(std.testing.allocator, &root);
    defer std.testing.allocator.free(escaping_targets);
    try std.testing.expectEqual(@as(usize, 1), escaping_targets.len);
    try std.testing.expectEqual(exit, escaping_targets[0]);
}

test "loop validation cache generation reuses unchanged state and invalidates on reopen" {
    var visited = [_]bool{ true, false };
    var visited_contexts = [_]?Builder.VisitContext{ null, null };
    var loop_headers = [_]bool{ true, false };
    var epochs = [_]usize{ std.math.maxInt(usize), std.math.maxInt(usize) };
    var generations = [_]usize{ std.math.maxInt(usize), std.math.maxInt(usize) };
    var outcomes = [_]LoopValidationOutcome{ .uncomputed, .uncomputed };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = undefined,
        .visited = &visited,
        .visited_contexts = &visited_contexts,
        .loop_headers = &loop_headers,
        .loop_validation_epochs = &epochs,
        .loop_validation_generations = &generations,
        .loop_validation_outcomes = &outcomes,
        .validation_generation = 7,
        .visited_count = 2,
    };
    const membership = [_]bool{ true, false };

    try builder.validateNaturalLoopMembership(0, &membership, null);
    try std.testing.expectEqual(LoopValidationOutcome.valid, builder.cachedLoopValidation(0, null));
    try std.testing.expectEqual(@as(usize, 2), epochs[0]);
    try std.testing.expectEqual(@as(usize, 7), generations[0]);

    try builder.reopenLoopHeader(0);
    try std.testing.expectEqual(@as(usize, 1), builder.visited_count);
    try std.testing.expectEqual(@as(usize, 8), builder.validation_generation);
    try std.testing.expectEqual(LoopValidationOutcome.uncomputed, builder.cachedLoopValidation(0, null));

    // The visit count alone is intentionally restored to the old value.  The
    // generation stamp must still prevent reuse of the old result.
    visited[0] = true;
    builder.visited_count = 2;
    try std.testing.expectEqual(LoopValidationOutcome.uncomputed, builder.cachedLoopValidation(0, null));

    try builder.validateNaturalLoopMembership(0, &membership, null);
    try std.testing.expectEqual(LoopValidationOutcome.valid, builder.cachedLoopValidation(0, null));
    try std.testing.expectEqual(@as(usize, 8), generations[0]);
}

pub const LoopControl = struct {
    block: ir.BlockId,
    continue_edge: ir.Edge,
    exit_edge: ir.Edge,
    continue_on_true: bool,
};

pub const LoopTerminalControl = struct {
    block: ir.BlockId,
    continue_edge: ir.Edge,
    terminal_edge: ir.Edge,
    terminal_block: ir.BlockId,
    continue_on_true: bool,
};

pub const LoopBoundary = union(enum) {
    exit: ir.Edge,
    escape: ir.Edge,
    terminal: struct {
        edge: ir.Edge,
        block: ir.BlockId,
    },
    side_exit: struct {
        entry_edge: ir.Edge,
        region: *Region,
    },
    side_escape: struct {
        entry_edge: ir.Edge,
        region: *Region,
        target: ir.BlockId,
    },
    shared_exit: loop_exit_shape.SharedPaths.EntryRef,
};

pub const LoopBoundaryControl = struct {
    block: ir.BlockId,
    body_edge: ir.Edge,
    body_region: *Region,
    boundary: LoopBoundary,
    body_on_true: bool,
};

pub const Node = union(enum) {
    block: ir.BlockId,
    branch: Branch,
    loop: Loop,
    latch_loop: LatchLoop,
    infinite_loop: InfiniteLoop,
    loop_control: LoopControl,
    loop_boundary: LoopBoundaryControl,
    loop_terminal: LoopTerminalControl,

    pub fn blockId(self: Node) ir.BlockId {
        return switch (self) {
            .block => |block_id| block_id,
            .branch => |branch| branch.block,
            .loop => |loop| loop.header,
            .latch_loop => |loop| loop.header,
            .infinite_loop => |loop| loop.header,
            .loop_control => |control| control.block,
            .loop_boundary => |control| control.block,
            .loop_terminal => |control| control.block,
        };
    }
};

const LoopValidationOutcome = enum { uncomputed, valid, invalid };

const FreeTargetCapture = struct {
    target: ir.BlockId,
    parent: ?*const FreeTargetCapture,
};

pub fn regionFreeTargetsAlloc(
    allocator: std.mem.Allocator,
    region: *const Region,
) std.mem.Allocator.Error![]ir.BlockId {
    var targets: std.AutoHashMapUnmanaged(ir.BlockId, void) = .empty;
    defer targets.deinit(allocator);
    try collectRegionFreeTargets(allocator, region, null, &targets);
    return sortedFreeTargetsAlloc(allocator, &targets);
}

pub fn loopFreeTargetsAlloc(
    allocator: std.mem.Allocator,
    node: Node,
) std.mem.Allocator.Error![]ir.BlockId {
    var targets: std.AutoHashMapUnmanaged(ir.BlockId, void) = .empty;
    defer targets.deinit(allocator);
    try collectLoopFreeTargets(allocator, node, null, &targets);
    return sortedFreeTargetsAlloc(allocator, &targets);
}

pub fn regionOwnsEscape(region: *const Region) bool {
    const target = region.stop orelse return false;
    if (region.continue_projection) |projection| {
        if (region.continue_target == null or region.continue_target.? != projection.target) return true;
    }
    return nodesEscapeTo(region.nodes, target);
}

/// Reports an escape carried by a nested structured node to `target`.
///
/// A loop header can be both the current region's owned stop and the target of
/// a nested nonlocal escape. The latter must be consumed as a loop continue by
/// the emitter, even though it is intentionally absent from free-target sets.
pub fn regionHasNestedEscapeTo(region: *const Region, target: ir.BlockId) bool {
    for (region.nodes) |node| {
        if (nodeEscapesTo(node, target)) return true;
    }
    return false;
}

/// Reports whether this region contains a loop-boundary exit to `target`.
///
/// Unlike an ordinary nonlocal escape, a loop-boundary exit is owned by the
/// loop that supplies `Region.loop_exit`. The emitter still needs to carry it
/// through temporary `repeat ... until true` transfer wrappers, so keep this
/// query separate from the free-target census.
pub fn regionHasLoopBoundaryExitTo(region: *const Region, target: ir.BlockId) bool {
    for (region.nodes) |node| {
        if (nodeHasLoopBoundaryExitTo(node, target)) return true;
    }
    return false;
}

/// Returns the distinct loop-boundary exit targets in a structured region.
/// These targets need function-scope signal locals so nested wrappers can
/// communicate with the loop that owns each exit.
pub fn loopBoundaryExitTargetsAlloc(
    allocator: std.mem.Allocator,
    region: *const Region,
) std.mem.Allocator.Error![]ir.BlockId {
    var targets: std.AutoHashMapUnmanaged(ir.BlockId, void) = .empty;
    defer targets.deinit(allocator);
    try collectLoopBoundaryExitTargets(allocator, region, &targets);
    return sortedFreeTargetsAlloc(allocator, &targets);
}

test "loop-boundary exit targets are tracked separately from free targets" {
    const allocator = std.testing.allocator;
    const block = ir.BlockId.fromIndex(1);
    const exit = ir.BlockId.fromIndex(3);
    var body_region = Region{ .nodes = &.{}, .stop = null, .loop_exit = exit };
    var nodes = [_]Node{.{ .loop_boundary = .{
        .block = block,
        .body_edge = .{ .target = ir.BlockId.fromIndex(2) },
        .body_region = &body_region,
        .boundary = .{ .exit = .{ .target = exit } },
        .body_on_true = true,
    } }};
    const region = Region{ .nodes = &nodes, .stop = null, .loop_exit = exit };

    try std.testing.expect(regionHasLoopBoundaryExitTo(&region, exit));
    try std.testing.expect(!regionHasLoopBoundaryExitTo(&region, ir.BlockId.fromIndex(4)));
    const boundary_targets = try loopBoundaryExitTargetsAlloc(allocator, &region);
    defer allocator.free(boundary_targets);
    try std.testing.expectEqualSlices(ir.BlockId, &.{exit}, boundary_targets);

    const free_targets = try regionFreeTargetsAlloc(allocator, &region);
    defer allocator.free(free_targets);
    try std.testing.expectEqual(@as(usize, 0), free_targets.len);
}

fn functionExceedsLocalRegisterBudget(program: *const ir.Program, function: ir.Function) bool {
    var potential_locals = function.parameters.len;
    for (program.values) |value| {
        if (value.function != function.id) continue;
        switch (value.origin) {
            .parameter => {},
            else => potential_locals = std.math.add(usize, potential_locals, 1) catch return true,
        }
    }
    for (program.value_packs) |pack| {
        if (pack.function == function.id) {
            potential_locals = std.math.add(usize, potential_locals, 1) catch return true;
        }
    }
    for (function.local_places) |place_id| {
        if (place_id.index() >= program.places.len) continue;
        const place = program.places[place_id.index()];
        if (place.function == function.id and place.origin == .local) {
            potential_locals = std.math.add(usize, potential_locals, 1) catch return true;
        }
    }
    return potential_locals > luau_runtime.max_local_registers;
}

const Builder = struct {
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    visited: []bool,
    visited_contexts: []?VisitContext,
    loop_headers: []const bool,
    loop_memberships: ?[]?[]bool = null,
    loop_validation_epochs: ?[]usize = null,
    loop_validation_generations: ?[]usize = null,
    loop_validation_outcomes: ?[]LoopValidationOutcome = null,
    stop_boundary_closure: ?[]?bool = null,
    validation_generation: usize = 0,
    replay_context: ?*structural_overlap.ReplayProjectionContext = null,
    visited_count: usize = 0,
    active_shared_reentries: ?*const loop_continue_shape.SharedPaths = null,
    active_shared_exits: ?*const loop_exit_shape.SharedPaths = null,
    collision: ?*?Collision = null,
    trace_projection_calls: usize = 0,
    trace_projection_ms: i64 = 0,
    trace_parameter_calls: usize = 0,
    trace_parameter_ms: i64 = 0,
    trace_reach_calls: usize = 0,
    trace_reach_ms: i64 = 0,
    trace_bridge_calls: usize = 0,
    trace_bridge_ms: i64 = 0,
    trace_iteration_entry_calls: usize = 0,
    trace_join_calls: usize = 0,
    trace_join_ms: i64 = 0,
    trace_loop_probe_calls: usize = 0,
    trace_loop_probe_ms: i64 = 0,
    trace_build_loop_ms: i64 = 0,
    trace_build_latch_ms: i64 = 0,
    trace_build_infinite_ms: i64 = 0,
    trace_infinite_classify_calls: usize = 0,
    trace_infinite_classify_ms: i64 = 0,
    trace_infinite_continuation_calls: usize = 0,
    trace_infinite_continuation_ms: i64 = 0,
    trace_infinite_resolve_calls: usize = 0,
    trace_infinite_resolve_ms: i64 = 0,
    trace_infinite_shared_entry_calls: usize = 0,
    trace_infinite_shared_entry_ms: i64 = 0,
    trace_infinite_body_calls: usize = 0,
    trace_infinite_body_ms: i64 = 0,
    trace_infinite_probe_calls: usize = 0,
    trace_region_step_calls: usize = 0,
    trace_outside_termination_calls: usize = 0,
    trace_loop_calls: usize = 0,
    trace_loop_ms: i64 = 0,
    trace_empty_reentry_calls: usize = 0,
    trace_visited_boundary_calls: usize = 0,
    trace_zero_parameter_replay_calls: usize = 0,
    trace_region_depth: usize = 0,
    mutation_log: std.ArrayList(Mutation) = .empty,
    mutation_depth: usize = 0,

    const EscapeTarget = struct {
        block: ir.BlockId,
        parent: ?*const EscapeTarget,
    };

    const EscapeTargetProjection = struct {
        targets: ?*const EscapeTarget,
        owned_head: ?*EscapeTarget = null,
        owned_count: usize = 0,

        fn deinit(self: *EscapeTargetProjection, allocator: std.mem.Allocator) void {
            var current = self.owned_head;
            var remaining = self.owned_count;
            while (current) |target| {
                if (remaining == 0) break;
                const next = target.parent;
                allocator.destroy(target);
                current = @constCast(next);
                remaining -= 1;
            }
            self.* = undefined;
        }
    };

    const VisitContext = struct {
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        // Parameterized continuations carry an SSA-like tuple at their
        // boundary. Keep that projection with the visit context so a later
        // entry cannot reuse the region merely because its control context
        // happens to match.
        parameter_arguments: ?[]const ir.ValueId = null,
        // Keep the edge that first admitted this block into the owner
        // context.  A parameterized continuation can be entered after an
        // effectful prefix whose region entry has no parameter tuple; the
        // edge still carries the tuple that must authenticate a later SCC
        // reentry.
        entry_reference: ?ir.CfgEdgeRef = null,
    };

    // Candidate builders speculatively claim ownership while deciding whether
    // a region is representable. Keep the rollback trail local to Builder so
    // rejected nested candidates cannot poison their enclosing search.
    const Mutation = union(enum) {
        visited: struct {
            index: usize,
            value: bool,
        },
        context: struct {
            index: usize,
            value: ?VisitContext,
        },
        validation: struct {
            index: usize,
            epoch: usize,
            generation: usize,
            outcome: LoopValidationOutcome,
        },
        membership: struct {
            index: usize,
            value: ?[]bool,
            installed: []bool,
        },
    };

    const MutationCheckpoint = struct {
        log_len: usize,
        visited_count: usize,
        validation_generation: usize,
        depth: usize,
    };

    fn beginMutation(self: *Builder) MutationCheckpoint {
        const checkpoint = MutationCheckpoint{
            .log_len = self.mutation_log.items.len,
            .visited_count = self.visited_count,
            .validation_generation = self.validation_generation,
            .depth = self.mutation_depth,
        };
        self.mutation_depth += 1;
        return checkpoint;
    }

    fn finishMutation(self: *Builder, checkpoint: MutationCheckpoint) void {
        std.debug.assert(self.mutation_depth == checkpoint.depth + 1);
        std.debug.assert(self.mutation_log.items.len >= checkpoint.log_len);
        self.mutation_depth -= 1;
        if (self.mutation_depth == 0) {
            self.mutation_log.deinit(self.allocator);
            self.mutation_log = .empty;
        }
    }

    fn rollbackMutation(self: *Builder, checkpoint: MutationCheckpoint) void {
        std.debug.assert(self.mutation_depth == checkpoint.depth + 1);
        while (self.mutation_log.items.len > checkpoint.log_len) {
            const entry = self.mutation_log.pop() orelse unreachable;
            switch (entry) {
                .visited => |mutation| self.visited[mutation.index] = mutation.value,
                .context => |mutation| self.visited_contexts[mutation.index] = mutation.value,
                .validation => |mutation| {
                    if (self.loop_validation_epochs) |epochs| epochs[mutation.index] = mutation.epoch;
                    if (self.loop_validation_generations) |generations| generations[mutation.index] = mutation.generation;
                    if (self.loop_validation_outcomes) |outcomes| outcomes[mutation.index] = mutation.outcome;
                },
                .membership => |mutation| {
                    if (self.loop_memberships) |cache| {
                        if (cache[mutation.index]) |current| {
                            if (current.ptr == mutation.installed.ptr and current.len == mutation.installed.len) {
                                self.allocator.free(current);
                            }
                        }
                        cache[mutation.index] = mutation.value;
                    }
                },
            }
        }
        self.visited_count = checkpoint.visited_count;
        self.validation_generation = checkpoint.validation_generation;
        self.mutation_depth -= 1;
        if (self.mutation_depth == 0) {
            self.mutation_log.deinit(self.allocator);
            self.mutation_log = .empty;
        }
    }

    fn setVisited(self: *Builder, index: usize, value: bool) BuildError!void {
        if (self.visited[index] == value) return;
        if (self.mutation_depth != 0) {
            try self.mutation_log.append(self.allocator, .{ .visited = .{
                .index = index,
                .value = self.visited[index],
            } });
        }
        self.visited[index] = value;
    }

    fn markVisited(self: *Builder, index: usize) BuildError!void {
        if (self.visited[index]) return;
        try self.setVisited(index, true);
        self.visited_count += 1;
    }

    fn unmarkVisited(self: *Builder, index: usize) BuildError!void {
        if (!self.visited[index] or self.visited_count == 0) return error.UnsupportedShape;
        try self.setVisited(index, false);
        self.visited_count -= 1;
    }

    fn setVisitedContext(self: *Builder, index: usize, value: ?VisitContext) BuildError!void {
        if (self.mutation_depth != 0) {
            try self.mutation_log.append(self.allocator, .{ .context = .{
                .index = index,
                .value = self.visited_contexts[index],
            } });
        }
        if (value != null and index < self.analysis.function.blocks.len) {
            const block_id = self.analysis.function.blocks[index];
            if (isParameterizedNumericTransitionHeader(self.analysis.program, block_id)) {
                structural_overlap.traceStructural("structural_phase numeric_context_set block={} start={} stop={?} loop_exit={?} continue_target={?} arguments={any} entry_source={?}\n", .{
                    block_id.index(),
                    value.?.start.index(),
                    if (value.?.stop) |block| block.index() else null,
                    if (value.?.loop_exit) |block| block.index() else null,
                    if (value.?.continue_target) |block| block.index() else null,
                    value.?.parameter_arguments orelse &.{},
                    if (value.?.entry_reference) |reference| reference.source.index() else null,
                });
            }
        }
        self.visited_contexts[index] = value;
    }

    fn setVisitContextParameterArguments(
        self: *Builder,
        index: usize,
        value: ?[]const ir.ValueId,
    ) BuildError!void {
        const context = self.visited_contexts[index] orelse return error.UnsupportedShape;
        if (self.mutation_depth != 0) {
            try self.mutation_log.append(self.allocator, .{ .context = .{
                .index = index,
                .value = context,
            } });
        }
        if (index < self.analysis.function.blocks.len) {
            const block_id = self.analysis.function.blocks[index];
            if (isParameterizedNumericTransitionHeader(self.analysis.program, block_id)) {
                structural_overlap.traceStructural("structural_phase numeric_context_update block={} arguments={any}\n", .{
                    block_id.index(),
                    value orelse &.{},
                });
            }
        }
        self.visited_contexts[index].?.parameter_arguments = value;
    }

    fn setLoopValidationCache(
        self: *Builder,
        index: usize,
        epoch: usize,
        generation: usize,
        outcome: LoopValidationOutcome,
    ) BuildError!void {
        const epochs = self.loop_validation_epochs orelse return;
        const generations = self.loop_validation_generations orelse return;
        const outcomes = self.loop_validation_outcomes orelse return;
        if (self.mutation_depth != 0) {
            try self.mutation_log.append(self.allocator, .{ .validation = .{
                .index = index,
                .epoch = epochs[index],
                .generation = generations[index],
                .outcome = outcomes[index],
            } });
        }
        epochs[index] = epoch;
        generations[index] = generation;
        outcomes[index] = outcome;
    }

    fn installLoopMembership(self: *Builder, index: usize, installed: []bool) BuildError!void {
        const cache = self.loop_memberships orelse {
            self.allocator.free(installed);
            return error.UnsupportedShape;
        };
        if (self.mutation_depth != 0) {
            self.mutation_log.append(self.allocator, .{ .membership = .{
                .index = index,
                .value = cache[index],
                .installed = installed,
            } }) catch |err| {
                self.allocator.free(installed);
                return err;
            };
        }
        cache[index] = installed;
    }

    fn isEscapeTarget(targets: ?*const EscapeTarget, block: ir.BlockId) bool {
        var current = targets;
        while (current) |target| : (current = target.parent) {
            if (target.block == block) return true;
        }
        return false;
    }

    fn prependEscapeTarget(
        storage: *EscapeTarget,
        block: ir.BlockId,
        parent: ?*const EscapeTarget,
    ) *const EscapeTarget {
        storage.* = .{ .block = block, .parent = parent };
        return storage;
    }

    fn shadowEscapeTargetsAlloc(
        allocator: std.mem.Allocator,
        targets: ?*const EscapeTarget,
        owned_entry: ir.BlockId,
    ) BuildError!EscapeTargetProjection {
        var blocks: std.ArrayList(ir.BlockId) = .empty;
        defer blocks.deinit(allocator);
        var current = targets;
        var found = false;
        while (current) |target| : (current = target.parent) {
            if (target.block == owned_entry) {
                found = true;
            } else {
                try blocks.append(allocator, target.block);
            }
        }
        if (!found) return .{ .targets = targets };

        var owned_head: ?*EscapeTarget = null;
        current = targets;
        var owned_count: usize = 0;
        errdefer {
            var cleanup = EscapeTargetProjection{
                .targets = null,
                .owned_head = owned_head,
                .owned_count = owned_count,
            };
            cleanup.deinit(allocator);
        }
        var index = blocks.items.len;
        while (index != 0) {
            index -= 1;
            const clone = try allocator.create(EscapeTarget);
            clone.* = .{ .block = blocks.items[index], .parent = owned_head };
            owned_head = clone;
            owned_count += 1;
        }
        return .{
            .targets = owned_head,
            .owned_head = owned_head,
            .owned_count = owned_count,
        };
    }

    fn noteCollisionEdge(self: *Builder, reference: ir.CfgEdgeRef) void {
        const output = self.collision orelse return;
        if (output.*) |*collision| {
            if (collision.block == reference.target and collision.incoming == null) {
                collision.incoming = reference;
            }
        }
    }

    fn hasAuthenticatedContinuationBridge(
        self: *Builder,
        reference: ir.CfgEdgeRef,
    ) BuildError!bool {
        if (self.replay_context) |context| {
            return context.hasAuthenticatedContinuationBridgeForEdge(self.analysis, reference);
        }
        return structural_overlap.hasAuthenticatedContinuationBridgeForEdgeAlloc(
            self.allocator,
            self.analysis.program,
            self.analysis,
            reference,
        );
    }

    fn isParameterizedNumericTransitionHeader(
        program: *const ir.Program,
        block_id: ir.BlockId,
    ) bool {
        if (!structural_overlap.isIterationTransitionHeader(program, block_id)) return false;
        const block = program.blocks[block_id.index()];
        const instruction = program.instructions[block.instructions[0].index()];
        return switch (instruction.operation) {
            .numeric_for_next => true,
            else => false,
        };
    }

    // A numeric header owned by the current region may be re-entered from a
    // distinct internal tuple without changing its enclosing boundary. The
    // reentry may be reached from another region start or from the header's
    // own start; in both cases a canonical carrier must own the tuple and the
    // normalized iteration-state proof must reach that same carrier.
    fn authenticatedInternalDistinctNumericReentry(
        self: *Builder,
        current: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
        incoming: ?ir.CfgEdgeRef,
    ) BuildError!bool {
        if (parameters_match or
            context.start != current or
            context.stop != stop or
            context.loop_exit != loop_exit or
            context.continue_target != continue_target or
            !isParameterizedNumericTransitionHeader(self.analysis.program, current))
        {
            return false;
        }

        const reference = incoming orelse return false;
        if (reference.target != current or
            !try self.analysis.canReach(current, reference.source) or
            !try self.analysis.canReach(reference.source, current))
        {
            return false;
        }
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or
            !node_split.parametersAreCanonical(self.analysis.program.values, block))
        {
            return false;
        }
        const replay_context = self.replay_context orelse return false;
        return try replay_context.hasAuthenticatedNumericIterationCarrierReentryForEdge(
            self.analysis,
            current,
            reference,
        );
    }

    const InternalDistinctNumericReentryMutation = enum {
        valid,
        same_start,
        wrong_state,
        acyclic,
        noncanonical_carrier,
        mismatched_carrier_tuple,
    };

    fn internalDistinctNumericReentryWitness(
        mutation: InternalDistinctNumericReentryMutation,
    ) BuildError!bool {
        const allocator = std.testing.allocator;
        const function_id = ir.FunctionId.fromIndex(0);
        const entry = ir.BlockId.fromIndex(0);
        const header = ir.BlockId.fromIndex(1);
        const state_source = ir.BlockId.fromIndex(2);
        const carrier = ir.BlockId.fromIndex(3);
        const reentry_source = ir.BlockId.fromIndex(4);
        const exit = ir.BlockId.fromIndex(5);
        const function_parameter_0 = ir.ValueId.fromIndex(0);
        const function_parameter_1 = ir.ValueId.fromIndex(1);
        const function_parameter_2 = ir.ValueId.fromIndex(2);
        const function_parameter_3 = ir.ValueId.fromIndex(3);
        const header_control = ir.ValueId.fromIndex(4);
        const header_limit = ir.ValueId.fromIndex(5);
        const header_step = ir.ValueId.fromIndex(6);
        const header_initial = ir.ValueId.fromIndex(7);
        const carrier_parameter_0 = ir.ValueId.fromIndex(8);
        const carrier_parameter_1 = ir.ValueId.fromIndex(9);
        const carrier_parameter_2 = ir.ValueId.fromIndex(10);
        const carrier_parameter_3 = ir.ValueId.fromIndex(11);
        const false_value = ir.ValueId.fromIndex(12);
        const has_value = ir.ValueId.fromIndex(13);
        const normalized_limit = ir.ValueId.fromIndex(14);
        const normalized_step = ir.ValueId.fromIndex(15);
        const next_control = ir.ValueId.fromIndex(16);
        const false_instruction = ir.InstructionId.fromIndex(0);
        const transition_instruction = ir.InstructionId.fromIndex(1);
        var state_arguments = [_]ir.ValueId{
            next_control,
            normalized_limit,
            normalized_step,
            false_value,
        };
        var incoming_arguments = [_]ir.ValueId{
            carrier_parameter_0,
            carrier_parameter_1,
            carrier_parameter_2,
            carrier_parameter_3,
        };
        if (mutation == .wrong_state) state_arguments[0] = function_parameter_0;
        if (mutation == .mismatched_carrier_tuple) incoming_arguments[0] = function_parameter_0;

        var blocks = [_]ir.Block{
            .{ .id = entry, .function = function_id, .instructions = &.{false_instruction}, .terminator = .{ .jump = .{
                .target = header,
                .arguments = &.{ function_parameter_0, function_parameter_1, function_parameter_2, function_parameter_3 },
            } } },
            .{ .id = header, .function = function_id, .parameters = &.{
                header_control,
                header_limit,
                header_step,
                header_initial,
            }, .instructions = &.{transition_instruction}, .terminator = .{ .branch = .{
                .condition = has_value,
                .then_edge = .{ .target = state_source },
                .else_edge = .{ .target = exit },
            } } },
            .{ .id = state_source, .function = function_id, .terminator = .{ .jump = .{
                .target = carrier,
                .arguments = &state_arguments,
            } } },
            .{ .id = carrier, .function = function_id, .parameters = &.{
                carrier_parameter_0,
                carrier_parameter_1,
                carrier_parameter_2,
                carrier_parameter_3,
            }, .terminator = .{ .jump = .{ .target = reentry_source } } },
            .{ .id = reentry_source, .function = function_id, .terminator = .{ .jump = .{
                .target = header,
                .arguments = &incoming_arguments,
            } } },
            .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
        };
        if (mutation == .acyclic) {
            blocks[carrier.index()].terminator = .{ .jump = .{ .target = exit } };
        }

        var values = [_]ir.Value{
            .{ .id = function_parameter_0, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 0 } },
            .{ .id = function_parameter_1, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
            .{ .id = function_parameter_2, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } },
            .{ .id = function_parameter_3, .function = function_id, .type = .boolean, .origin = .{ .parameter = 3 } },
            .{ .id = header_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
            .{ .id = header_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header, .index = 1 } } },
            .{ .id = header_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header, .index = 2 } } },
            .{ .id = header_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = header, .index = 3 } } },
            .{ .id = carrier_parameter_0, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = carrier, .index = 0 } } },
            .{ .id = carrier_parameter_1, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = carrier, .index = 1 } } },
            .{ .id = carrier_parameter_2, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = carrier, .index = 2 } } },
            .{ .id = carrier_parameter_3, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = carrier, .index = 3 } } },
            .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_instruction, .index = 0 } } },
            .{ .id = has_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 0 } } },
            .{ .id = normalized_limit, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 1 } } },
            .{ .id = normalized_step, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 2 } } },
            .{ .id = next_control, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 3 } } },
        };
        if (mutation == .noncanonical_carrier) {
            values[carrier_parameter_0.index()].origin = .{ .parameter = 0 };
        }

        const function = ir.Function{
            .id = function_id,
            .parameters = &.{
                function_parameter_0,
                function_parameter_1,
                function_parameter_2,
                function_parameter_3,
            },
            .blocks = &.{ entry, header, state_source, carrier, reentry_source, exit },
            .entry_block = entry,
        };
        const instructions = [_]ir.Instruction{
            .{ .id = false_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
            .{ .id = transition_instruction, .block = header, .operation = .{ .numeric_for_next = .{
                .control = header_control,
                .limit = header_limit,
                .step = header_step,
                .initial = header_initial,
                .mode = .semantic_normalized,
            } }, .results = &.{ has_value, normalized_limit, normalized_step, next_control }, .effects = .numeric_for_next },
        };
        const program = ir.Program{
            .program_id = "internal-distinct-numeric-reentry-witness",
            .entry_function = function_id,
            .functions = &.{function},
            .blocks = &blocks,
            .instructions = &instructions,
            .values = &values,
        };
        var analysis = cfg.Analysis.init(allocator, &program, function) catch |err| switch (err) {
            error.InvalidCfg => return false,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer analysis.deinit();
        const loop_headers = try natural_loop.headerCandidatesAlloc(allocator, &analysis);
        defer allocator.free(loop_headers);
        var replay_context = try structural_overlap.ReplayProjectionContext.initForFunction(
            allocator,
            &program,
            function_id,
        );
        defer replay_context.deinit();
        var visited = [_]bool{ false, false, false, false, false, false };
        var contexts = [_]?Builder.VisitContext{ null, .{
            .start = header,
            .stop = exit,
            .loop_exit = null,
            .continue_target = null,
            .parameter_arguments = null,
        }, null, null, null, null };
        var builder: Builder = .{
            .allocator = allocator,
            .analysis = &analysis,
            .visited = &visited,
            .visited_contexts = &contexts,
            .loop_headers = loop_headers,
            .replay_context = &replay_context,
        };
        return try builder.authenticatedInternalDistinctNumericReentry(
            header,
            exit,
            null,
            null,
            contexts[header.index()].?,
            false,
            .{ .source = reentry_source, .kind = .jump, .target = header },
        );
    }

    test "internal distinct numeric reentry requires a carrier state proof" {
        try std.testing.expect(try internalDistinctNumericReentryWitness(.valid));
        try std.testing.expect(try internalDistinctNumericReentryWitness(.same_start));
        try std.testing.expect(!(try internalDistinctNumericReentryWitness(.wrong_state)));
        try std.testing.expect(!(try internalDistinctNumericReentryWitness(.acyclic)));
        try std.testing.expect(!(try internalDistinctNumericReentryWitness(.noncanonical_carrier)));
        try std.testing.expect(!(try internalDistinctNumericReentryWitness(.mismatched_carrier_tuple)));
    }

    // A zero-parameter loop header may be reached again from an internal
    // loop path after a different structured stop has been selected.  This
    // is not an empty projection: the header's instructions and branch still
    // execute, so the reuse is admitted only when the incoming edge is a
    // live replay bridge and the header owns an unambiguous natural-loop
    // entry.  The caller still requires the direct projection from the
    // immediately preceding structured node before transferring control.
    fn authenticatedZeroParameterLoopHeaderReentry(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
        incoming: ?ir.CfgEdgeRef,
    ) BuildError!bool {
        if (context.start == start or
            current == start or
            context.stop == stop or
            context.loop_exit != loop_exit or
            context.continue_target != continue_target or
            !parameters_match)
        {
            return false;
        }

        const reference = incoming orelse return false;
        if (reference.target != current or
            !try self.analysis.canReach(current, reference.source) or
            !try self.analysis.canReach(reference.source, current))
        {
            return false;
        }

        const local_index = self.analysis.blockIndex(current) orelse return false;
        if (local_index >= self.loop_headers.len or
            current.index() >= self.analysis.program.blocks.len)
        {
            return false;
        }
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or block.function != self.analysis.function.id or
            block.parameters.len != 0 or block.instructions.len == 0)
        {
            return false;
        }

        const edge = cfg_edge.value(self.analysis.program, reference) orelse return false;
        if (edge.target != current or edge.arguments.len != 0 or
            !try self.hasAuthenticatedContinuationBridge(reference))
        {
            return false;
        }

        var membership = if (self.loop_headers[local_index])
            try natural_loop.collect(self.allocator, self.analysis, current)
        else
            null;
        defer if (membership) |*owned| owned.deinit();
        const source_index = self.analysis.blockIndex(reference.source) orelse return false;
        if (membership == null or !membership.?.bits[source_index]) {
            if (membership) |*owned| owned.deinit();
            membership = try natural_loop.collectStronglyConnected(
                self.allocator,
                self.analysis,
                current,
            );
        }
        if (membership == null or !membership.?.bits[source_index]) return false;

        // A loop header must expose one owned backedge arm and one outside
        // arm.  Requiring this distinction keeps an altered or ambiguous
        // exit from being silently treated as the same loop owner.
        const branch = switch (block.terminator) {
            .branch => |value| value,
            .jump, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
        };
        const then_index = self.analysis.blockIndex(branch.then_edge.target) orelse return false;
        const else_index = self.analysis.blockIndex(branch.else_edge.target) orelse return false;
        const then_member = membership.?.bits[then_index];
        const else_member = membership.?.bits[else_index];
        if (then_member == else_member) return false;

        const then_block = self.analysis.program.blocks[branch.then_edge.target.index()];
        const else_block = self.analysis.program.blocks[branch.else_edge.target.index()];
        if (then_block.id != branch.then_edge.target or else_block.id != branch.else_edge.target or
            then_block.function != self.analysis.function.id or
            else_block.function != self.analysis.function.id or
            branch.then_edge.arguments.len != then_block.parameters.len or
            branch.else_edge.arguments.len != else_block.parameters.len)
        {
            return false;
        }
        return true;
    }

    const ZeroParameterLoopReentryMutation = enum {
        valid,
        unauthenticated,
        acyclic,
        invalid_header,
        ambiguous_exit,
    };

    fn zeroParameterLoopReentryWitness(
        mutation: ZeroParameterLoopReentryMutation,
    ) BuildError!bool {
        const allocator = std.testing.allocator;
        const function_id = ir.FunctionId.fromIndex(0);
        const entry = ir.BlockId.fromIndex(0);
        const owner_start = ir.BlockId.fromIndex(1);
        const incoming_start = ir.BlockId.fromIndex(2);
        const header = ir.BlockId.fromIndex(3);
        const body = ir.BlockId.fromIndex(4);
        const exit = ir.BlockId.fromIndex(5);
        const owner_stop = ir.BlockId.fromIndex(6);
        const incoming_stop = ir.BlockId.fromIndex(7);
        const original = ir.BlockId.fromIndex(8);
        const selector = ir.ValueId.fromIndex(0);
        const header_condition = ir.ValueId.fromIndex(1);
        const original_condition = ir.ValueId.fromIndex(2);
        const header_constant = ir.InstructionId.fromIndex(0);
        const original_constant = ir.InstructionId.fromIndex(1);
        const block_list = [_]ir.BlockId{
            entry,
            owner_start,
            incoming_start,
            header,
            body,
            exit,
            owner_stop,
            incoming_stop,
            original,
        };
        var blocks = [_]ir.Block{
            .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
                .condition = selector,
                .then_edge = .{ .target = owner_start },
                .else_edge = .{ .target = incoming_start },
            } } },
            .{ .id = owner_start, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
            .{ .id = incoming_start, .function = function_id, .terminator = .{ .jump = .{ .target = body } } },
            .{ .id = header, .function = function_id, .instructions = &.{header_constant}, .terminator = .{ .branch = .{
                .condition = header_condition,
                .then_edge = .{ .target = body },
                .else_edge = .{ .target = exit },
            } } },
            .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
            .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
            .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
            .{ .id = incoming_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
            .{ .id = original, .function = function_id, .instructions = &.{original_constant}, .terminator = .{ .branch = .{
                .condition = original_condition,
                .then_edge = .{ .target = body },
                .else_edge = .{ .target = exit },
            } } },
        };
        switch (mutation) {
            .valid, .unauthenticated => {},
            .acyclic => blocks[body.index()].terminator = .{ .jump = .{ .target = exit } },
            .invalid_header => blocks[header.index()].terminator = .{ .jump = .{ .target = body } },
            .ambiguous_exit => blocks[header.index()].terminator = .{ .branch = .{
                .condition = header_condition,
                .then_edge = .{ .target = body },
                .else_edge = .{ .target = body },
            } },
        }
        const function = ir.Function{
            .id = function_id,
            .parameters = &.{selector},
            .blocks = &block_list,
            .entry_block = entry,
        };
        const values = [_]ir.Value{
            .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
            .{ .id = header_condition, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = header_constant, .index = 0 } } },
            .{ .id = original_condition, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = original_constant, .index = 0 } } },
        };
        const instructions = [_]ir.Instruction{
            .{ .id = header_constant, .block = header, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{header_condition}, .effects = .pure },
            .{ .id = original_constant, .block = original, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{original_condition}, .effects = .pure },
        };
        const rewrites = [_]ir.CfgEdgeRewrite{.{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = body,
            .kind = .jump,
            .from = .{ .target = original },
            .to = .{ .target = header },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        }};
        const rewrite_slice: []const ir.CfgEdgeRewrite = if (mutation == .unauthenticated) &.{} else &rewrites;
        const program = ir.Program{
            .program_id = "zero-parameter-loop-reentry-witness",
            .entry_function = function_id,
            .functions = &.{function},
            .blocks = &blocks,
            .instructions = &instructions,
            .values = &values,
            .edge_rewrites = rewrite_slice,
        };
        var analysis = cfg.Analysis.init(allocator, &program, function) catch |err| switch (err) {
            error.InvalidCfg => return false,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer analysis.deinit();
        const loop_headers = try natural_loop.headerCandidatesAlloc(allocator, &analysis);
        defer allocator.free(loop_headers);
        const header_index = analysis.blockIndex(header) orelse return error.UnsupportedShape;
        const visited = try allocator.alloc(bool, function.blocks.len);
        defer allocator.free(visited);
        @memset(visited, false);
        visited[header_index] = true;
        const contexts = try allocator.alloc(?Builder.VisitContext, function.blocks.len);
        defer allocator.free(contexts);
        @memset(contexts, null);
        contexts[header_index] = .{
            .start = owner_start,
            .stop = owner_stop,
            .loop_exit = null,
            .continue_target = null,
            .parameter_arguments = &.{},
        };
        var builder: Builder = .{
            .allocator = allocator,
            .analysis = &analysis,
            .visited = visited,
            .visited_contexts = contexts,
            .loop_headers = loop_headers,
        };
        const reference: ir.CfgEdgeRef = .{ .source = body, .kind = .jump, .target = header };
        return try builder.authenticatedZeroParameterLoopHeaderReentry(
            header,
            incoming_start,
            incoming_stop,
            null,
            null,
            contexts[header_index].?,
            true,
            reference,
        );
    }

    test "zero-parameter loop reentry requires authenticated same-SCC ownership" {
        try std.testing.expect(try zeroParameterLoopReentryWitness(.valid));
        try std.testing.expect(!(try zeroParameterLoopReentryWitness(.unauthenticated)));
        try std.testing.expect(!(try zeroParameterLoopReentryWitness(.acyclic)));
        try std.testing.expect(!(try zeroParameterLoopReentryWitness(.invalid_header)));
        try std.testing.expect(!(try zeroParameterLoopReentryWitness(.ambiguous_exit)));
    }

    // A fully closed zero-parameter loop can be reached through the same
    // authenticated entry edge from a different structured prefix.  Reuse
    // the loop only when its natural region has one external entry, one
    // unique exit, and no edge that targets an enclosing control boundary.
    // The exact shared entry edge is sufficient for an unchanged owner; a
    // cloned entry still needs the ordinary continuation-bridge proof.
    fn authenticatedIndependentZeroParameterLoopReentry(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        context: VisitContext,
        parameters_match: bool,
        incoming: ?ir.CfgEdgeRef,
    ) BuildError!bool {
        if (!parameters_match or current == start or context.start == start or
            context.start == current or
            (context.stop == stop and context.loop_exit == loop_exit and
                context.continue_target == continue_target))
        {
            return false;
        }

        const reference = incoming orelse return false;
        if (reference.target != current) return false;
        const incoming_edge = cfg_edge.value(self.analysis.program, reference) orelse return false;
        if (incoming_edge.target != current or incoming_edge.arguments.len != 0) return false;

        const header_index = self.analysis.blockIndex(current) orelse return false;
        if (header_index >= self.loop_headers.len or !self.loop_headers[header_index]) return false;
        const header = self.analysis.program.blocks[current.index()];
        if (header.id != current or header.function != self.analysis.function.id or
            header.parameters.len != 0)
        {
            return false;
        }

        var membership = (try natural_loop.collect(self.allocator, self.analysis, current)) orelse return false;
        defer membership.deinit();
        const exit = switch (try natural_loop.classifyExit(self.analysis, membership.bits)) {
            .unique => |target| target,
            .closed, .multiple => return false,
        };
        if (exit == current or exit == stop or exit == loop_exit or exit == continue_target or
            isEscapeTarget(escape_targets, exit) or isEscapeTarget(continue_targets, exit))
        {
            return false;
        }

        const same_owner_entry = if (context.entry_reference) |owner| std.meta.eql(owner, reference) else false;
        if (!same_owner_entry and !try self.hasAuthenticatedContinuationBridge(reference)) return false;

        var entry_count: usize = 0;
        var incoming_is_entry = false;
        for (membership.bits, 0..) |is_member, local_index| {
            if (!is_member) continue;
            if (!self.visited[local_index]) return false;
            const block_id = self.analysis.function.blocks[local_index];
            const block = self.analysis.program.blocks[block_id.index()];
            if (block.id != block_id or block.function != self.analysis.function.id or
                block.parameters.len != 0)
            {
                return false;
            }
            for (0..self.analysis.predecessorCount(block_id)) |predecessor_index| {
                const predecessor = self.analysis.predecessorAt(block_id, predecessor_index) orelse return false;
                const predecessor_local = self.analysis.blockIndex(predecessor) orelse return false;
                if (membership.bits[predecessor_local] or !self.analysis.isReachable(predecessor)) continue;
                const entry = directEdgeReference(self.analysis.program, .{ .block = predecessor }, block_id) orelse return false;
                const edge = cfg_edge.value(self.analysis.program, entry) orelse return false;
                if (edge.target != block_id or edge.arguments.len != block.parameters.len) return false;
                entry_count += 1;
                if (std.meta.eql(entry, reference)) incoming_is_entry = true;
            }
        }
        if (entry_count != 1 or !incoming_is_entry) return false;

        for (membership.bits, 0..) |is_member, local_index| {
            if (!is_member) continue;
            const block_id = self.analysis.function.blocks[local_index];
            const block = self.analysis.program.blocks[block_id.index()];
            var outgoing: [2]?ir.Edge = .{ null, null };
            var outgoing_count: usize = 0;
            switch (block.terminator) {
                .jump => |edge| {
                    outgoing[0] = edge;
                    outgoing_count = 1;
                },
                .branch => |branch| {
                    outgoing[0] = branch.then_edge;
                    outgoing[1] = branch.else_edge;
                    outgoing_count = 2;
                },
                .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
            }
            for (outgoing[0..outgoing_count]) |maybe_edge| {
                const edge = maybe_edge orelse return false;
                const target_index = self.analysis.blockIndex(edge.target) orelse return false;
                const target_block = self.analysis.program.blocks[edge.target.index()];
                if (target_block.id != edge.target or target_block.function != self.analysis.function.id or
                    edge.arguments.len != target_block.parameters.len or
                    (!membership.bits[target_index] and edge.target != exit))
                {
                    return false;
                }
            }
        }

        const branch = switch (header.terminator) {
            .branch => |value| value,
            .jump, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
        };
        const then_index = self.analysis.blockIndex(branch.then_edge.target) orelse return false;
        const else_index = self.analysis.blockIndex(branch.else_edge.target) orelse return false;
        return membership.bits[then_index] != membership.bits[else_index];
    }

    const IndependentZeroParameterLoopReentryMutation = enum {
        valid,
        unauthenticated_entry,
        multiple_external_entries,
        outer_control_exit,
        unvisited_member,
    };

    fn independentZeroParameterLoopReentryWitness(
        mutation: IndependentZeroParameterLoopReentryMutation,
    ) BuildError!bool {
        const allocator = std.testing.allocator;
        const function_id = ir.FunctionId.fromIndex(0);
        const entry = ir.BlockId.fromIndex(0);
        const owner_entry = ir.BlockId.fromIndex(1);
        const second_entry = ir.BlockId.fromIndex(2);
        const header = ir.BlockId.fromIndex(3);
        const body = ir.BlockId.fromIndex(4);
        const exit = ir.BlockId.fromIndex(5);
        const stop = ir.BlockId.fromIndex(6);
        const selector = ir.ValueId.fromIndex(0);
        const header_condition = ir.ValueId.fromIndex(1);
        const header_instruction = ir.InstructionId.fromIndex(0);

        var blocks = [_]ir.Block{
            .{ .id = entry, .function = function_id, .terminator = switch (mutation) {
                .multiple_external_entries => .{ .branch = .{
                    .condition = selector,
                    .then_edge = .{ .target = owner_entry },
                    .else_edge = .{ .target = second_entry },
                } },
                else => .{ .jump = .{ .target = owner_entry } },
            } },
            .{ .id = owner_entry, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
            .{ .id = second_entry, .function = function_id, .terminator = switch (mutation) {
                .multiple_external_entries => .{ .jump = .{ .target = header } },
                else => .{ .return_values = &.{} },
            } },
            .{ .id = header, .function = function_id, .instructions = &.{header_instruction}, .terminator = .{ .branch = .{
                .condition = header_condition,
                .then_edge = .{ .target = body },
                .else_edge = .{ .target = exit },
            } } },
            .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
            .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
            .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        };
        const function = ir.Function{
            .id = function_id,
            .parameters = &.{selector},
            .blocks = &.{ entry, owner_entry, second_entry, header, body, exit, stop },
            .entry_block = entry,
        };
        const values = [_]ir.Value{
            .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
            .{ .id = header_condition, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = header_instruction, .index = 0 } } },
        };
        const instructions = [_]ir.Instruction{
            .{ .id = header_instruction, .block = header, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{header_condition}, .effects = .pure },
        };
        const program = ir.Program{
            .program_id = "independent-zero-parameter-loop-reentry-witness",
            .entry_function = function_id,
            .functions = &.{function},
            .blocks = &blocks,
            .instructions = &instructions,
            .values = &values,
        };
        var analysis = cfg.Analysis.init(allocator, &program, function) catch |err| switch (err) {
            error.InvalidCfg => return false,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer analysis.deinit();
        const loop_headers = try natural_loop.headerCandidatesAlloc(allocator, &analysis);
        defer allocator.free(loop_headers);
        const visited = try allocator.alloc(bool, function.blocks.len);
        defer allocator.free(visited);
        @memset(visited, false);
        visited[analysis.blockIndex(header).?] = true;
        visited[analysis.blockIndex(body).?] = mutation != .unvisited_member;
        const contexts = try allocator.alloc(?Builder.VisitContext, function.blocks.len);
        defer allocator.free(contexts);
        @memset(contexts, null);

        const owner_reference = ir.CfgEdgeRef{ .source = owner_entry, .kind = .jump, .target = header };
        contexts[analysis.blockIndex(header).?] = .{
            .start = owner_entry,
            .stop = stop,
            .loop_exit = null,
            .continue_target = null,
            .parameter_arguments = &.{},
            .entry_reference = if (mutation == .unauthenticated_entry) null else owner_reference,
        };
        var builder: Builder = .{
            .allocator = allocator,
            .analysis = &analysis,
            .visited = visited,
            .visited_contexts = contexts,
            .loop_headers = loop_headers,
        };
        var outer_escape: EscapeTarget = .{ .block = exit, .parent = null };
        const escape_targets = if (mutation == .outer_control_exit) &outer_escape else null;
        const incoming = if (mutation == .multiple_external_entries)
            ir.CfgEdgeRef{ .source = second_entry, .kind = .jump, .target = header }
        else
            owner_reference;
        return try builder.authenticatedIndependentZeroParameterLoopReentry(
            header,
            entry,
            null,
            null,
            null,
            escape_targets,
            null,
            contexts[analysis.blockIndex(header).?].?,
            true,
            incoming,
        );
    }

    fn reopenLoopHeader(self: *Builder, header_index: usize) BuildError!void {
        if (header_index >= self.visited.len or !self.visited[header_index] or self.visited_count == 0) return error.UnsupportedShape;
        if (self.validation_generation == std.math.maxInt(usize)) return error.UnsupportedShape;
        try self.unmarkVisited(header_index);
        self.validation_generation += 1;
    }

    fn validateNaturalLoopMembership(
        self: *Builder,
        header_index: usize,
        bits: []const bool,
        enclosing_allowed: ?[]const bool,
    ) BuildError!void {
        for (bits, 0..) |is_member, local_index| {
            if (!is_member) continue;
            if (enclosing_allowed) |allowed| {
                if (!allowed[local_index]) return error.UnsupportedShape;
            }
            if (local_index != header_index and self.visited[local_index]) {
                if (enclosing_allowed == null) {
                    try self.setLoopValidationCache(
                        header_index,
                        self.visited_count,
                        self.validation_generation,
                        .invalid,
                    );
                }
                return error.UnsupportedShape;
            }
        }
        if (enclosing_allowed == null) {
            try self.setLoopValidationCache(
                header_index,
                self.visited_count,
                self.validation_generation,
                .valid,
            );
        }
    }

    fn cachedLoopValidation(
        self: *const Builder,
        header_index: usize,
        enclosing_allowed: ?[]const bool,
    ) LoopValidationOutcome {
        if (enclosing_allowed != null or
            self.loop_validation_epochs == null or
            self.loop_validation_generations == null or
            self.loop_validation_outcomes == null) return .uncomputed;
        if (self.loop_validation_epochs.?[header_index] != self.visited_count or
            self.loop_validation_generations.?[header_index] != self.validation_generation) return .uncomputed;
        return self.loop_validation_outcomes.?[header_index];
    }

    fn isOutsideEntryToOwnedLoopHeader(
        self: *Builder,
        header: ir.BlockId,
        source: ir.BlockId,
    ) BuildError!bool {
        const header_index = self.analysis.blockIndex(header) orelse return error.UnsupportedShape;
        if (header_index >= self.loop_headers.len or !self.loop_headers[header_index]) return false;
        const owner = self.visited_contexts[header_index] orelse return false;
        if (owner.start != header or owner.stop != header or owner.continue_target != header) return false;
        const source_index = self.analysis.blockIndex(source) orelse return error.UnsupportedShape;
        if (self.loop_memberships) |cache| {
            const membership = if (cache[header_index]) |bits| bits else blk: {
                var collected = (try natural_loop.collect(self.allocator, self.analysis, header)) orelse return false;
                errdefer collected.deinit();
                const cached = try self.allocator.dupe(bool, collected.bits);
                collected.deinit();
                try self.installLoopMembership(header_index, cached);
                break :blk cached;
            };
            return !membership[source_index];
        }
        var membership = (try natural_loop.collect(self.allocator, self.analysis, header)) orelse return false;
        defer membership.deinit();
        return !membership.bits[source_index];
    }
};

test "independent zero-parameter loop reentry requires one authenticated entry" {
    try std.testing.expect(try Builder.independentZeroParameterLoopReentryWitness(.valid));
    try std.testing.expect(!(try Builder.independentZeroParameterLoopReentryWitness(.unauthenticated_entry)));
    try std.testing.expect(!(try Builder.independentZeroParameterLoopReentryWitness(.multiple_external_entries)));
    try std.testing.expect(!(try Builder.independentZeroParameterLoopReentryWitness(.outer_control_exit)));
    try std.testing.expect(!(try Builder.independentZeroParameterLoopReentryWitness(.unvisited_member)));
}

test "owned loop header projection distinguishes preheaders from backedges" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const latch = ir.BlockId.fromIndex(2);
    const terminal = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = latch } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = terminal },
        } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ preheader, header, latch, terminal },
        .entry_block = preheader,
    }};
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program: ir.Program = .{
        .program_id = "owned-loop-header-entry",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);
    var visited = [_]bool{ false, true, true, false };
    var contexts = [_]?Builder.VisitContext{ null, .{
        .start = header,
        .stop = header,
        .loop_exit = terminal,
        .continue_target = header,
    }, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };

    try std.testing.expect(try builder.isOutsideEntryToOwnedLoopHeader(header, preheader));
    try std.testing.expect(!try builder.isOutsideEntryToOwnedLoopHeader(header, latch));
}

fn nodeIncomingEdgesAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    node: Node,
    target: ir.BlockId,
) std.mem.Allocator.Error![]ir.CfgEdgeRef {
    var incoming: std.ArrayList(ir.CfgEdgeRef) = .empty;
    defer incoming.deinit(allocator);
    for (0..analysis.predecessorCount(target)) |index| {
        const predecessor = analysis.predecessorAt(target, index) orelse continue;
        if (!nodeOwnsBlock(node, predecessor)) continue;
        const reference = directEdgeReference(analysis.program, .{ .block = predecessor }, target) orelse continue;
        try incoming.append(allocator, reference);
    }
    return incoming.toOwnedSlice(allocator);
}

// A multi-entry clone may carry several authenticated continuations into the
// same target. Keep only the argument class that belongs to the collision
// being repaired; unrelated entry tuples must remain on their own lineage.
fn narrowIncomingGroupByArgumentsAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    group: []ir.CfgEdgeRef,
    representative: ir.CfgEdgeRef,
) std.mem.Allocator.Error![]ir.CfgEdgeRef {
    const representative_edge = cfg_edge.value(program, representative) orelse return group;
    var matching_count: usize = 0;
    for (group) |reference| {
        const edge = cfg_edge.value(program, reference) orelse return group;
        if (std.mem.eql(ir.ValueId, edge.arguments, representative_edge.arguments)) matching_count += 1;
    }
    if (matching_count == group.len) return group;

    const narrowed = try allocator.alloc(ir.CfgEdgeRef, matching_count);
    var index: usize = 0;
    for (group) |reference| {
        const edge = cfg_edge.value(program, reference) orelse continue;
        if (!std.mem.eql(ir.ValueId, edge.arguments, representative_edge.arguments)) continue;
        narrowed[index] = reference;
        index += 1;
    }
    allocator.free(group);
    return narrowed;
}

fn collisionContextsMatch(
    left: ?CollisionContext,
    right: ?CollisionContext,
) bool {
    // Missing visit context is not evidence that two incoming edges differ.
    // Preserve the group until an authenticated context exists on both sides.
    const left_context = left orelse return true;
    const right_context = right orelse return true;
    if (left_context.start != right_context.start or
        left_context.stop != right_context.stop or
        left_context.loop_exit != right_context.loop_exit or
        left_context.continue_target != right_context.continue_target) return false;
    if (left_context.parameter_arguments == null or right_context.parameter_arguments == null) return true;
    return std.mem.eql(ir.ValueId, left_context.parameter_arguments.?, right_context.parameter_arguments.?);
}

test "collision group partitions distinct incoming argument tuples" {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const first = ir.BlockId.fromIndex(0);
    const second = ir.BlockId.fromIndex(1);
    const third = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const first_argument = ir.ValueId.fromIndex(10);
    const second_argument = ir.ValueId.fromIndex(11);
    const first_arguments = [_]ir.ValueId{first_argument};
    const second_arguments = [_]ir.ValueId{second_argument};
    const blocks = [_]ir.Block{
        .{ .id = first, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &first_arguments,
        } } },
        .{ .id = second, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &second_arguments,
        } } },
        .{ .id = third, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &first_arguments,
        } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ first, second, third, target },
        .entry_block = first,
    };
    const program = ir.Program{
        .program_id = "collision-group-argument-classes",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var group = try allocator.alloc(ir.CfgEdgeRef, 3);
    group[0] = .{ .source = first, .kind = .jump, .target = target };
    group[1] = .{ .source = second, .kind = .jump, .target = target };
    group[2] = .{ .source = third, .kind = .jump, .target = target };

    const narrowed = try narrowIncomingGroupByArgumentsAlloc(allocator, &program, group, group[0]);
    defer allocator.free(narrowed);
    try std.testing.expectEqual(@as(usize, 2), narrowed.len);
    try std.testing.expectEqual(first, narrowed[0].source);
    try std.testing.expectEqual(third, narrowed[1].source);
}

test "collision context partition requires authenticated visit context" {
    const first = CollisionContext{
        .start = ir.BlockId.fromIndex(1),
        .stop = ir.BlockId.fromIndex(2),
        .loop_exit = null,
        .continue_target = null,
    };
    const same = CollisionContext{
        .start = ir.BlockId.fromIndex(1),
        .stop = ir.BlockId.fromIndex(2),
        .loop_exit = null,
        .continue_target = null,
    };
    const different = CollisionContext{
        .start = ir.BlockId.fromIndex(3),
        .stop = ir.BlockId.fromIndex(2),
        .loop_exit = null,
        .continue_target = null,
    };
    try std.testing.expect(collisionContextsMatch(first, same));
    try std.testing.expect(!collisionContextsMatch(first, different));
    try std.testing.expect(collisionContextsMatch(first, null));
}

fn nodeOwnsBlock(node: Node, target: ir.BlockId) bool {
    if (node.blockId() == target) return true;
    return switch (node) {
        .branch => |branch| regionOwnsBlock(branch.then_region, target) or regionOwnsBlock(branch.else_region, target),
        .loop => |loop| regionOwnsBlock(loop.body_region, target),
        .latch_loop => |loop| regionOwnsBlock(loop.body_region, target),
        .infinite_loop => |loop| regionOwnsBlock(loop.body_region, target) or
            (loop.shared_side_exit != null and sharedSideExitOwnsBlock(loop.shared_side_exit.?, target)),
        .loop_boundary => |control| regionOwnsBlock(control.body_region, target) or switch (control.boundary) {
            .side_exit => |side| regionOwnsBlock(side.region, target),
            .side_escape => |side| regionOwnsBlock(side.region, target),
            else => false,
        },
        .block, .loop_control, .loop_terminal => false,
    };
}

fn sharedSideExitOwnsBlock(side_exit: SharedSideExit, target: ir.BlockId) bool {
    for (side_exit.entries) |entry| {
        if (regionOwnsBlock(entry.region, target)) return true;
    }
    return false;
}

fn sharedSideExitHasTerminalJoinEscapedAcrossArms(
    program: *const ir.Program,
    side_exit: SharedSideExit,
    other: *const Region,
) bool {
    for (side_exit.entries) |entry| {
        if (regionHasTerminalJoinEscapedAcrossArms(program, entry.region, other)) return true;
    }
    return false;
}

fn sharedSideExitEscapesTo(side_exit: SharedSideExit, target: ir.BlockId) bool {
    for (side_exit.entries) |entry| {
        if (regionEscapesTo(entry.region, target)) return true;
    }
    return false;
}

fn regionOwnsBlock(region: *const Region, target: ir.BlockId) bool {
    for (region.nodes) |node| if (nodeOwnsBlock(node, target)) return true;
    return false;
}

fn appendBoundaryTarget(
    allocator: std.mem.Allocator,
    boundaries: *std.ArrayList(ir.BlockId),
    target: ir.BlockId,
) std.mem.Allocator.Error!void {
    for (boundaries.items) |existing| if (existing == target) return;
    try boundaries.append(allocator, target);
}

fn directEdgeReference(program: *const ir.Program, node: Node, target: ir.BlockId) ?ir.CfgEdgeRef {
    const source = switch (node) {
        .block => |block_id| block_id,
        else => return null,
    };
    if (source.index() >= program.blocks.len) return null;
    return switch (program.blocks[source.index()].terminator) {
        .jump => |edge| if (edge.target == target)
            .{ .source = source, .kind = .jump, .target = target }
        else
            null,
        .branch => |branch| if (branch.then_edge.target == target and branch.else_edge.target != target)
            .{ .source = source, .kind = .branch_then, .target = target }
        else if (branch.else_edge.target == target and branch.then_edge.target != target)
            .{ .source = source, .kind = .branch_else, .target = target }
        else
            null,
        else => null,
    };
}

fn makeLoopControl(block: ir.BlockId, branch: ir.Branch, continue_target: ir.BlockId, exit_target: ir.BlockId) ?LoopControl {
    if (branch.then_edge.target == continue_target and branch.else_edge.target == exit_target) {
        return .{
            .block = block,
            .continue_edge = branch.then_edge,
            .exit_edge = branch.else_edge,
            .continue_on_true = true,
        };
    }
    if (branch.else_edge.target == continue_target and branch.then_edge.target == exit_target) {
        return .{
            .block = block,
            .continue_edge = branch.else_edge,
            .exit_edge = branch.then_edge,
            .continue_on_true = false,
        };
    }
    return null;
}

fn sharedOwnsBlock(shared: *const loop_exit_shape.SharedPaths, block_id: ir.BlockId) bool {
    for (shared.blocks) |candidate| if (candidate == block_id) return true;
    return false;
}

fn isTerminal(terminator: ir.Terminator) bool {
    return switch (terminator) {
        .return_values, .return_pack, .return_expanded, .throw_error => true,
        .jump, .branch, .unreachable_block => false,
    };
}

const FinalContinueProjection = union(enum) {
    edge: ir.Edge,
    transferred,
};

fn finalContinueProjection(program: *const ir.Program, node: Node, target: ir.BlockId) ?FinalContinueProjection {
    return switch (node) {
        .block => |block_id| edge: {
            if (block_id.index() >= program.blocks.len) return null;
            const jump = switch (program.blocks[block_id.index()].terminator) {
                .jump => |jump| jump,
                else => return null,
            };
            break :edge if (jump.target == target) .{ .edge = jump } else null;
        },
        .branch => |branch| if (branch.join != null and branch.join.? == target) .transferred else null,
        .loop => |loop| if (loop.exit_edge.target == target) .{ .edge = loop.exit_edge } else null,
        .latch_loop => |loop| if (loop.exit == target) .transferred else null,
        .infinite_loop => |loop| if (loop.exit != null and loop.exit.? == target) .transferred else null,
        else => null,
    };
}

fn regionFallsThroughTo(program: *const ir.Program, region: *const Region, target: ir.BlockId) bool {
    if (region.stop == null or region.stop.? != target or
        region.terminal_projection != null or
        region.continue_projection != null or
        region.escape_projection != null)
    {
        return false;
    }
    if (region.nodes.len == 0 or region.stop_forwarding != null) return true;
    return nodeFallsThroughTo(program, region.nodes[region.nodes.len - 1], target);
}

fn regionHasTerminalJoinEscapedAcrossArms(
    program: *const ir.Program,
    owner: *const Region,
    other: *const Region,
) bool {
    for (owner.nodes) |node| {
        if (nodeHasTerminalJoinEscapedAcrossArms(program, node, other)) return true;
    }
    return false;
}

fn nodeHasTerminalJoinEscapedAcrossArms(
    program: *const ir.Program,
    node: Node,
    other: *const Region,
) bool {
    return switch (node) {
        .block, .loop_control, .loop_terminal => false,
        .branch => |branch| {
            if (branch.join) |join| {
                if (join.index() < program.blocks.len and
                    isTerminal(program.blocks[join.index()].terminator) and
                    regionEscapesTo(other, join)) return true;
            }
            return regionHasTerminalJoinEscapedAcrossArms(program, branch.then_region, other) or
                regionHasTerminalJoinEscapedAcrossArms(program, branch.else_region, other);
        },
        .loop => |loop| regionHasTerminalJoinEscapedAcrossArms(program, loop.body_region, other),
        .latch_loop => |loop| regionHasTerminalJoinEscapedAcrossArms(program, loop.body_region, other),
        .infinite_loop => |loop| regionHasTerminalJoinEscapedAcrossArms(program, loop.body_region, other) or
            (loop.shared_side_exit != null and
                sharedSideExitHasTerminalJoinEscapedAcrossArms(program, loop.shared_side_exit.?, other)),
        .loop_boundary => |control| {
            if (regionHasTerminalJoinEscapedAcrossArms(program, control.body_region, other)) return true;
            return switch (control.boundary) {
                .side_exit => |side| regionHasTerminalJoinEscapedAcrossArms(program, side.region, other),
                .side_escape => |side| regionHasTerminalJoinEscapedAcrossArms(program, side.region, other),
                .exit, .escape, .terminal, .shared_exit => false,
            };
        },
    };
}

fn nodeFallsThroughTo(program: *const ir.Program, node: Node, target: ir.BlockId) bool {
    return switch (node) {
        .branch => |branch| if (branch.join) |join|
            join == target
        else
            regionFallsThroughTo(program, branch.then_region, target) or
                regionFallsThroughTo(program, branch.else_region, target),
        else => finalContinueProjection(program, node, target) != null,
    };
}

fn nodesEscapeTo(nodes: []const Node, target: ir.BlockId) bool {
    for (nodes) |node| if (nodeEscapesTo(node, target)) return true;
    return false;
}

fn regionEscapesTo(region: *const Region, target: ir.BlockId) bool {
    if (region.stop != null and region.stop.? == target) return false;
    return (region.escape_projection != null and region.escape_projection.?.target == target) or
        (region.continue_projection != null and
            region.continue_projection.?.target == target and
            (region.continue_target == null or region.continue_target.? != target)) or
        nodesEscapeTo(region.nodes, target);
}

fn nodeEscapesTo(node: Node, target: ir.BlockId) bool {
    return switch (node) {
        .block, .loop_control, .loop_terminal => false,
        .branch => |branch| regionEscapesTo(branch.then_region, target) or
            regionEscapesTo(branch.else_region, target),
        .loop => |loop| (loop.exit_is_escape and loop.exit_edge.target == target) or
            regionEscapesTo(loop.body_region, target),
        .latch_loop => |loop| (loop.exit_is_escape and loop.exit == target) or
            regionEscapesTo(loop.body_region, target),
        .infinite_loop => |loop| (loop.exit_is_escape and loop.exit != null and loop.exit.? == target) or
            regionEscapesTo(loop.body_region, target) or
            (loop.shared_side_exit != null and sharedSideExitEscapesTo(loop.shared_side_exit.?, target)),
        .loop_boundary => |control| boundary: {
            if (regionEscapesTo(control.body_region, target)) break :boundary true;
            break :boundary switch (control.boundary) {
                .escape => |edge| edge.target == target,
                .side_exit => |side| regionEscapesTo(side.region, target),
                .side_escape => |side| side.target == target or regionEscapesTo(side.region, target),
                .exit, .terminal, .shared_exit => false,
            };
        },
    };
}

fn nodeHasLoopBoundaryExitTo(node: Node, target: ir.BlockId) bool {
    return switch (node) {
        .block, .loop_control, .loop_terminal => false,
        .branch => |branch| regionHasLoopBoundaryExitTo(branch.then_region, target) or
            regionHasLoopBoundaryExitTo(branch.else_region, target),
        .loop => |loop| regionHasLoopBoundaryExitTo(loop.body_region, target),
        .latch_loop => |loop| regionHasLoopBoundaryExitTo(loop.body_region, target),
        .infinite_loop => |loop| regionHasLoopBoundaryExitTo(loop.body_region, target) or
            (loop.shared_side_exit != null and
                sharedSideExitHasLoopBoundaryExitTo(loop.shared_side_exit.?, target)),
        .loop_boundary => |control| {
            if (regionHasLoopBoundaryExitTo(control.body_region, target)) return true;
            return switch (control.boundary) {
                .exit => |edge| edge.target == target,
                .side_exit => |side| regionHasLoopBoundaryExitTo(side.region, target),
                .side_escape => |side| regionHasLoopBoundaryExitTo(side.region, target),
                .escape, .terminal, .shared_exit => false,
            };
        },
    };
}

fn sharedSideExitHasLoopBoundaryExitTo(side_exit: SharedSideExit, target: ir.BlockId) bool {
    for (side_exit.entries) |entry| {
        if (regionHasLoopBoundaryExitTo(entry.region, target)) return true;
    }
    return false;
}

fn collectLoopBoundaryExitTargets(
    allocator: std.mem.Allocator,
    region: *const Region,
    targets: *std.AutoHashMapUnmanaged(ir.BlockId, void),
) std.mem.Allocator.Error!void {
    for (region.nodes) |node| try collectNodeLoopBoundaryExitTargets(allocator, node, targets);
}

fn collectNodeLoopBoundaryExitTargets(
    allocator: std.mem.Allocator,
    node: Node,
    targets: *std.AutoHashMapUnmanaged(ir.BlockId, void),
) std.mem.Allocator.Error!void {
    switch (node) {
        .block, .loop_control, .loop_terminal => {},
        .branch => |branch| {
            try collectLoopBoundaryExitTargets(allocator, branch.then_region, targets);
            try collectLoopBoundaryExitTargets(allocator, branch.else_region, targets);
        },
        .loop => |loop| try collectLoopBoundaryExitTargets(allocator, loop.body_region, targets),
        .latch_loop => |loop| try collectLoopBoundaryExitTargets(allocator, loop.body_region, targets),
        .infinite_loop => |loop| {
            try collectLoopBoundaryExitTargets(allocator, loop.body_region, targets);
            if (loop.shared_side_exit) |side_exit| {
                for (side_exit.entries) |entry| {
                    try collectLoopBoundaryExitTargets(allocator, entry.region, targets);
                }
            }
        },
        .loop_boundary => |control| {
            try collectLoopBoundaryExitTargets(allocator, control.body_region, targets);
            switch (control.boundary) {
                .exit => |edge| try targets.put(allocator, edge.target, {}),
                .side_exit => |side| try collectLoopBoundaryExitTargets(allocator, side.region, targets),
                .side_escape => |side| try collectLoopBoundaryExitTargets(allocator, side.region, targets),
                .escape, .terminal, .shared_exit => {},
            }
        },
    }
}

fn collectRegionFreeTargets(
    allocator: std.mem.Allocator,
    region: *const Region,
    captures: ?*const FreeTargetCapture,
    targets: *std.AutoHashMapUnmanaged(ir.BlockId, void),
) std.mem.Allocator.Error!void {
    var own_capture: FreeTargetCapture = undefined;
    const nested_captures = if (region.stop) |target| nested: {
        own_capture = .{ .target = target, .parent = captures };
        break :nested &own_capture;
    } else captures;
    for (region.nodes) |node| try collectNodeFreeTargets(allocator, node, nested_captures, targets);
    if (region.escape_projection) |projection| {
        try addFreeTarget(allocator, targets, nested_captures, projection.target);
    }
    if (region.continue_projection) |projection| {
        if (region.continue_target == null or region.continue_target.? != projection.target) {
            try addFreeTarget(allocator, targets, nested_captures, projection.target);
        }
    }
}

fn collectNodeFreeTargets(
    allocator: std.mem.Allocator,
    node: Node,
    captures: ?*const FreeTargetCapture,
    targets: *std.AutoHashMapUnmanaged(ir.BlockId, void),
) std.mem.Allocator.Error!void {
    switch (node) {
        .block, .loop_control, .loop_terminal => {},
        .branch => |branch| {
            try collectRegionFreeTargets(allocator, branch.then_region, captures, targets);
            try collectRegionFreeTargets(allocator, branch.else_region, captures, targets);
        },
        .loop, .latch_loop, .infinite_loop => try collectLoopFreeTargets(allocator, node, captures, targets),
        .loop_boundary => |control| {
            try collectRegionFreeTargets(allocator, control.body_region, captures, targets);
            switch (control.boundary) {
                .escape => |edge| try addFreeTarget(allocator, targets, captures, edge.target),
                .side_exit => |side| try collectRegionFreeTargets(allocator, side.region, captures, targets),
                .side_escape => |side| {
                    try collectRegionFreeTargets(allocator, side.region, captures, targets);
                    try addFreeTarget(allocator, targets, captures, side.target);
                },
                .exit, .terminal, .shared_exit => {},
            }
        },
    }
}

fn collectLoopFreeTargets(
    allocator: std.mem.Allocator,
    node: Node,
    captures: ?*const FreeTargetCapture,
    targets: *std.AutoHashMapUnmanaged(ir.BlockId, void),
) std.mem.Allocator.Error!void {
    switch (node) {
        .loop => |loop| {
            var loop_capture: FreeTargetCapture = undefined;
            const body_captures = if (!loop.exit_is_escape)
                capturesWithOwnedExit(captures, loop.exit_edge.target, &loop_capture)
            else
                captures;
            if (loop.exit_is_escape) try addFreeTarget(allocator, targets, captures, loop.exit_edge.target);
            try collectRegionFreeTargets(allocator, loop.body_region, body_captures, targets);
        },
        .latch_loop => |loop| {
            var loop_capture: FreeTargetCapture = undefined;
            const body_captures = if (!loop.exit_is_escape)
                capturesWithOwnedExit(captures, loop.exit, &loop_capture)
            else
                captures;
            if (loop.exit_is_escape) try addFreeTarget(allocator, targets, captures, loop.exit);
            try collectRegionFreeTargets(allocator, loop.body_region, body_captures, targets);
        },
        .infinite_loop => |loop| {
            var loop_capture: FreeTargetCapture = undefined;
            const loop_captures = if (!loop.exit_is_escape and loop.exit != null)
                capturesWithOwnedExit(captures, loop.exit.?, &loop_capture)
            else
                captures;
            if (loop.exit_is_escape) try addFreeTarget(allocator, targets, captures, loop.exit.?);
            var side_captures: []FreeTargetCapture = &.{};
            defer if (side_captures.len != 0) allocator.free(side_captures);
            const body_captures = if (loop.shared_side_exit) |side| captured: {
                side_captures = try allocator.alloc(FreeTargetCapture, side.entries.len);
                for (side_captures, 0..) |*capture, index| {
                    capture.* = .{
                        .target = side.entries[index].entry,
                        .parent = if (index + 1 < side_captures.len)
                            &side_captures[index + 1]
                        else
                            loop_captures,
                    };
                }
                break :captured if (side_captures.len == 0) loop_captures else &side_captures[0];
            } else loop_captures;
            try collectRegionFreeTargets(allocator, loop.body_region, body_captures, targets);
            if (loop.shared_side_exit) |side| {
                for (side.entries) |entry| {
                    try collectRegionFreeTargets(allocator, entry.region, captures, targets);
                }
            }
        },
        else => unreachable,
    }
}

fn capturesWithOwnedExit(
    captures: ?*const FreeTargetCapture,
    target: ir.BlockId,
    storage: *FreeTargetCapture,
) ?*const FreeTargetCapture {
    storage.* = .{ .target = target, .parent = captures };
    return storage;
}

fn addFreeTarget(
    allocator: std.mem.Allocator,
    targets: *std.AutoHashMapUnmanaged(ir.BlockId, void),
    captures: ?*const FreeTargetCapture,
    target: ir.BlockId,
) std.mem.Allocator.Error!void {
    var current = captures;
    while (current) |capture| : (current = capture.parent) {
        if (capture.target == target) return;
    }
    try targets.put(allocator, target, {});
}

fn sortedFreeTargetsAlloc(
    allocator: std.mem.Allocator,
    targets: *const std.AutoHashMapUnmanaged(ir.BlockId, void),
) std.mem.Allocator.Error![]ir.BlockId {
    const result = try allocator.alloc(ir.BlockId, targets.count());
    var iterator = targets.keyIterator();
    var index: usize = 0;
    while (iterator.next()) |target| : (index += 1) result[index] = target.*;
    std.mem.sort(ir.BlockId, result, {}, struct {
        fn lessThan(_: void, left: ir.BlockId, right: ir.BlockId) bool {
            return left.index() < right.index();
        }
    }.lessThan);
    return result;
}

fn finishRegion(
    allocator: std.mem.Allocator,
    region: *Region,
    nodes: *std.ArrayList(Node),
    stop: ?ir.BlockId,
    loop_exit: ?ir.BlockId,
    continue_target: ?ir.BlockId,
) !*Region {
    region.* = .{
        .nodes = try nodes.toOwnedSlice(allocator),
        .stop = stop,
        .loop_exit = loop_exit,
        .continue_target = continue_target,
    };
    return region;
}

fn destroyNodeList(allocator: std.mem.Allocator, nodes: *std.ArrayList(Node)) void {
    for (nodes.items) |node| switch (node) {
        .branch => |branch| destroyBranch(allocator, branch),
        .loop => |loop| destroyRegion(allocator, loop.body_region),
        .latch_loop => |loop| destroyLatchLoop(allocator, loop),
        .infinite_loop => |loop| destroyInfiniteLoop(allocator, loop),
        .loop_control => {},
        .loop_boundary => |control| destroyLoopBoundaryControl(allocator, control),
        .loop_terminal => {},
        .block => {},
    };
    nodes.deinit(allocator);
}

fn destroyRegion(allocator: std.mem.Allocator, region: *Region) void {
    for (region.nodes) |node| switch (node) {
        .branch => |branch| destroyBranch(allocator, branch),
        .loop => |loop| destroyRegion(allocator, loop.body_region),
        .latch_loop => |loop| destroyLatchLoop(allocator, loop),
        .infinite_loop => |loop| destroyInfiniteLoop(allocator, loop),
        .loop_control => {},
        .loop_boundary => |control| destroyLoopBoundaryControl(allocator, control),
        .loop_terminal => {},
        .block => {},
    };
    if (region.continue_projection) |*projection| {
        if (projection.forwarding) |*path| path.deinit(allocator);
    }
    allocator.free(region.nodes);
    allocator.destroy(region);
}

fn destroyBranch(allocator: std.mem.Allocator, branch: Branch) void {
    destroyEdgeOverride(allocator, branch.then_edge_override);
    destroyEdgeOverride(allocator, branch.else_edge_override);
    destroyRegion(allocator, branch.then_region);
    destroyRegion(allocator, branch.else_region);
}

fn destroyLatchLoop(allocator: std.mem.Allocator, loop: LatchLoop) void {
    destroyRegion(allocator, loop.body_region);
    if (loop.shared_reentries) |paths| paths.deinit(allocator);
    if (loop.shared_exits) |paths| paths.deinit(allocator);
}

fn destroyInfiniteLoop(allocator: std.mem.Allocator, loop: InfiniteLoop) void {
    destroyRegion(allocator, loop.body_region);
    if (loop.shared_side_exit) |side_exit| destroySharedSideExit(allocator, side_exit);
}

fn destroySharedSideExit(allocator: std.mem.Allocator, side_exit: SharedSideExit) void {
    for (side_exit.entries) |entry| destroyRegion(allocator, entry.region);
    allocator.free(side_exit.entries);
}

fn destroyEdgeOverride(allocator: std.mem.Allocator, edge_override: ?EdgeOverride) void {
    if (edge_override) |value| switch (value) {
        .history_cut => {},
        .forwarding => |forwarding| {
            var path = forwarding;
            path.deinit(allocator);
        },
    };
}

fn destroyLoopBoundaryControl(allocator: std.mem.Allocator, control: LoopBoundaryControl) void {
    destroyRegion(allocator, control.body_region);
    destroyLoopBoundary(allocator, control.boundary);
}

fn destroyLoopBoundary(allocator: std.mem.Allocator, boundary: LoopBoundary) void {
    switch (boundary) {
        .side_exit => |side_exit| destroyRegion(allocator, side_exit.region),
        .side_escape => |side_escape| destroyRegion(allocator, side_escape.region),
        .exit, .escape, .terminal, .shared_exit => {},
    }
}
