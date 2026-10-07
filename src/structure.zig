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

fn sharedSideExitEscapesTo(side_exit: SharedSideExit, target: ir.BlockId) bool {
    for (side_exit.entries) |entry| {
        if (regionEscapesTo(entry.region, target)) return true;
    }
    return false;
}

const FinalContinueProjection = union(enum) {
    edge: ir.Edge,
    transferred,
};

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
