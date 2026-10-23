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
const stage_trace = @import("stage_trace.zig");

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
    /// The plan escapes to a block that no enclosing region stop or owned
    /// loop exit consumes; the gate closes "root escape target consumed",
    /// not "each CFG edge realized".
    unowned_escape_target,
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
    /// A continue to the region's own continue target carried by an escape flag instead of a lexical `continue`,
    /// because the innermost Luau loop statement around its writer is a transfer wrapper that stops at another
    /// block (`markFlaggedContinues`). The escape census counts it as it counts a nonlocal continue.
    via_flag: bool = false,
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

fn containsBlockId(blocks: []const ir.BlockId, target: ir.BlockId) bool {
    for (blocks) |block| if (block == target) return true;
    return false;
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
    /// The body region's exit continue, to the holding region's continue target, which is also the body region's stop,
    /// carried by an escape flag instead of a lexical `continue`, because the innermost Luau loop statement around its
    /// writer is a transfer wrapper that stops at another block (`markFlaggedContinues`). The escape census counts it as
    /// an escape to the body region's stop.
    continue_via_flag: bool = false,
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

fn lessArbitraryNode(_: void, left: Node, right: Node) bool {
    return left.blockId().index() < right.blockId().index();
}

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
        if (continueProjectionUsesFlag(region, projection)) return true;
    }
    return nodesEscapeTo(region.nodes, target);
}

/// Whether a region's continue projection is written as an escape flag, which every transfer wrapper on the way
/// forwards and the loop body's wrapper consumes as a `continue`, rather than as a lexical `continue`: its target is
/// not the region's continue target, or `markFlaggedContinues` found that a lexical `continue` would bind to a
/// wrapper that stops at another block.
fn continueProjectionUsesFlag(region: *const Region, projection: ContinueProjection) bool {
    return region.continue_target == null or region.continue_target.? != projection.target or projection.via_flag;
}

/// A Luau loop statement the readable writers put around a region's text, as `markFlaggedContinues` models it: a
/// transfer wrapper (`repeat ... until true`), whose end reaches `stop`, or a loop, whose next pass starts at `header`
/// (`stop` is its body region's stop). `parent` is the statement around it.
const EnclosingStatement = struct {
    kind: enum { wrapper, loop },
    header: ?ir.BlockId = null,
    stop: ?ir.BlockId = null,
    parent: ?*const EnclosingStatement = null,
};

/// Marks each continue projection to its region's own continue target whose writer would put a lexical `continue`
/// inside a transfer wrapper (`repeat ... until true`) that stops at another block: Luau binds that `continue` to the
/// wrapper, and leaving the wrapper reaches its stop, not the loop's next pass. A marked projection is carried by an
/// escape flag (`ContinueProjection.via_flag`), and the escape census counts it as it counts a nonlocal continue, so
/// the writer sets the flag and leaves its wrapper, each wrapper on the way forwards the flag, and the loop body's
/// wrapper consumes it as a `continue`. Counting it can put a wrapper around a region that had none, which can
/// capture another continue, so the walk repeats until it marks nothing more. Only a continue to a loop header that is
/// also the loop body region's stop is marked, so that region captures the flag and no census outside the loop
/// moves; any other captured continue stays lexical, and its writer refuses it.
///
/// A loop boundary's body exit continue (`LoopBoundaryControl.continue_via_flag`), which its writer puts after the body
/// region in the holding region's text, is marked by the same rule and counted as an escape to the body region's stop.
pub fn markFlaggedContinues(allocator: std.mem.Allocator, root: *Region) std.mem.Allocator.Error!void {
    while (try markRegionContinues(allocator, root, null, false)) {}
}

/// The readable writer's wrapper test (`emitRegionWithPredeclaredBlock`): a region is written inside a transfer
/// wrapper when it owns an escape to its stop or has a free target.
fn regionIsWrapped(allocator: std.mem.Allocator, region: *const Region) std.mem.Allocator.Error!bool {
    if (regionOwnsEscape(region)) return true;
    if (region.stop == null) return false;
    const targets = try regionFreeTargetsAlloc(allocator, region);
    defer allocator.free(targets);
    return targets.len != 0;
}

/// Marks the continues of `region`, written inside `around`, and of the regions below it; returns whether it marked
/// one. An `else` arm the writer may fold into an `elseif` counts as written without a wrapper of its own.
fn markRegionContinues(
    allocator: std.mem.Allocator,
    region: *Region,
    around: ?*const EnclosingStatement,
    may_fold_into_elseif: bool,
) std.mem.Allocator.Error!bool {
    const wrapper: EnclosingStatement = .{ .kind = .wrapper, .stop = region.stop, .parent = around };
    const wrapped = !may_fold_into_elseif and try regionIsWrapped(allocator, region);
    const inner: ?*const EnclosingStatement = if (wrapped) &wrapper else around;
    // A region with nodes writes its continue after its last node, inside its own wrapper.
    var marked = region.nodes.len != 0 and markContinueProjection(region, inner);
    for (region.nodes) |*node| {
        if (try markNodeContinues(allocator, region, node, inner)) marked = true;
    }
    return marked;
}

fn markNodeContinues(
    allocator: std.mem.Allocator,
    holder: *const Region,
    node: *Node,
    around: ?*const EnclosingStatement,
) std.mem.Allocator.Error!bool {
    var marked = false;
    switch (node.*) {
        .block, .loop_control, .loop_terminal => {},
        .branch => |branch| {
            // An empty arm has no wrapper of its own: its continue is written in this region's `if` arm.
            if (branch.then_region.nodes.len == 0) {
                if (markContinueProjection(branch.then_region, around)) marked = true;
            } else if (try markRegionContinues(allocator, branch.then_region, around, false)) {
                marked = true;
            }
            if (branch.else_region.nodes.len == 0) {
                if (markContinueProjection(branch.else_region, around)) marked = true;
            } else if (try markRegionContinues(allocator, branch.else_region, around, elseArmMayFoldIntoElseIf(branch))) {
                marked = true;
            }
        },
        .loop => |loop| marked = try markLoopBodyContinues(allocator, loop.header, loop.body_region, around),
        .latch_loop => |loop| marked = try markLoopBodyContinues(allocator, loop.header, loop.body_region, around),
        .infinite_loop => |loop| {
            marked = try markLoopBodyContinues(allocator, loop.header, loop.body_region, around);
            // The shared side-exit regions are written after the loop's `end`.
            if (loop.shared_side_exit) |side_exit| {
                for (side_exit.entries) |entry| {
                    if (try markRegionContinues(allocator, entry.region, around, false)) marked = true;
                }
            }
        },
        .loop_boundary => |*control| {
            // The body exit continue follows the body region in this region's text.
            if (markLoopBoundaryContinue(holder, control, around)) marked = true;
            // The body region and the side region are written in this region's text; an empty body's continue is
            // left to its writer.
            if (control.body_region.nodes.len != 0 and try markRegionContinues(allocator, control.body_region, around, false)) {
                marked = true;
            }
            switch (control.boundary) {
                .side_exit => |side| {
                    if (try markRegionContinues(allocator, side.region, around, false)) marked = true;
                },
                .side_escape => |side| {
                    if (try markRegionContinues(allocator, side.region, around, false)) marked = true;
                },
                .exit, .escape, .terminal, .shared_exit => {},
            }
        },
    }
    return marked;
}

fn markLoopBodyContinues(
    allocator: std.mem.Allocator,
    header: ir.BlockId,
    body: *Region,
    around: ?*const EnclosingStatement,
) std.mem.Allocator.Error!bool {
    const loop: EnclosingStatement = .{ .kind = .loop, .header = header, .stop = body.stop, .parent = around };
    return markRegionContinues(allocator, body, &loop, false);
}

/// Marks `region`'s continue projection when it continues the innermost loop at its header, which is also the loop
/// body region's stop, and the innermost Luau loop statement around its writer is a transfer wrapper that stops at
/// another block. Returns whether it marked.
fn markContinueProjection(region: *Region, around: ?*const EnclosingStatement) bool {
    const projection = if (region.continue_projection) |*value| value else return false;
    if (projection.via_flag) return false;
    const target = region.continue_target orelse return false;
    if (projection.target != target) return false;
    if (!wrapperCapturesLoopContinue(around, target)) return false;
    projection.via_flag = true;
    return true;
}

/// Marks a loop boundary's body exit continue (`LoopBoundaryControl.continue_via_flag`) under the rule
/// `markContinueProjection` applies. Its writer (`emitLoopBoundaryBodyImpl`) ends the body arm with a `continue` to the
/// holding region's continue target when the body region stops there, at a block other than the holding region's stop,
/// with the same loop exit and continue target and no continue projection of its own (the `.continue_target` case of
/// `transparent_stop.validateLoopBoundaryBody`). Returns whether it marked.
fn markLoopBoundaryContinue(holder: *const Region, control: *LoopBoundaryControl, around: ?*const EnclosingStatement) bool {
    if (control.continue_via_flag) return false;
    const body = control.body_region;
    const target = body.stop orelse return false;
    const holder_stop = holder.stop orelse return false;
    const continue_target = holder.continue_target orelse return false;
    if (target == holder_stop or target != continue_target or body.continue_projection != null) return false;
    if (body.continue_target == null or body.continue_target.? != continue_target) return false;
    if (body.loop_exit != holder.loop_exit) return false;
    if (!wrapperCapturesLoopContinue(around, target)) return false;
    control.continue_via_flag = true;
    return true;
}

/// Whether a lexical `continue` to `target` written inside `around` would bind to a transfer wrapper that stops at
/// another block, inside a loop whose header and body region stop are both `target`, so that loop body's wrapper
/// captures the flag that carries it instead.
fn wrapperCapturesLoopContinue(around: ?*const EnclosingStatement, target: ir.BlockId) bool {
    const innermost = around orelse return false;
    if (innermost.kind != .wrapper or (innermost.stop != null and innermost.stop.? == target)) return false;
    var outer = innermost.parent;
    while (outer) |statement| : (outer = statement.parent) {
        if (statement.kind == .wrapper) continue;
        return statement.header != null and statement.header.? == target and
            statement.stop != null and statement.stop.? == target;
    }
    return false;
}

/// Whether the readable writer may write `branch`'s else arm as an `elseif` (`emitElseIfChain`), with no wrapper of
/// its own: the structural part of that test. The rest (no declaration, no written instruction, no expression form)
/// depends on emission, so the arm counts as unwrapped whenever this holds, and a continue the arm's own wrapper
/// would capture is then left lexical and refused by its writer.
fn elseArmMayFoldIntoElseIf(branch: Branch) bool {
    const join = branch.join orelse return false;
    const arm = branch.else_region;
    if (arm.continue_projection != null or arm.stop == null or arm.stop.? != join or arm.nodes.len != 1) return false;
    const nested = switch (arm.nodes[0]) {
        .branch => |value| value,
        else => return false,
    };
    if (nested.then_edge_override != null or nested.else_edge_override != null or
        nested.then_shared_reentry != null or nested.else_shared_reentry != null) return false;
    if (nested.join) |nested_join| return nested_join == join;
    return nested.then_region.stop != null and nested.then_region.stop.? == join and
        nested.else_region.stop != null and nested.else_region.stop.? == join;
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

/// The exit of a loop node whose escape flag the loop declares at the top of each pass, or null.
///
/// The escape census lets a loop own its exit: `collectLoopFreeTargets` puts an exit that is not itself an escape
/// in the capture chain of the body, so an escape to it from the body (a nested loop that leaves through it, a
/// loop-boundary escape or side escape to it, or a projection of a region in the body) is no free target above the
/// loop and no transfer wrapper's stop. The region that holds the loop declares the flag before its wrapper when its
/// stop is the exit. Otherwise every read and write of the flag lies inside the loop, and the loop declares it at
/// the top of every pass, so a loop that runs again starts with the flag false; a function-scope declaration of the
/// same flag (for a loop-boundary exit to the same block) is shadowed inside the loop.
pub fn loopOwnedExitFlag(holding_region: *const Region, node: Node) ?ir.BlockId {
    const owned: struct { exit: ir.BlockId, body: *const Region } = switch (node) {
        .loop => |loop| if (loop.exit_is_escape) return null else .{ .exit = loop.exit_edge.target, .body = loop.body_region },
        .latch_loop => |loop| if (loop.exit_is_escape) return null else .{ .exit = loop.exit, .body = loop.body_region },
        .infinite_loop => |loop| if (loop.exit_is_escape) return null else .{ .exit = loop.exit orelse return null, .body = loop.body_region },
        else => return null,
    };
    if (holding_region.stop != null and holding_region.stop.? == owned.exit) return null;
    if (!regionEscapesTo(owned.body, owned.exit)) return null;
    return owned.exit;
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

/// Reports a loop-boundary body arm that the writer would end with a lexical
/// `continue` to a block other than `stop`.
///
/// When a region owns an escape it is written inside a `repeat ... until true`
/// transfer wrapper. A nested loop boundary whose body arm continues the
/// enclosing loop is written as a lexical `continue`, which Luau binds to that
/// `repeat` and so reaches `stop`, not the loop header. This is the
/// escape-wrapper case the loop-boundary exit path already carries; keep it
/// separate so the emitter can refuse and fall back to the flat layout. The
/// node is reported on the `.continue_target` condition alone: its body region's
/// stop is set, differs from the holding region's stop, and equals the holding
/// region's continue target, whatever the body region's continue projection.
/// A node whose body exit continue `markFlaggedContinues` carries by flag is not
/// reported: its writer sets the flag and leaves the wrapper instead.
pub fn regionHasLoopBoundaryContinueNotTo(region: *const Region, stop: ir.BlockId) bool {
    for (region.nodes) |node| {
        if (nodeHasLoopBoundaryContinueNotTo(node, stop, region.continue_target)) return true;
    }
    return false;
}

/// Reports a loop exit below `region` that the writer ends with an unflagged
/// lexical `break`: a `.loop_boundary` side exit whose side region does not
/// always end the function, a `.loop_boundary` shared exit, or a
/// `.loop_control` exit (written through `emitLoopExit`).
///
/// When a region is written inside a `repeat ... until true` transfer wrapper,
/// such a `break` binds to that `repeat`, whatever the wrapper's stop (the loop
/// header or the latch block): leaving the wrapper reaches its stop and the
/// loop runs another pass instead of leaving. No escape flag is set for these
/// exits and the loop-boundary census counts only `.exit`, so nothing carries
/// the exit out of the wrapper; keep it separate so the emitter can refuse and
/// fall back to the flat layout. The walk descends into branch arms,
/// loop-boundary body and side regions, and infinite-loop shared side-exit
/// regions; it does not enter `.loop`, `.latch_loop` or `.infinite_loop`
/// bodies, where a nested loop rebinds `break`. It compares no stop, so it
/// walks null-stop arms too.
pub fn regionHasUnflaggedLoopExitBreak(program: *const ir.Program, region: *const Region) bool {
    for (region.nodes) |node| {
        if (nodeHasUnflaggedLoopExitBreak(program, node)) return true;
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

test "a continue that a wrapper stopping at another block would capture is carried by flag" {
    const allocator = std.testing.allocator;
    const header = ir.BlockId.fromIndex(1);
    const join = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    const forwarder = ir.BlockId.fromIndex(4);
    const outer_test = ir.BlockId.fromIndex(5);
    const inner_test = ir.BlockId.fromIndex(6);

    // In a loop body: if <outer> then if <inner> then <continue the loop> else <leave the loop> end end, joining at
    // `join`. The arm that leaves the loop gives the outer arm a free target, so the outer arm is written inside a
    // transfer wrapper that stops at the join, and a lexical continue in the inner then-arm would bind to it.
    var continue_nodes = [_]Node{.{ .block = ir.BlockId.fromIndex(7) }};
    var continue_arm = Region{
        .nodes = &continue_nodes,
        .stop = join,
        .loop_exit = exit,
        .continue_target = header,
        .continue_projection = .{ .target = header, .edge = null },
    };
    var escape_nodes = [_]Node{.{ .block = ir.BlockId.fromIndex(8) }};
    var escape_arm = Region{
        .nodes = &escape_nodes,
        .stop = join,
        .loop_exit = exit,
        .continue_target = header,
        .escape_projection = .{ .target = exit, .edge = null },
    };
    var arm_nodes = [_]Node{.{ .branch = .{ .block = inner_test, .then_region = &continue_arm, .else_region = &escape_arm, .join = null } }};
    var arm = Region{ .nodes = &arm_nodes, .stop = join, .loop_exit = exit, .continue_target = header };
    var empty_arm = Region{ .nodes = &.{}, .stop = join, .loop_exit = exit, .continue_target = header };
    var body_nodes = [_]Node{
        .{ .branch = .{ .block = outer_test, .then_region = &arm, .else_region = &empty_arm, .join = join } },
        .{ .block = join },
    };

    // A loop whose body stops at a block that forwards to the header: not marked, so no census outside the loop
    // moves; the writer refuses the continue as before.
    var forwarded_body = Region{ .nodes = &body_nodes, .stop = forwarder, .loop_exit = exit, .continue_target = header };
    var forwarded_nodes = [_]Node{.{ .infinite_loop = .{ .header = header, .body_region = &forwarded_body, .exit = exit } }};
    var forwarded_root = Region{ .nodes = &forwarded_nodes, .stop = null, .loop_exit = null };
    try markFlaggedContinues(allocator, &forwarded_root);
    try std.testing.expect(!continue_arm.continue_projection.?.via_flag);

    // A latch loop whose body stops at the header: marked, and counted as a nonlocal continue is counted. The arm
    // with the continue and the loop body each own a wrapper; the outer arm forwards the flag.
    var body = Region{ .nodes = &body_nodes, .stop = header, .loop_exit = exit, .continue_target = header };
    var root_nodes = [_]Node{.{ .latch_loop = .{ .header = header, .body_region = &body, .exit = exit, .latch_count = 1 } }};
    var root = Region{ .nodes = &root_nodes, .stop = null, .loop_exit = null };
    try std.testing.expect(!regionOwnsEscape(&continue_arm));
    try std.testing.expect(!regionOwnsEscape(&body));
    try markFlaggedContinues(allocator, &root);
    try std.testing.expect(continue_arm.continue_projection.?.via_flag);
    try std.testing.expect(regionOwnsEscape(&continue_arm));
    try std.testing.expect(!regionOwnsEscape(&arm));
    try std.testing.expect(regionOwnsEscape(&body));
    try std.testing.expect(regionHasNestedEscapeTo(&body, header));
    const arm_targets = try regionFreeTargetsAlloc(allocator, &arm);
    defer allocator.free(arm_targets);
    try std.testing.expectEqualSlices(ir.BlockId, &.{ header, exit }, arm_targets);
    const body_targets = try regionFreeTargetsAlloc(allocator, &body);
    defer allocator.free(body_targets);
    try std.testing.expectEqualSlices(ir.BlockId, &.{exit}, body_targets);
    const root_targets = try regionFreeTargetsAlloc(allocator, &root);
    defer allocator.free(root_targets);
    try std.testing.expectEqual(@as(usize, 0), root_targets.len);

    // A continue that no wrapper encloses binds to its loop: not marked, and no wrapper is added.
    var lone_nodes = [_]Node{.{ .block = ir.BlockId.fromIndex(9) }};
    var lone_arm = Region{
        .nodes = &lone_nodes,
        .stop = join,
        .loop_exit = exit,
        .continue_target = header,
        .continue_projection = .{ .target = header, .edge = null },
    };
    var lone_empty = Region{ .nodes = &.{}, .stop = join, .loop_exit = exit, .continue_target = header };
    var lone_body_nodes = [_]Node{
        .{ .branch = .{ .block = outer_test, .then_region = &lone_arm, .else_region = &lone_empty, .join = join } },
        .{ .block = join },
    };
    var lone_body = Region{ .nodes = &lone_body_nodes, .stop = header, .loop_exit = exit, .continue_target = header };
    var lone_root_nodes = [_]Node{.{ .latch_loop = .{ .header = header, .body_region = &lone_body, .exit = exit, .latch_count = 1 } }};
    var lone_root = Region{ .nodes = &lone_root_nodes, .stop = null, .loop_exit = null };
    try markFlaggedContinues(allocator, &lone_root);
    try std.testing.expect(!lone_arm.continue_projection.?.via_flag);
    try std.testing.expect(!regionOwnsEscape(&lone_body));
}

test "a loop-boundary exit continue that a wrapper stopping at another block would capture is carried by flag" {
    const allocator = std.testing.allocator;
    const header = ir.BlockId.fromIndex(7);
    const join = ir.BlockId.fromIndex(24);
    const exit = ir.BlockId.fromIndex(26);

    // An infinite loop whose body (stopping at the header) leaves through a shared side exit at `join`:
    // if <8> then <9>; if <10> then <continue the loop> else <14>; <loop boundary 15> end else <23> end. The loop
    // boundary's body region stops at the header, the holding arm's continue target, so its writer ends the body arm
    // with a continue; its side arm escapes to `join`, the holding arm's stop, so that arm is written inside a transfer
    // wrapper that stops at `join`, and a lexical continue there would bind to the wrapper.
    var boundary_body_nodes = [_]Node{ .{ .block = ir.BlockId.fromIndex(20) }, .{ .block = ir.BlockId.fromIndex(21) } };
    var boundary_body = Region{ .nodes = &boundary_body_nodes, .stop = header, .loop_exit = exit, .continue_target = header };
    var side_nodes = [_]Node{.{ .block = ir.BlockId.fromIndex(16) }};
    var side_region = Region{ .nodes = &side_nodes, .stop = join, .loop_exit = null };
    var boundary_arm_nodes = [_]Node{
        .{ .block = ir.BlockId.fromIndex(14) },
        .{ .loop_boundary = .{
            .block = ir.BlockId.fromIndex(15),
            .body_edge = .{ .target = ir.BlockId.fromIndex(20) },
            .body_region = &boundary_body,
            .boundary = .{ .side_escape = .{ .entry_edge = .{ .target = ir.BlockId.fromIndex(16) }, .region = &side_region, .target = join } },
            .body_on_true = true,
        } },
    };
    var boundary_arm = Region{ .nodes = &boundary_arm_nodes, .stop = join, .loop_exit = exit, .continue_target = header };
    var continue_nodes = [_]Node{ .{ .block = ir.BlockId.fromIndex(11) }, .{ .block = ir.BlockId.fromIndex(12) } };
    var continue_arm = Region{
        .nodes = &continue_nodes,
        .stop = join,
        .loop_exit = exit,
        .continue_target = header,
        .continue_projection = .{ .target = header, .edge = null },
    };
    var then_nodes = [_]Node{
        .{ .block = ir.BlockId.fromIndex(9) },
        .{ .branch = .{ .block = ir.BlockId.fromIndex(10), .then_region = &continue_arm, .else_region = &boundary_arm, .join = null } },
    };
    var then_arm = Region{ .nodes = &then_nodes, .stop = join, .loop_exit = exit, .continue_target = header };
    var else_nodes = [_]Node{.{ .block = ir.BlockId.fromIndex(23) }};
    var else_arm = Region{ .nodes = &else_nodes, .stop = join, .loop_exit = exit, .continue_target = header };
    var body_nodes = [_]Node{
        .{ .block = header },
        .{ .branch = .{ .block = ir.BlockId.fromIndex(8), .then_region = &then_arm, .else_region = &else_arm, .join = join } },
    };
    var body = Region{
        .nodes = &body_nodes,
        .stop = header,
        .loop_exit = exit,
        .continue_target = header,
        .escape_projection = .{ .target = join, .edge = null },
    };
    var shared_nodes = [_]Node{.{ .block = join }};
    var shared_region = Region{ .nodes = &shared_nodes, .stop = exit, .loop_exit = null };
    var shared_entries = [_]SharedSideEntry{.{ .entry = join, .region = &shared_region }};
    var root_nodes = [_]Node{.{ .infinite_loop = .{
        .header = header,
        .body_region = &body,
        .exit = exit,
        .shared_side_exit = .{ .entries = &shared_entries },
    } }};
    var root = Region{ .nodes = &root_nodes, .stop = null, .loop_exit = null };
    const boundary = &boundary_arm_nodes[1].loop_boundary;

    // Before the marking no region counts the continue, and the refusal at a wrapper reports the boundary both at the
    // loop body's wrapper and at the holding arm's.
    try std.testing.expect(!regionOwnsEscape(&body));
    try std.testing.expect(regionHasLoopBoundaryContinueNotTo(&body, header));
    try std.testing.expect(regionHasLoopBoundaryContinueNotTo(&boundary_arm, join));

    try markFlaggedContinues(allocator, &root);
    try std.testing.expect(boundary.continue_via_flag);
    // Counting the mark gives the outer then-arm a free target, so it is written inside a wrapper that stops at
    // `join`, which would capture the sibling arm's lexical continue: the fixed point carries that one by flag too.
    try std.testing.expect(continue_arm.continue_projection.?.via_flag);
    try std.testing.expect(regionOwnsEscape(&body));
    try std.testing.expect(regionHasNestedEscapeTo(&body, header));
    const boundary_arm_targets = try regionFreeTargetsAlloc(allocator, &boundary_arm);
    defer allocator.free(boundary_arm_targets);
    try std.testing.expectEqualSlices(ir.BlockId, &.{header}, boundary_arm_targets);
    const then_targets = try regionFreeTargetsAlloc(allocator, &then_arm);
    defer allocator.free(then_targets);
    try std.testing.expectEqualSlices(ir.BlockId, &.{header}, then_targets);
    const body_targets = try regionFreeTargetsAlloc(allocator, &body);
    defer allocator.free(body_targets);
    try std.testing.expectEqualSlices(ir.BlockId, &.{join}, body_targets);
    const root_targets = try regionFreeTargetsAlloc(allocator, &root);
    defer allocator.free(root_targets);
    try std.testing.expectEqual(@as(usize, 0), root_targets.len);
    // The marked boundary is written as the flag and a `break`, so neither wrapper refuses it.
    try std.testing.expect(!regionHasLoopBoundaryContinueNotTo(&body, header));
    try std.testing.expect(!regionHasLoopBoundaryContinueNotTo(&boundary_arm, join));
}

test "a loop-boundary exit continue under a wrapper that stops at the loop header stays lexical" {
    const allocator = std.testing.allocator;
    const header = ir.BlockId.fromIndex(7);
    const join = ir.BlockId.fromIndex(24);
    const exit = ir.BlockId.fromIndex(26);

    // The same loop body with the loop boundary's side arm ending the function instead: the holding arm owns no
    // escape and has no free target, so no wrapper of its own, and its continue binds to the loop body's wrapper,
    // which stops at the header. Nothing is marked.
    var boundary_body_nodes = [_]Node{ .{ .block = ir.BlockId.fromIndex(20) }, .{ .block = ir.BlockId.fromIndex(21) } };
    var boundary_body = Region{ .nodes = &boundary_body_nodes, .stop = header, .loop_exit = exit, .continue_target = header };
    var boundary_arm_nodes = [_]Node{
        .{ .block = ir.BlockId.fromIndex(14) },
        .{ .loop_boundary = .{
            .block = ir.BlockId.fromIndex(15),
            .body_edge = .{ .target = ir.BlockId.fromIndex(20) },
            .body_region = &boundary_body,
            .boundary = .{ .terminal = .{ .edge = .{ .target = ir.BlockId.fromIndex(16) }, .block = ir.BlockId.fromIndex(16) } },
            .body_on_true = true,
        } },
    };
    var boundary_arm = Region{ .nodes = &boundary_arm_nodes, .stop = join, .loop_exit = exit, .continue_target = header };
    var continue_nodes = [_]Node{ .{ .block = ir.BlockId.fromIndex(11) }, .{ .block = ir.BlockId.fromIndex(12) } };
    var continue_arm = Region{
        .nodes = &continue_nodes,
        .stop = join,
        .loop_exit = exit,
        .continue_target = header,
        .continue_projection = .{ .target = header, .edge = null },
    };
    var then_nodes = [_]Node{
        .{ .block = ir.BlockId.fromIndex(9) },
        .{ .branch = .{ .block = ir.BlockId.fromIndex(10), .then_region = &continue_arm, .else_region = &boundary_arm, .join = null } },
    };
    var then_arm = Region{ .nodes = &then_nodes, .stop = join, .loop_exit = exit, .continue_target = header };
    var else_nodes = [_]Node{.{ .block = ir.BlockId.fromIndex(23) }};
    var else_arm = Region{ .nodes = &else_nodes, .stop = join, .loop_exit = exit, .continue_target = header };
    var body_nodes = [_]Node{
        .{ .block = header },
        .{ .branch = .{ .block = ir.BlockId.fromIndex(8), .then_region = &then_arm, .else_region = &else_arm, .join = join } },
    };
    var body = Region{
        .nodes = &body_nodes,
        .stop = header,
        .loop_exit = exit,
        .continue_target = header,
        .escape_projection = .{ .target = join, .edge = null },
    };
    var shared_nodes = [_]Node{.{ .block = join }};
    var shared_region = Region{ .nodes = &shared_nodes, .stop = exit, .loop_exit = null };
    var shared_entries = [_]SharedSideEntry{.{ .entry = join, .region = &shared_region }};
    var root_nodes = [_]Node{.{ .infinite_loop = .{
        .header = header,
        .body_region = &body,
        .exit = exit,
        .shared_side_exit = .{ .entries = &shared_entries },
    } }};
    var root = Region{ .nodes = &root_nodes, .stop = null, .loop_exit = null };
    const boundary = &boundary_arm_nodes[1].loop_boundary;

    try markFlaggedContinues(allocator, &root);
    try std.testing.expect(!boundary.continue_via_flag);
    try std.testing.expect(!continue_arm.continue_projection.?.via_flag);
    try std.testing.expect(!regionOwnsEscape(&boundary_arm));
    const boundary_arm_targets = try regionFreeTargetsAlloc(allocator, &boundary_arm);
    defer allocator.free(boundary_arm_targets);
    try std.testing.expectEqual(@as(usize, 0), boundary_arm_targets.len);
    try std.testing.expect(!regionOwnsEscape(&body));
    // The refusal at the loop body's wrapper still compares the boundary with its holding arm's own stop, not with the
    // wrapper's, so it reports this lexical continue although the continue reaches the header: the function is
    // written in the flat layout, as before.
    try std.testing.expect(regionHasLoopBoundaryContinueNotTo(&body, header));
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

test "loop exits written as an unflagged break are reported whatever the region's stop" {
    // A side exit whose side region does not end the function, a shared exit and a loop control's exit are each
    // written with an unflagged `break`, which binds to a `repeat ... until true` transfer wrapper whatever the
    // wrapper's stop. Only the side regions' last blocks are read: the jump and return pair
    // pins the termination copy to the emitter's regionAlwaysFunctionTerminates.
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const decision = ir.BlockId.fromIndex(1);
    const control = ir.BlockId.fromIndex(2);
    const latch = ir.BlockId.fromIndex(3);
    const side_jump = ir.BlockId.fromIndex(4);
    const side_return = ir.BlockId.fromIndex(5);
    const exit = ir.BlockId.fromIndex(6);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = decision } } },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = control },
            .else_edge = .{ .target = side_jump },
        } } },
        .{ .id = control, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = latch },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = side_jump, .function = function_id, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = side_return, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ ir.ValueId.fromIndex(0), ir.ValueId.fromIndex(1) },
        .blocks = &.{ header, decision, control, latch, side_jump, side_return, exit },
        .entry_block = header,
    }};
    const program: ir.Program = .{
        .program_id = "unflagged-loop-exit-break",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var body_region = Region{ .nodes = &.{}, .stop = latch, .loop_exit = exit, .continue_target = header };
    var side_jump_nodes = [_]Node{.{ .block = side_jump }};
    var side_jump_region = Region{ .nodes = &side_jump_nodes, .stop = exit, .loop_exit = null };
    var side_return_nodes = [_]Node{.{ .block = side_return }};
    var side_return_region = Region{ .nodes = &side_return_nodes, .stop = exit, .loop_exit = null };

    // A side exit whose side region ends in a jump is reported under a header stop and a latch stop alike; the
    // same node whose side region returns is not.
    var side_exit_nodes = [_]Node{.{ .loop_boundary = .{
        .block = decision,
        .body_edge = .{ .target = control },
        .body_region = &body_region,
        .boundary = .{ .side_exit = .{ .entry_edge = .{ .target = side_jump }, .region = &side_jump_region } },
        .body_on_true = true,
    } }};
    const header_stop = Region{ .nodes = &side_exit_nodes, .stop = header, .loop_exit = exit, .continue_target = header };
    try std.testing.expect(regionHasUnflaggedLoopExitBreak(&program, &header_stop));
    const latch_stop = Region{ .nodes = &side_exit_nodes, .stop = latch, .loop_exit = exit, .continue_target = header };
    try std.testing.expect(regionHasUnflaggedLoopExitBreak(&program, &latch_stop));
    var returning_nodes = [_]Node{.{ .loop_boundary = .{
        .block = decision,
        .body_edge = .{ .target = control },
        .body_region = &body_region,
        .boundary = .{ .side_exit = .{ .entry_edge = .{ .target = side_return }, .region = &side_return_region } },
        .body_on_true = true,
    } }};
    const returning = Region{ .nodes = &returning_nodes, .stop = header, .loop_exit = exit, .continue_target = header };
    try std.testing.expect(!regionHasUnflaggedLoopExitBreak(&program, &returning));

    // A nested loop rebinds `break`, so the side exit inside a `.loop` body is not reported; a null-stop branch
    // arm is walked like any other region.
    var loop_body = Region{ .nodes = &side_exit_nodes, .stop = header, .loop_exit = exit, .continue_target = header };
    var loop_nodes = [_]Node{.{ .loop = .{
        .header = header,
        .body_region = &loop_body,
        .body_edge = .{ .target = decision },
        .exit_edge = .{ .target = exit },
        .continue_on_true = true,
    } }};
    const nested = Region{ .nodes = &loop_nodes, .stop = null, .loop_exit = null };
    try std.testing.expect(!regionHasUnflaggedLoopExitBreak(&program, &nested));
    var arm_region = Region{ .nodes = &side_exit_nodes, .stop = null, .loop_exit = exit, .continue_target = header };
    var empty_arm = Region{ .nodes = &.{}, .stop = null, .loop_exit = exit, .continue_target = header };
    var branch_nodes = [_]Node{.{ .branch = .{
        .block = header,
        .then_region = &arm_region,
        .else_region = &empty_arm,
        .join = null,
    } }};
    const null_stop_arm = Region{ .nodes = &branch_nodes, .stop = header, .loop_exit = exit, .continue_target = header };
    try std.testing.expect(regionHasUnflaggedLoopExitBreak(&program, &null_stop_arm));

    // A shared exit and a loop control's exit always end with the bare `break`; the loop control sits in a region
    // whose stop is the latch block.
    const shared = loop_exit_shape.SharedPaths{ .exit = exit, .blocks = &.{}, .route_indices = &.{}, .entries = &.{} };
    var shared_nodes = [_]Node{.{ .loop_boundary = .{
        .block = decision,
        .body_edge = .{ .target = control },
        .body_region = &body_region,
        .boundary = .{ .shared_exit = .{ .owner = &shared, .index = 0 } },
        .body_on_true = true,
    } }};
    const shared_holder = Region{ .nodes = &shared_nodes, .stop = header, .loop_exit = exit, .continue_target = header };
    try std.testing.expect(regionHasUnflaggedLoopExitBreak(&program, &shared_holder));
    var control_nodes = [_]Node{.{ .loop_control = .{
        .block = control,
        .continue_edge = .{ .target = latch },
        .exit_edge = .{ .target = exit },
        .continue_on_true = true,
    } }};
    const control_holder = Region{ .nodes = &control_nodes, .stop = latch, .loop_exit = exit, .continue_target = header };
    try std.testing.expect(regionHasUnflaggedLoopExitBreak(&program, &control_holder));
}

pub const Plan = struct {
    allocator: std.mem.Allocator,
    root: *Region,

    // Large authenticated rewrite graphs can be valid without having a
    // useful reducible region decomposition. Keep recursive structuring
    // bounded; the emitter preserves the complete reachable graph with its
    // dispatcher, so the limit is on
    // the function's admitted block budget rather than its live reachability.
    pub const arbitrary_fallback_block_limit: usize = 1_024;

    pub fn shouldUseArbitraryFallbackForFunction(program: *const ir.Program, function: ir.Function) bool {
        if (program.edge_rewrites.len != 0 and function.blocks.len > arbitrary_fallback_block_limit) return true;
        return false;
    }

    pub fn shouldUseArbitraryFallback(analysis: *const cfg.Analysis) bool {
        return shouldUseArbitraryFallbackForFunction(analysis.program, analysis.function);
    }

    pub fn init(allocator: std.mem.Allocator, analysis: *const cfg.Analysis) BuildError!Plan {
        var collision: ?Collision = null;
        return initWithCollision(allocator, analysis, &collision) catch |err| {
            if (collision) |*value| {
                value.deinit(allocator);
            }
            return err;
        };
    }

    /// Preserve a valid CFG when structured ownership cannot be proven.  The
    /// fallback is intentionally a complete block list; emission owns the
    /// control-state representation and still consumes the original edges.
    pub fn initWithArbitraryFallback(allocator: std.mem.Allocator, analysis: *const cfg.Analysis) BuildError!Plan {
        if (shouldUseArbitraryFallback(analysis)) return initArbitraryCfg(allocator, analysis);
        var plan = Plan.init(allocator, analysis) catch |err| {
            if (err != error.UnsupportedShape) return err;
            return initArbitraryCfg(allocator, analysis);
        };
        // The readable writers, and the register and syntax-depth certificates that budget their text, build this
        // plan: a continue a wrapper would capture is carried by flag in all of them alike.
        errdefer plan.deinit();
        try markFlaggedContinues(allocator, plan.root);
        return plan;
    }

    /// Construct the explicit dispatcher representation after a structured
    /// attempt has already established that ownership cannot be proven.
    pub fn initArbitrary(allocator: std.mem.Allocator, analysis: *const cfg.Analysis) BuildError!Plan {
        return initArbitraryCfg(allocator, analysis);
    }

    fn initArbitraryCfg(allocator: std.mem.Allocator, analysis: *const cfg.Analysis) BuildError!Plan {
        const reachable_count = analysis.reachableCount();
        if (reachable_count == 0) return error.UnsupportedShape;
        const nodes = try allocator.alloc(Node, reachable_count);
        errdefer allocator.free(nodes);
        var node_index: usize = 0;
        for (analysis.function.blocks) |block| {
            if (!analysis.isReachable(block)) continue;
            if (node_index >= nodes.len) return error.UnsupportedShape;
            nodes[node_index] = .{ .block = block };
            node_index += 1;
        }
        if (node_index != nodes.len) return error.UnsupportedShape;
        std.sort.heap(Node, nodes, {}, lessArbitraryNode);
        const root = try allocator.create(Region);
        errdefer allocator.destroy(root);
        root.* = .{
            .nodes = nodes,
            .stop = null,
            .loop_exit = null,
            .arbitrary_cfg = true,
        };
        return .{ .allocator = allocator, .root = root };
    }

    pub fn initWithCollision(
        allocator: std.mem.Allocator,
        analysis: *const cfg.Analysis,
        collision: ?*?Collision,
    ) BuildError!Plan {
        return initWithCollisionAndReplayContext(allocator, analysis, collision, null);
    }

    pub fn initWithCollisionAndReplayContext(
        allocator: std.mem.Allocator,
        analysis: *const cfg.Analysis,
        collision: ?*?Collision,
        replay_context: ?*structural_overlap.ReplayProjectionContext,
    ) BuildError!Plan {
        const visited = try allocator.alloc(bool, analysis.function.blocks.len);
        defer allocator.free(visited);
        @memset(visited, false);
        const visited_contexts = try allocator.alloc(?Builder.VisitContext, analysis.function.blocks.len);
        defer allocator.free(visited_contexts);
        @memset(visited_contexts, null);
        const loop_header_start = structural_overlap.structuralPhaseNow();
        const loop_headers = try natural_loop.headerCandidatesAlloc(allocator, analysis);
        defer allocator.free(loop_headers);
        const loop_memberships = try allocator.alloc(?[]bool, analysis.function.blocks.len);
        defer {
            for (loop_memberships) |membership| {
                if (membership) |bits| allocator.free(bits);
            }
            allocator.free(loop_memberships);
        }
        @memset(loop_memberships, null);
        const loop_validation_epochs = try allocator.alloc(usize, analysis.function.blocks.len);
        defer allocator.free(loop_validation_epochs);
        @memset(loop_validation_epochs, std.math.maxInt(usize));
        const loop_validation_generations = try allocator.alloc(usize, analysis.function.blocks.len);
        defer allocator.free(loop_validation_generations);
        @memset(loop_validation_generations, std.math.maxInt(usize));
        const loop_validation_outcomes = try allocator.alloc(LoopValidationOutcome, analysis.function.blocks.len);
        defer allocator.free(loop_validation_outcomes);
        @memset(loop_validation_outcomes, .uncomputed);
        const stop_boundary_closure = try allocator.alloc(?bool, analysis.function.blocks.len);
        defer allocator.free(stop_boundary_closure);
        @memset(stop_boundary_closure, null);
        structural_overlap.traceStructural("structural_phase plan_loop_headers function={} count={} ms={}\n", .{
            analysis.function.id.index(),
            std.mem.countScalar(bool, loop_headers, true),
            structural_overlap.structuralPhaseMillis(loop_header_start),
        });
        var owned_replay_context: ?structural_overlap.ReplayProjectionContext = null;
        var active_replay_context = replay_context;
        if (active_replay_context == null) {
            const replay_start = structural_overlap.structuralPhaseNow();
            owned_replay_context = try structural_overlap.ReplayProjectionContext.initForFunction(
                allocator,
                analysis.program,
                analysis.function.id,
            );
            active_replay_context = &owned_replay_context.?;
            structural_overlap.traceStructural("structural_phase plan_replay function={} ms={}\n", .{
                analysis.function.id.index(),
                structural_overlap.structuralPhaseMillis(replay_start),
            });
        }
        defer if (owned_replay_context) |*value| value.deinit();

        var builder: Builder = .{
            .allocator = allocator,
            .analysis = analysis,
            .visited = visited,
            .visited_contexts = visited_contexts,
            .loop_headers = loop_headers,
            .loop_memberships = loop_memberships,
            .loop_validation_epochs = loop_validation_epochs,
            .loop_validation_generations = loop_validation_generations,
            .loop_validation_outcomes = loop_validation_outcomes,
            .stop_boundary_closure = stop_boundary_closure,
            .replay_context = active_replay_context.?,
            .collision = collision,
            .trace_join_calls = 0,
            .trace_join_ms = 0,
        };
        const build_start = structural_overlap.structuralPhaseNow();
        const root = builder.buildRegion(analysis.function.entry_block, null, null, null) catch |err| {
            structural_overlap.traceStructural("structural_phase plan_build_failed function={} error={s} build_ms={} visited={} reachable={} join_calls={} join_ms={} loop_probe_calls={} loop_probe_ms={} build_loop_ms={} build_latch_ms={} build_infinite_ms={}\n", .{
                analysis.function.id.index(),
                @errorName(err),
                structural_overlap.structuralPhaseMillis(build_start),
                builder.visited_count,
                analysis.reachableCount(),
                builder.trace_join_calls,
                builder.trace_join_ms,
                builder.trace_loop_probe_calls,
                builder.trace_loop_probe_ms,
                builder.trace_build_loop_ms,
                builder.trace_build_latch_ms,
                builder.trace_build_infinite_ms,
            });
            structural_overlap.traceStructural("structural_phase plan_build_detail function={} infinite_classify_calls={} infinite_classify_ms={} infinite_continuation_calls={} infinite_continuation_ms={} infinite_resolve_calls={} infinite_resolve_ms={} infinite_shared_entry_calls={} infinite_shared_entry_ms={} infinite_body_calls={} infinite_body_ms={} projection_calls={} projection_ms={} parameter_calls={} parameter_ms={} reach_calls={} reach_ms={} bridge_calls={} bridge_ms={}\n", .{
                analysis.function.id.index(),
                builder.trace_infinite_classify_calls,
                builder.trace_infinite_classify_ms,
                builder.trace_infinite_continuation_calls,
                builder.trace_infinite_continuation_ms,
                builder.trace_infinite_resolve_calls,
                builder.trace_infinite_resolve_ms,
                builder.trace_infinite_shared_entry_calls,
                builder.trace_infinite_shared_entry_ms,
                builder.trace_infinite_body_calls,
                builder.trace_infinite_body_ms,
                builder.trace_projection_calls,
                builder.trace_projection_ms,
                builder.trace_parameter_calls,
                builder.trace_parameter_ms,
                builder.trace_reach_calls,
                builder.trace_reach_ms,
                builder.trace_bridge_calls,
                builder.trace_bridge_ms,
            });
            return err;
        };
        structural_overlap.traceStructural("structural_phase plan_build function={} visited={} reachable={} ms={}\n", .{
            analysis.function.id.index(),
            builder.visited_count,
            analysis.reachableCount(),
            structural_overlap.structuralPhaseMillis(build_start),
        });
        structural_overlap.traceStructural("structural_phase plan_build_detail function={} projection_calls={} projection_ms={} parameter_calls={} parameter_ms={} reach_calls={} reach_ms={} bridge_calls={} bridge_ms={}\n", .{
            analysis.function.id.index(),
            builder.trace_projection_calls,
            builder.trace_projection_ms,
            builder.trace_parameter_calls,
            builder.trace_parameter_ms,
            builder.trace_reach_calls,
            builder.trace_reach_ms,
            builder.trace_bridge_calls,
            builder.trace_bridge_ms,
        });
        errdefer destroyRegion(allocator, root);
        if (builder.visited_count != analysis.reachableCount()) {
            try builder.noteUnvisitedReachable();
            return error.UnsupportedShape;
        }
        try finishPlan(allocator, analysis, root, collision);
        return .{ .allocator = allocator, .root = root };
    }

    pub fn deinit(self: *Plan) void {
        destroyRegion(self.allocator, self.root);
        self.* = undefined;
    }
};

/// Post-build plan checks shared by `Plan.initWithCollisionAndReplayContext`
/// and the plan-accounting test, so the test drives the constructor's own
/// entry point. The constructor runs its
/// builder-owned visited-count check first and then calls this.
pub fn finishPlan(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    root: *const Region,
    collision: ?*?Collision,
) BuildError!void {
    try checkEscapeAccounting(allocator, analysis, root, collision);
}

/// Plan-level accounting gate (described in the preprint): refuse a plan whose root
/// free-target census is not empty, i.e. a plan that escapes to a block that
/// no enclosing region stop or owned loop exit consumes; such a plan emits a
/// write-only escape flag and falls through. The gate closes "root escape
/// target consumed", not "each CFG edge realized".
pub fn checkEscapeAccounting(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    root: *const Region,
    collision: ?*?Collision,
) BuildError!void {
    const free_targets = try regionFreeTargetsAlloc(allocator, root);
    defer allocator.free(free_targets);
    if (free_targets.len == 0) return;
    const output = collision orelse return error.UnsupportedShape;
    if (output.* != null) return error.UnsupportedShape;
    const target = free_targets[0];
    var edges: std.ArrayList(ir.CfgEdgeRef) = .empty;
    defer edges.deinit(allocator);
    try collectRegionEscapeEdges(allocator, analysis, root, null, target, &edges);
    const incoming_group: []ir.CfgEdgeRef = if (edges.items.len == 0) &.{} else try edges.toOwnedSlice(allocator);
    output.* = .{
        .block = target,
        .previous = if (incoming_group.len != 0) incoming_group[0].source else null,
        .incoming = if (incoming_group.len != 0) incoming_group[0] else null,
        .reason = .unowned_escape_target,
        .incoming_group = incoming_group,
    };
    return error.UnsupportedShape;
}

// The escape-edge walker mirrors `collectRegionFreeTargets`,
// `collectNodeFreeTargets` and `collectLoopFreeTargets` with the same capture
// chain, for one free target: it appends the CFG edges of every escape to
// `target` that no enclosing capture consumes.
fn collectRegionEscapeEdges(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    region: *const Region,
    captures: ?*const FreeTargetCapture,
    target: ir.BlockId,
    edges: *std.ArrayList(ir.CfgEdgeRef),
) std.mem.Allocator.Error!void {
    var own_capture: FreeTargetCapture = undefined;
    const nested_captures = if (region.stop) |stop| nested: {
        own_capture = .{ .target = stop, .parent = captures };
        break :nested &own_capture;
    } else captures;
    for (region.nodes) |node| try collectNodeEscapeEdges(allocator, analysis, node, nested_captures, target, edges);
    if (region.nodes.len == 0) return;
    const last = region.nodes[region.nodes.len - 1];
    if (region.escape_projection) |projection| {
        if (projection.target == target) try appendEscapeEdges(allocator, analysis, nested_captures, last, target, edges);
    }
    if (region.continue_projection) |projection| {
        if (continueProjectionUsesFlag(region, projection) and projection.target == target) {
            try appendEscapeEdges(allocator, analysis, nested_captures, last, target, edges);
        }
    }
}

fn collectNodeEscapeEdges(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    node: Node,
    captures: ?*const FreeTargetCapture,
    target: ir.BlockId,
    edges: *std.ArrayList(ir.CfgEdgeRef),
) std.mem.Allocator.Error!void {
    switch (node) {
        .block, .loop_control, .loop_terminal => {},
        .branch => |branch| {
            try collectRegionEscapeEdges(allocator, analysis, branch.then_region, captures, target, edges);
            try collectRegionEscapeEdges(allocator, analysis, branch.else_region, captures, target, edges);
        },
        .loop, .latch_loop, .infinite_loop => try collectLoopEscapeEdges(allocator, analysis, node, captures, target, edges),
        .loop_boundary => |control| {
            try collectRegionEscapeEdges(allocator, analysis, control.body_region, captures, target, edges);
            switch (control.boundary) {
                .escape => |edge| {
                    if (edge.target == target) try appendEscapeEdges(allocator, analysis, captures, node, target, edges);
                },
                .side_exit => |side| try collectRegionEscapeEdges(allocator, analysis, side.region, captures, target, edges),
                .side_escape => |side| {
                    try collectRegionEscapeEdges(allocator, analysis, side.region, captures, target, edges);
                    if (side.target == target) try appendEscapeEdges(allocator, analysis, captures, node, target, edges);
                },
                .exit, .terminal, .shared_exit => {},
            }
        },
    }
}

fn collectLoopEscapeEdges(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    node: Node,
    captures: ?*const FreeTargetCapture,
    target: ir.BlockId,
    edges: *std.ArrayList(ir.CfgEdgeRef),
) std.mem.Allocator.Error!void {
    switch (node) {
        .loop => |loop| {
            var loop_capture: FreeTargetCapture = undefined;
            const body_captures = if (!loop.exit_is_escape)
                capturesWithOwnedExit(captures, loop.exit_edge.target, &loop_capture)
            else
                captures;
            if (loop.exit_is_escape and loop.exit_edge.target == target) {
                try appendEscapeEdges(allocator, analysis, captures, node, target, edges);
            }
            try collectRegionEscapeEdges(allocator, analysis, loop.body_region, body_captures, target, edges);
        },
        .latch_loop => |loop| {
            var loop_capture: FreeTargetCapture = undefined;
            const body_captures = if (!loop.exit_is_escape)
                capturesWithOwnedExit(captures, loop.exit, &loop_capture)
            else
                captures;
            if (loop.exit_is_escape and loop.exit == target) {
                try appendEscapeEdges(allocator, analysis, captures, node, target, edges);
            }
            try collectRegionEscapeEdges(allocator, analysis, loop.body_region, body_captures, target, edges);
        },
        .infinite_loop => |loop| {
            var loop_capture: FreeTargetCapture = undefined;
            const loop_captures = if (!loop.exit_is_escape and loop.exit != null)
                capturesWithOwnedExit(captures, loop.exit.?, &loop_capture)
            else
                captures;
            if (loop.exit_is_escape and loop.exit.? == target) {
                try appendEscapeEdges(allocator, analysis, captures, node, target, edges);
            }
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
            try collectRegionEscapeEdges(allocator, analysis, loop.body_region, body_captures, target, edges);
            if (loop.shared_side_exit) |side| {
                for (side.entries) |entry| {
                    try collectRegionEscapeEdges(allocator, analysis, entry.region, captures, target, edges);
                }
            }
        },
        else => unreachable,
    }
}

// Record the CFG edges of one escape to `target` unless a capture in the
// chain consumes it: the direct edge of a `.block` node, otherwise the edges
// into `target` from blocks the node owns (transferred escapes, escaping loop
// exits and loop-boundary escapes).
fn appendEscapeEdges(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    captures: ?*const FreeTargetCapture,
    node: Node,
    target: ir.BlockId,
    edges: *std.ArrayList(ir.CfgEdgeRef),
) std.mem.Allocator.Error!void {
    var current = captures;
    while (current) |capture| : (current = capture.parent) {
        if (capture.target == target) return;
    }
    if (directEdgeReference(analysis.program, node, target)) |reference| {
        return appendUniqueEscapeEdge(allocator, edges, reference);
    }
    const owned = try nodeIncomingEdgesAlloc(allocator, analysis, node, target);
    defer allocator.free(owned);
    for (owned) |reference| try appendUniqueEscapeEdge(allocator, edges, reference);
}

fn appendUniqueEscapeEdge(
    allocator: std.mem.Allocator,
    edges: *std.ArrayList(ir.CfgEdgeRef),
    reference: ir.CfgEdgeRef,
) std.mem.Allocator.Error!void {
    for (edges.items) |existing| {
        if (std.meta.eql(existing, reference)) return;
    }
    try edges.append(allocator, reference);
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

    fn filterTerminalEscapeTargetsAlloc(
        self: *const Builder,
        targets: ?*const EscapeTarget,
    ) BuildError!EscapeTargetProjection {
        var blocks: std.ArrayList(ir.BlockId) = .empty;
        defer blocks.deinit(self.allocator);
        var current = targets;
        var removed = false;
        while (current) |target| : (current = target.parent) {
            const is_terminal = target.block.index() < self.analysis.program.blocks.len and
                isTerminal(self.analysis.program.blocks[target.block.index()].terminator);
            if (is_terminal) {
                removed = true;
            } else {
                try blocks.append(self.allocator, target.block);
            }
        }
        if (!removed) return .{ .targets = targets };

        var owned_head: ?*EscapeTarget = null;
        var index = blocks.items.len;
        var owned_count: usize = 0;
        errdefer {
            var cleanup = EscapeTargetProjection{
                .targets = null,
                .owned_head = owned_head,
                .owned_count = owned_count,
            };
            cleanup.deinit(self.allocator);
        }
        while (index != 0) {
            index -= 1;
            const clone = try self.allocator.create(EscapeTarget);
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

    fn noteUnvisitedLoopMember(self: *Builder, membership: []const bool, local_index: usize) void {
        const output = self.collision orelse return;
        if (output.* != null or local_index >= self.analysis.function.blocks.len) return;
        const block = self.analysis.function.blocks[local_index];
        var incoming: ?ir.CfgEdgeRef = null;
        for (0..self.analysis.predecessorCount(block)) |predecessor_index| {
            const predecessor = self.analysis.predecessorAt(block, predecessor_index) orelse continue;
            const predecessor_local = self.analysis.blockIndex(predecessor) orelse continue;
            if (!membership[predecessor_local] or !self.visited[predecessor_local]) continue;
            incoming = directEdgeReference(self.analysis.program, .{ .block = predecessor }, block);
            if (incoming != null) break;
        }
        output.* = .{
            .block = block,
            .previous = if (incoming) |reference| reference.source else null,
            .incoming = incoming,
            .reason = .unvisited_loop_member,
        };
    }

    fn noteUnvisitedReachable(self: *Builder) BuildError!void {
        const output = self.collision orelse return;
        if (output.* != null) return;
        var fallback: ?ir.BlockId = null;
        var frontiers: std.ArrayList(UnvisitedFrontier) = .empty;
        errdefer {
            for (frontiers.items) |frontier| {
                self.allocator.free(frontier.incoming);
                if (frontier.incoming_contexts.len != 0) self.allocator.free(frontier.incoming_contexts);
                self.allocator.free(frontier.closure);
            }
            frontiers.deinit(self.allocator);
        }
        for (self.analysis.function.blocks, 0..) |block, local_index| {
            if (self.visited[local_index] or !self.analysis.isReachable(block)) continue;
            if (fallback == null) fallback = block;
            var incoming: std.ArrayList(ir.CfgEdgeRef) = .empty;
            var incoming_contexts: std.ArrayList(?CollisionContext) = .empty;
            defer incoming.deinit(self.allocator);
            defer incoming_contexts.deinit(self.allocator);
            for (0..self.analysis.predecessorCount(block)) |predecessor_index| {
                const predecessor = self.analysis.predecessorAt(block, predecessor_index) orelse continue;
                const predecessor_local = self.analysis.blockIndex(predecessor) orelse continue;
                if (!self.visited[predecessor_local]) continue;
                const reference = directEdgeReference(self.analysis.program, .{ .block = predecessor }, block) orelse continue;
                try incoming.append(self.allocator, reference);
                try incoming_contexts.append(self.allocator, self.contextForBlock(predecessor));
            }
            if (incoming.items.len == 0) continue;
            const owned_incoming = try incoming.toOwnedSlice(self.allocator);
            const owned_incoming_contexts = try incoming_contexts.toOwnedSlice(self.allocator);
            const closure = self.unvisitedReachableClosureAlloc(block) catch |err| {
                self.allocator.free(owned_incoming);
                self.allocator.free(owned_incoming_contexts);
                return err;
            };
            frontiers.append(self.allocator, .{
                .block = block,
                .incoming = owned_incoming,
                .incoming_contexts = owned_incoming_contexts,
                .closure = closure,
            }) catch |err| {
                self.allocator.free(owned_incoming);
                self.allocator.free(owned_incoming_contexts);
                self.allocator.free(closure);
                return err;
            };
        }
        if (frontiers.items.len != 0) {
            const owned = try frontiers.toOwnedSlice(self.allocator);
            output.* = .{
                .block = owned[0].block,
                .previous = owned[0].incoming[0].source,
                .incoming = owned[0].incoming[0],
                .reason = .unvisited_reachable,
                .incoming_context = self.contextForBlock(owned[0].incoming[0].source),
                .unvisited_frontiers = owned,
            };
            return;
        }
        if (fallback) |block| {
            output.* = .{
                .block = block,
                .previous = null,
                .incoming = null,
                .reason = .unvisited_reachable,
            };
        }
    }

    fn unvisitedReachableClosureAlloc(self: *const Builder, start: ir.BlockId) BuildError![]ir.BlockId {
        const found = try self.allocator.alloc(bool, self.analysis.function.blocks.len);
        defer self.allocator.free(found);
        @memset(found, false);
        var pending: std.ArrayList(ir.BlockId) = .empty;
        defer pending.deinit(self.allocator);
        var closure: std.ArrayList(ir.BlockId) = .empty;
        errdefer closure.deinit(self.allocator);
        try pending.append(self.allocator, start);
        while (pending.pop()) |block| {
            const local_index = self.analysis.blockIndex(block) orelse return error.UnsupportedShape;
            if (found[local_index] or self.visited[local_index] or !self.analysis.isReachable(block)) continue;
            found[local_index] = true;
            try closure.append(self.allocator, block);
            for (0..self.analysis.successorCount(block)) |successor_index| {
                const successor = self.analysis.successorAt(block, successor_index) orelse return error.UnsupportedShape;
                try pending.append(self.allocator, successor);
            }
        }
        return closure.toOwnedSlice(self.allocator);
    }

    fn noteCollisionNode(
        self: *Builder,
        block: ir.BlockId,
        node: ?Node,
        incoming_reference: ?ir.CfgEdgeRef,
        reason: CollisionReason,
        incoming_context: CollisionContext,
    ) BuildError!void {
        const output = self.collision orelse return;
        if (output.* != null) return;
        const previous = if (node) |value| value.blockId() else null;
        if (reason == .already_owned) {
            const owner = self.contextForBlock(block);
            structural_overlap.traceStructural("structural_phase collision_note function={} depth={} block={} previous={?} incoming_source={?} incoming_target={?} owner_start={?} owner_stop={?} owner_loop_exit={?} owner_continue_target={?} incoming_start={} incoming_stop={?} incoming_loop_exit={?} incoming_continue_target={?}\n", .{
                self.analysis.function.id.index(),
                self.trace_region_depth,
                block.index(),
                if (previous) |value| value.index() else null,
                if (incoming_reference) |reference| reference.source.index() else null,
                if (incoming_reference) |reference| reference.target.index() else null,
                if (owner) |context| context.start.index() else null,
                if (owner) |context| if (context.stop) |value| value.index() else null else null,
                if (owner) |context| if (context.loop_exit) |value| value.index() else null else null,
                if (owner) |context| if (context.continue_target) |value| value.index() else null else null,
                incoming_context.start.index(),
                if (incoming_context.stop) |value| value.index() else null,
                if (incoming_context.loop_exit) |value| value.index() else null,
                if (incoming_context.continue_target) |value| value.index() else null,
            });
        }
        var incoming: ?ir.CfgEdgeRef = null;
        var incoming_group: []ir.CfgEdgeRef = &.{};
        // The traversal edge is the ownership collision's actual context.
        // A previous structured node may have a different predecessor into
        // the same block, especially after a parameterized clone. Preserve
        // the supplied edge before consulting node-owned predecessors.
        if (reason == .already_owned) {
            if (incoming_reference) |reference| {
                if (reference.target == block and
                    cfg_edge.value(self.analysis.program, reference) != null)
                {
                    incoming = reference;
                }
            }
        }
        if (incoming == null) {
            if (node) |value| {
                incoming = directEdgeReference(self.analysis.program, value, block);
                if (incoming == null) {
                    const owned = try nodeIncomingEdgesAlloc(self.allocator, self.analysis, value, block);
                    if (owned.len == 1) {
                        incoming = owned[0];
                        self.allocator.free(owned);
                    } else if (owned.len > 1) {
                        incoming = owned[0];
                        incoming_group = owned;
                    } else {
                        self.allocator.free(owned);
                    }
                }
            } else if (reason == .already_owned) {
                // A region may begin at an already-owned block, so there is no
                // preceding structured node from which to recover the entry edge.
                // Preserve the caller's exact edge as a single split candidate.
                // Authentication is not required at this handoff: an
                // unauthenticated entry is precisely the context that the
                // downstream contextual splitter must prove before cloning.
                // Never replace it with an arbitrary predecessor; that loses the
                // value tuple which caused the ownership collision.
                if (incoming_reference) |reference| {
                    if (reference.target == block and
                        cfg_edge.value(self.analysis.program, reference) != null)
                    {
                        incoming = reference;
                    }
                }
                if (incoming == null) {
                    incoming_group = (try stableNodeSplitIncomingGroupAlloc(
                        self.allocator,
                        self.analysis,
                        block,
                    )) orelse &.{};
                }
            }
        }
        if (incoming_group.len > 1) {
            const representative = incoming orelse incoming_group[0];
            incoming_group = try narrowIncomingGroupByArgumentsAlloc(
                self.allocator,
                self.analysis.program,
                incoming_group,
                representative,
            );
            incoming_group = try narrowIncomingGroupByContextAlloc(
                self.allocator,
                self,
                incoming_group,
                representative,
            );
        }
        output.* = .{
            .block = block,
            .previous = previous,
            .incoming = incoming,
            .reason = reason,
            .owner_context = self.contextForBlock(block),
            .incoming_context = incoming_context,
            .incoming_group = incoming_group,
        };
    }

    fn contextForBlock(self: *const Builder, block: ir.BlockId) ?CollisionContext {
        const local_index = self.analysis.blockIndex(block) orelse return null;
        const context = self.visited_contexts[local_index] orelse return null;
        return .{
            .start = context.start,
            .stop = context.stop,
            .loop_exit = context.loop_exit,
            .continue_target = context.continue_target,
            .parameter_arguments = context.parameter_arguments,
        };
    }

    fn parameterProjectionMatches(
        self: *Builder,
        block_id: ir.BlockId,
        expected: ?[]const ir.ValueId,
        actual: ?[]const ir.ValueId,
    ) BuildError!bool {
        self.trace_parameter_calls += 1;
        const trace_start = structural_overlap.structuralPhaseNow();
        defer self.trace_parameter_ms += structural_overlap.structuralPhaseMillis(trace_start);
        if (block_id.index() >= self.analysis.program.blocks.len) return false;
        const block = self.analysis.program.blocks[block_id.index()];
        if (block.id != block_id) return false;
        if (block.parameters.len == 0) {
            return (expected == null or expected.?.len == 0) and
                (actual == null or actual.?.len == 0);
        }
        const expected_arguments = expected orelse return false;
        const actual_arguments = actual orelse return false;
        if (self.replay_context) |context| {
            return try context.parametersEquivalent(block_id, expected_arguments, actual_arguments);
        }
        return expected_arguments.len == block.parameters.len and
            actual_arguments.len == block.parameters.len and
            std.mem.eql(ir.ValueId, expected_arguments, actual_arguments);
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

    fn hasAuthenticatedContinuationBridgeForExpectedParameters(
        self: *Builder,
        reference: ir.CfgEdgeRef,
        expected: ?[]const ir.ValueId,
    ) BuildError!bool {
        if (try self.hasAuthenticatedContinuationBridge(reference)) return true;
        const expected_arguments = expected orelse return false;
        const context = self.replay_context orelse return false;
        const result = try context.hasAuthenticatedIterationContextualProjectionForEdge(
            self.analysis,
            reference,
            expected_arguments,
        );
        if (result) return true;
        // A composed continuation may carry an arbitrary canonical tuple,
        // not only the four values recognized by the iteration witness. Keep
        // this proof at the builder boundary so ownership reuse cannot fall
        // back to repeated collision cloning when replay has already
        // authenticated the complete parameter projection.
        return try context.hasAuthenticatedParameterizedContinuationProjectionForEdge(
            self.analysis,
            reference,
            expected_arguments,
        );
    }

    fn hasAuthenticatedEffectfulEntryBridge(
        self: *const Builder,
        reference: ir.CfgEdgeRef,
        expected_arguments: []const ir.ValueId,
    ) bool {
        return structural_overlap.hasAuthenticatedEffectfulEntryBridgeForEdge(
            self.analysis.program,
            self.analysis,
            reference,
            expected_arguments,
        );
    }

    const AuthenticatedBoundaryProjection = struct {
        target: ir.BlockId,
        edge: ir.Edge,
        continue_projection: bool,
    };

    fn authenticatedUnvisitedBoundaryProjection(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        current_arguments: ?[]const ir.ValueId,
        current_incoming: ?ir.CfgEdgeRef,
    ) BuildError!?AuthenticatedBoundaryProjection {
        const reference = current_incoming orelse return null;
        const arguments = current_arguments orelse return null;
        const replay = self.replay_context orelse return null;
        const projection = try replay.authenticatedContinuationCloneForEdge(self.analysis, reference) orelse return null;
        const root = projection.root;
        const is_continue_boundary = (continue_target != null and continue_target.? == root) or
            isEscapeTarget(continue_targets, root);
        const is_escape_boundary = (stop != null and stop.? == root) or
            (loop_exit != null and loop_exit.? == root) or
            isEscapeTarget(escape_targets, root);
        if (!is_continue_boundary and !is_escape_boundary) return null;

        const root_index = self.analysis.blockIndex(root) orelse return null;
        if (root.index() >= self.analysis.program.blocks.len) return null;
        const root_block = self.analysis.program.blocks[root.index()];
        if (root_block.id != root or
            !node_split.parametersAreCanonical(self.analysis.program.values, root_block)) return null;
        if (current.index() >= self.analysis.program.blocks.len) return null;
        const clone_block = self.analysis.program.blocks[current.index()];
        if (clone_block.id != current or
            !node_split.parametersAreCanonical(self.analysis.program.values, clone_block) or
            root_block.parameters.len != arguments.len or
            clone_block.parameters.len != arguments.len)
        {
            return null;
        }
        if (self.visited[root_index]) {
            const root_context = self.visited_contexts[root_index] orelse return null;
            if (!try self.parameterProjectionMatches(root, root_context.parameter_arguments, arguments)) return null;
        }

        const edge = cfg_edge.value(self.analysis.program, reference) orelse return null;
        if (edge.target != current) return null;
        if (!try self.coverAuthenticatedCloneGroup(
            projection.group,
            current,
            reference.source,
            .{
                .start = start,
                .stop = stop,
                .loop_exit = loop_exit,
                .continue_target = continue_target,
                .parameter_arguments = arguments,
                .entry_reference = reference,
            },
        )) return null;
        return .{
            .target = root,
            .edge = .{ .target = root, .arguments = edge.arguments },
            .continue_projection = is_continue_boundary,
        };
    }

    fn coverAuthenticatedCloneGroup(
        self: *Builder,
        group: ir.NodeSplitGroupId,
        entry: ir.BlockId,
        entry_source: ir.BlockId,
        entry_context: VisitContext,
    ) BuildError!bool {
        var clone_blocks: std.ArrayList(ir.BlockId) = .empty;
        defer clone_blocks.deinit(self.allocator);
        const indexed_rewrites = if (self.replay_context) |replay|
            replay.nodeSplitRewriteIndicesForGroup(group)
        else
            &.{};
        if (indexed_rewrites.len != 0 or self.replay_context != null) {
            for (indexed_rewrites) |rewrite_index| {
                const rewrite = self.analysis.program.edge_rewrites[rewrite_index];
                const target_index = self.analysis.blockIndex(rewrite.to.target) orelse return false;
                if (!self.analysis.isReachable(rewrite.to.target)) return false;
                var duplicate = false;
                for (clone_blocks.items) |existing| {
                    if (existing == rewrite.to.target) duplicate = true;
                }
                if (!duplicate) try clone_blocks.append(self.allocator, rewrite.to.target);
                _ = target_index;
            }
        } else for (self.analysis.program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.node_split_group != group) continue;
            const target_index = self.analysis.blockIndex(rewrite.to.target) orelse return false;
            if (!self.analysis.isReachable(rewrite.to.target)) return false;
            var duplicate = false;
            for (clone_blocks.items) |existing| {
                if (existing == rewrite.to.target) duplicate = true;
            }
            if (!duplicate) try clone_blocks.append(self.allocator, rewrite.to.target);
            _ = target_index;
        }
        if (clone_blocks.items.len == 0) return false;
        var contains_entry = false;
        for (clone_blocks.items) |block_id| {
            if (block_id == entry) contains_entry = true;
        }
        if (!contains_entry) return false;

        const authenticated_entries = try self.allocator.alloc(bool, clone_blocks.items.len);
        defer self.allocator.free(authenticated_entries);
        @memset(authenticated_entries, false);

        // A clone group is a closed structural body.  Any predecessor from
        // outside the group must be one of the authenticated entry rewrites;
        // otherwise covering it would hide an independent live path.
        for (clone_blocks.items, 0..) |block_id, clone_index| {
            for (0..self.analysis.predecessorCount(block_id)) |predecessor_index| {
                const predecessor = self.analysis.predecessorAt(block_id, predecessor_index) orelse return false;
                var owned_predecessor = false;
                for (clone_blocks.items) |candidate| {
                    if (candidate == predecessor) owned_predecessor = true;
                }
                if (owned_predecessor) continue;
                const reference = directEdgeReference(self.analysis.program, .{ .block = predecessor }, block_id) orelse return false;
                var authenticated_entry = reference.source == entry_source;
                if (!authenticated_entry) {
                    if (self.replay_context) |replay| {
                        authenticated_entry = replay.hasNodeSplitEntryEdge(
                            reference.source,
                            reference.kind,
                            block_id,
                            group,
                        );
                    } else {
                        for (self.analysis.program.edge_rewrites) |rewrite| {
                            if (rewrite.rule == .node_split and rewrite.node_split_group == group and
                                rewrite.source == reference.source and rewrite.kind == reference.kind and
                                rewrite.to.target == block_id)
                            {
                                authenticated_entry = true;
                                break;
                            }
                        }
                    }
                }
                if (!authenticated_entry) return false;
                authenticated_entries[clone_index] = true;
            }
        }

        for (clone_blocks.items, 0..) |block_id, clone_index| {
            const local_index = self.analysis.blockIndex(block_id) orelse return false;
            try self.markVisited(local_index);
            if (block_id == entry) {
                // The exact incoming edge authenticated this clone entry. If
                // it was newly covered, retain that caller-owned context so a
                // later traversal can identify the owner without reconstructing
                // it from equality or reachability.
                if (self.visited_contexts[local_index] == null) {
                    try self.setVisitedContext(local_index, entry_context);
                }
            } else if (!authenticated_entries[clone_index]) {
                try self.setVisitedContext(local_index, null);
            }
        }
        return true;
    }

    fn hasStableNodeSplitBridgeFromNode(
        self: *Builder,
        node: Node,
        target: ir.BlockId,
    ) BuildError!bool {
        return hasStableNodeSplitBridgeFromNodeWithContext(
            self.allocator,
            self.analysis,
            node,
            target,
            self.replay_context,
        );
    }

    // A raw structured join can lose its live tuple when both branch arms
    // finish and the builder transfers to the join. Recover that tuple only
    // for a branch-owned edge whose arguments are the complete positional
    // tuple of a dominating block-parameter producer. This proves a real
    // forwarding contract without comparing it to, or guessing, the owner's
    // visit tuple. Split/replay edges use the stronger bridge proofs above.
    fn hasAuthenticatedRawParameterizedJoinEdge(
        self: *Builder,
        node: Node,
        target: ir.BlockId,
        reference: ir.CfgEdgeRef,
    ) BuildError!bool {
        if (node != .branch or
            !isParameterizedNumericTransitionHeader(self.analysis.program, target) or
            reference.target != target)
        {
            return false;
        }
        if (target.index() >= self.analysis.program.blocks.len or
            reference.source.index() >= self.analysis.program.blocks.len)
        {
            return false;
        }
        const target_block = self.analysis.program.blocks[target.index()];
        const source_block = self.analysis.program.blocks[reference.source.index()];
        if (target_block.id != target or source_block.id != reference.source or
            source_block.function != self.analysis.function.id or
            target_block.function != source_block.function)
        {
            return false;
        }
        const edge = cfg_edge.value(self.analysis.program, reference) orelse return false;
        if (edge.target != target or edge.arguments.len != target_block.parameters.len) return false;

        // A raw proof must not consume an edge that a later replay pass owns.
        for (self.analysis.program.edge_rewrites) |rewrite| {
            if (rewrite.rule == .node_split and rewrite.source == reference.source and
                rewrite.kind == reference.kind and rewrite.to.target == target)
            {
                return false;
            }
        }

        var producer: ?ir.BlockId = null;
        for (edge.arguments, 0..) |argument, index| {
            if (argument.index() >= self.analysis.program.values.len) return false;
            const value = self.analysis.program.values[argument.index()];
            if (value.id != argument or value.function != target_block.function) return false;
            const origin = switch (value.origin) {
                .block_parameter => |parameter| parameter,
                else => return false,
            };
            if (origin.index != index) return false;
            if (producer) |selected| {
                if (selected != origin.block) return false;
            } else {
                producer = origin.block;
            }
            if (origin.block.index() >= self.analysis.program.blocks.len or
                self.analysis.program.blocks[origin.block.index()].id != origin.block)
            {
                return false;
            }
            const producer_block = self.analysis.program.blocks[origin.block.index()];
            if (index >= producer_block.parameters.len or producer_block.parameters[index] != argument or
                !structural_overlap.continuationParameterAcceptsValueType(
                    self.analysis.program,
                    target_block.parameters[index],
                    argument,
                ))
            {
                return false;
            }
        }

        const selected_producer = producer orelse return false;
        if (selected_producer == target or
            selected_producer.index() >= self.analysis.program.blocks.len or
            !self.analysis.isReachable(selected_producer) or
            !self.analysis.isReachable(reference.source))
        {
            return false;
        }
        const producer_reaches_source = try self.analysis.canReach(selected_producer, reference.source);
        const dominated_entry = self.analysis.dominates(selected_producer, reference.source) and
            producer_reaches_source;
        const loop_carried_entry = try self.analysis.canReach(target, selected_producer) and
            producer_reaches_source and
            try self.analysis.canReach(reference.source, target);
        return dominated_entry or loop_carried_entry;
    }

    fn authenticatedUniqueOwnedIncomingEntry(
        self: *Builder,
        node: Node,
        target: ir.BlockId,
        expected_arguments: ?[]const ir.ValueId,
    ) BuildError!?OwnedIncomingEntry {
        // A direct block predecessor can be the exact retained edge of a
        // structured numeric continuation. It is safe to recover only
        // through the same canonical tuple and authenticated iteration proof
        // used for structured branch entries below.
        if (target.index() >= self.analysis.program.blocks.len) return null;
        const target_block = self.analysis.program.blocks[target.index()];
        if (target_block.id != target) return null;

        const incoming = try nodeIncomingEdgesAlloc(self.allocator, self.analysis, node, target);
        defer self.allocator.free(incoming);
        const reference = if (incoming.len == 1)
            incoming[0]
        else
            try self.authenticatedEquivalentOwnedParameterizedJoinEntry(
                node,
                target,
                incoming,
                expected_arguments,
            ) orelse return null;
        const edge = cfg_edge.value(self.analysis.program, reference) orelse return null;
        if (edge.target != target or edge.arguments.len != target_block.parameters.len) return null;
        if (expected_arguments) |expected| {
            if (!std.mem.eql(ir.ValueId, expected, edge.arguments)) return null;
        }
        if (!try self.hasAuthenticatedContinuationBridge(reference) and
            !try self.hasAuthenticatedRawParameterizedJoinEdge(node, target, reference)) return null;
        return .{ .reference = reference, .arguments = edge.arguments };
    }

    // Multiple owned entries are safe to project only when the structured
    // branch itself contributes one authenticated anchor. Every other owned
    // entry must carry the exact same complete tuple and independently prove
    // that tuple through replay or the raw positional producer contract. A
    // set of unrelated nested predecessors has no anchor and remains a
    // collision, even when their value IDs happen to be equal.
    fn authenticatedEquivalentOwnedParameterizedJoinEntry(
        self: *Builder,
        node: Node,
        target: ir.BlockId,
        incoming: []const ir.CfgEdgeRef,
        expected_arguments: ?[]const ir.ValueId,
    ) BuildError!?ir.CfgEdgeRef {
        if (incoming.len < 2 or node != .branch or
            !isParameterizedNumericTransitionHeader(self.analysis.program, target)) return null;

        const anchor_source = node.blockId();
        var anchor: ?ir.CfgEdgeRef = null;
        for (incoming) |reference| {
            if (reference.source != anchor_source) continue;
            if (anchor != null) return null;
            anchor = reference;
        }
        const selected = if (anchor) |reference| reference else blk: {
            // A structured branch may converge through nested arms, leaving
            // no direct edge from the branch header to the numeric target.
            // Treat its common transition tuple as an anchor only when every
            // owned edge carries the exact same tuple and independently
            // authenticates that tuple against the prior owner entry.
            const expected = expected_arguments orelse return null;
            const replay_context = self.replay_context orelse return null;
            const representative = incoming[0];
            const representative_edge = cfg_edge.value(self.analysis.program, representative) orelse return null;
            for (incoming) |reference_| {
                const edge = cfg_edge.value(self.analysis.program, reference_) orelse return null;
                if (edge.target != target or
                    edge.arguments.len != representative_edge.arguments.len or
                    !std.mem.eql(ir.ValueId, edge.arguments, representative_edge.arguments) or
                    !try replay_context.hasAuthenticatedIterationContextualProjectionForEdge(
                        self.analysis,
                        reference_,
                        expected,
                    ))
                {
                    return null;
                }
            }
            break :blk representative;
        };
        const selected_edge = cfg_edge.value(self.analysis.program, selected) orelse return null;
        const target_block = self.analysis.program.blocks[target.index()];
        if (selected_edge.target != target or
            selected_edge.arguments.len != target_block.parameters.len)
        {
            return null;
        }

        for (incoming) |reference| {
            const edge = cfg_edge.value(self.analysis.program, reference) orelse return null;
            if (edge.target != target or
                edge.arguments.len != target_block.parameters.len or
                !std.mem.eql(ir.ValueId, edge.arguments, selected_edge.arguments))
            {
                return null;
            }
            if (!try self.hasAuthenticatedContinuationBridge(reference) and
                !try self.hasAuthenticatedRawParameterizedJoinEdge(node, target, reference))
            {
                return null;
            }
        }
        return selected;
    }

    // A structured branch join may retain the continuation projection while
    // clearing its live edge and argument tuple. Numeric re-entry still needs
    // that exact edge for contextual iteration proof; recover it only when
    // the node has one incoming edge, or a branch-owned set of equivalent
    // incoming edges, and the solver-neutral iteration witness authenticates
    // the complete owner tuple.
    fn authenticatedUniqueIncomingIterationEntry(
        self: *Builder,
        node: Node,
        target: ir.BlockId,
        expected_arguments: ?[]const ir.ValueId,
    ) BuildError!?OwnedIncomingEntry {
        const trace_entry = self.trace_iteration_entry_calls < 256;
        if (trace_entry) self.trace_iteration_entry_calls += 1;
        const node_kind = switch (node) {
            .block => "block",
            .branch => "branch",
            .loop => "loop",
            .latch_loop => "latch_loop",
            .infinite_loop => "infinite_loop",
            .loop_control => "loop_control",
            .loop_boundary => "loop_boundary",
            .loop_terminal => "loop_terminal",
        };
        if (trace_entry) {
            structural_overlap.traceStructural("structural_phase iteration_entry_probe node_kind={s} node={} target={} expected_len={?}\n", .{
                node_kind,
                node.blockId().index(),
                target.index(),
                if (expected_arguments) |arguments| arguments.len else null,
            });
        }
        const expected = expected_arguments orelse return null;
        if (expected.len == 0 or !isParameterizedNumericTransitionHeader(self.analysis.program, target)) return null;
        if (target.index() >= self.analysis.program.blocks.len) return null;
        const target_block = self.analysis.program.blocks[target.index()];
        if (target_block.id != target or target_block.parameters.len != expected.len or
            !node_split.parametersAreCanonical(self.analysis.program.values, target_block))
        {
            return null;
        }

        const incoming = if (node == .block)
            try self.allocator.dupe(ir.CfgEdgeRef, &.{directEdgeReference(
                self.analysis.program,
                node,
                target,
            ) orelse return null})
        else
            try nodeIncomingEdgesAlloc(self.allocator, self.analysis, node, target);
        defer self.allocator.free(incoming);
        if (trace_entry) {
            structural_overlap.traceStructural("structural_phase iteration_entry_shape node_kind={s} node={} target={} owned_incoming={}\n", .{
                node_kind,
                node.blockId().index(),
                target.index(),
                incoming.len,
            });
            for (incoming) |reference| {
                const edge = cfg_edge.value(self.analysis.program, reference);
                structural_overlap.traceStructural("structural_phase iteration_entry_shape_edge source={} kind={s} target={} args={any} edge_present={}\n", .{
                    reference.source.index(),
                    @tagName(reference.kind),
                    reference.target.index(),
                    if (edge) |value| value.arguments else &.{},
                    edge != null,
                });
            }
        }
        if (incoming.len == 0) return null;
        const reference = if (incoming.len == 1)
            incoming[0]
        else
            try self.authenticatedEquivalentOwnedParameterizedJoinEntry(
                node,
                target,
                incoming,
                expected_arguments,
            ) orelse return null;
        const edge = cfg_edge.value(self.analysis.program, reference) orelse return null;
        if (edge.target != target or edge.arguments.len != target_block.parameters.len) return null;
        const replay_context = self.replay_context orelse return null;
        const authenticated = try replay_context.hasAuthenticatedIterationContextualProjectionForEdge(
            self.analysis,
            reference,
            expected,
        );
        if (trace_entry) {
            structural_overlap.traceStructural("structural_phase iteration_entry_recovery node_kind={s} node={} target={} source={} expected={any} actual={any} authenticated={}\n", .{
                node_kind,
                node.blockId().index(),
                target.index(),
                reference.source.index(),
                expected,
                edge.arguments,
                authenticated,
            });
        }
        if (!authenticated) return null;
        return .{ .reference = reference, .arguments = edge.arguments };
    }

    fn visitedEntryContinuationProjection(
        self: *Builder,
        node: Node,
        target: ir.BlockId,
        incoming: ?ir.CfgEdgeRef,
        arguments: ?[]const ir.ValueId,
    ) BuildError!?VisitedEntryProjection {
        self.trace_projection_calls += 1;
        const trace_start = structural_overlap.structuralPhaseNow();
        defer self.trace_projection_ms += structural_overlap.structuralPhaseMillis(trace_start);
        if (continuationProjectionForVisitedEntry(
            self.analysis.program,
            node,
            target,
            incoming,
            arguments,
        )) |projection| {
            // A structured join reports a transferred projection without
            // retaining the live edge.  That is sufficient for a zero-
            // parameter continuation, but it is not a parameter projection:
            // a later owner comparison must not silently treat an unknown
            // tuple as equivalent to the target's formals. Recover one
            // authenticated owned edge before accepting the transfer.
            if (projection == .transferred and target.index() < self.analysis.program.blocks.len) {
                const target_block = self.analysis.program.blocks[target.index()];
                const missing_parameters = target_block.parameters.len != 0 and
                    (arguments == null or arguments.?.len != target_block.parameters.len);
                if (missing_parameters) {
                    if (try self.authenticatedUniqueOwnedIncomingEntry(node, target, null)) |entry| {
                        return .{
                            .projection = projection,
                            .arguments = entry.arguments,
                            .recovered_context_arguments = true,
                            .recovered_context_reference = entry.reference,
                        };
                    }
                    return null;
                }
            }
            return .{
                .projection = projection,
                .arguments = arguments,
                .recovered_context_arguments = false,
                .recovered_context_reference = null,
            };
        }

        // A branch join intentionally clears the live edge and tuple because
        // its arms may have distinct incoming state. Reconstruct that state
        // only for one owned predecessor whose clone/replay lineage is
        // already authenticated. Ambiguous or unauthenticated joins remain
        // collisions.
        if (incoming != null) {
            return null;
        }
        const recovered = try self.authenticatedUniqueOwnedIncomingEntry(node, target, arguments);
        if (recovered) |entry| {
            if (continuationProjectionForVisitedEntry(
                self.analysis.program,
                node,
                target,
                entry.reference,
                entry.arguments,
            )) |projection| {
                return .{
                    .projection = projection,
                    .arguments = entry.arguments,
                    .recovered_context_arguments = true,
                    .recovered_context_reference = entry.reference,
                };
            }
        }
        return null;
    }

    // A loop-carried transition may reach an earlier block only by crossing
    // the enclosing continuation boundary. Treat that backedge as the
    // structured region boundary; a path that reaches the block without
    // crossing it is still an ownership collision.
    fn canReachWithoutContinuationBoundary(
        self: *const Builder,
        source: ir.BlockId,
        target: ir.BlockId,
        continuation: ?ir.BlockId,
    ) BuildError!bool {
        const mutable_self = @constCast(self);
        mutable_self.trace_reach_calls += 1;
        const trace_start = structural_overlap.structuralPhaseNow();
        defer mutable_self.trace_reach_ms += structural_overlap.structuralPhaseMillis(trace_start);
        if (!try self.analysis.canReach(source, target)) return false;
        const boundary = continuation orelse return true;
        if (boundary == source or boundary == target) return true;
        return try self.analysis.canReachAvoiding(source, target, boundary);
    }

    // A zero-argument loop header may be entered again with a different
    // nested stop boundary. Reuse it only when both visits retain the same
    // loop controls and the header carries no block parameters or effects.
    // Its outgoing edge may carry a canonical successor tuple because the
    // empty header itself does not create or consume that state.
    fn zeroArgumentLoopContinuationContextMatches(
        self: *const Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
    ) bool {
        if (!parameters_match or current != start or context.start != start or
            context.stop == stop or context.loop_exit != loop_exit or
            context.continue_target != continue_target or stop == null or
            context.stop == null or loop_exit == null or continue_target == null)
        {
            return false;
        }
        const local_index = self.analysis.blockIndex(current) orelse return false;
        if (local_index >= self.loop_headers.len or !self.loop_headers[local_index]) return false;
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or block.parameters.len != 0) return false;
        if (block.instructions.len != 0) return false;
        return switch (block.terminator) {
            .branch => |branch| blk: {
                if (branch.then_edge.arguments.len != 0 or branch.else_edge.arguments.len != 0) break :blk false;
                const then_is_continue = branch.then_edge.target == continue_target.?;
                const else_is_continue = branch.else_edge.target == continue_target.?;
                const then_is_exit = branch.then_edge.target == loop_exit.?;
                const else_is_exit = branch.else_edge.target == loop_exit.?;
                break :blk (then_is_continue and else_is_exit) or (else_is_continue and then_is_exit);
            },
            .jump, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => self.transparentEmptyJumpWithCanonicalSuccessor(current),
        };
    }

    // An empty block is a semantic identity even when its jump carries values
    // into a parameterized successor. Keep the proof local to the admitted
    // CFG: the successor must be in the same function, have canonical formals,
    // and receive exactly one argument per formal.
    fn transparentEmptyJumpWithCanonicalSuccessor(
        self: *const Builder,
        current: ir.BlockId,
    ) bool {
        if (current.index() >= self.analysis.program.blocks.len) return false;
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or block.parameters.len != 0 or block.instructions.len != 0) return false;
        const outgoing = switch (block.terminator) {
            .jump => |edge| edge,
            .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
        };
        if (outgoing.target == current or outgoing.target.index() >= self.analysis.program.blocks.len) return false;
        const successor = self.analysis.program.blocks[outgoing.target.index()];
        return successor.id == outgoing.target and
            successor.function == block.function and
            outgoing.arguments.len == successor.parameters.len and
            (successor.parameters.len == 0 or
                node_split.parametersAreCanonical(self.analysis.program.values, successor));
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

    // A numeric transition may be revisited with a distinct SSA tuple when
    // the incoming edge carries the complete replay-authenticated state
    // produced by another numeric transition. Keep this proof separate from
    // ordinary parameter equality: the contextual iteration witness checks
    // every carried slot and the live owner edge.
    fn authenticatedDistinctNumericTuple(
        self: *Builder,
        current: ir.BlockId,
        context: VisitContext,
        incoming: ?ir.CfgEdgeRef,
        parameters_match: bool,
    ) BuildError!bool {
        if (parameters_match or
            !isParameterizedNumericTransitionHeader(self.analysis.program, current))
        {
            return false;
        }
        const reference = incoming orelse return false;
        if (reference.target != current) return false;
        const expected = context.parameter_arguments orelse return false;
        const replay_context = self.replay_context orelse return false;
        return try replay_context.hasAuthenticatedIterationContextualProjectionForEdge(
            self.analysis,
            reference,
            expected,
        );
    }

    fn authenticatedSameEntryNumericReentry(
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
        if (current != start or context.start != start or
            !isParameterizedNumericTransitionHeader(self.analysis.program, current) or
            context.loop_exit != loop_exit or
            (context.stop == stop and context.continue_target == continue_target))
        {
            return false;
        }
        const distinct_tuple = try self.authenticatedDistinctNumericTuple(
            current,
            context,
            incoming,
            parameters_match,
        );
        if (!parameters_match and !distinct_tuple) return false;
        if (incoming == null) return false;
        const reference = incoming.?;
        if (reference.target != current) return false;
        if (distinct_tuple) return true;
        self.trace_bridge_calls += 1;
        const bridge_start = structural_overlap.structuralPhaseNow();
        // A loop-carried numeric transition can be represented by its
        // authenticated state projection after a split has forwarded the
        // edge.  Preserve the direct bridge requirement, but allow the
        // solver-neutral iteration witness to authenticate that equivalent
        // continuation when no standalone node-split record remains.
        const result = try self.hasAuthenticatedContinuationBridgeForExpectedParameters(
            reference,
            context.parameter_arguments,
        );
        self.trace_bridge_ms += structural_overlap.structuralPhaseMillis(bridge_start);
        if (result) return true;
        const expected = context.parameter_arguments orelse return false;
        const replay_context = self.replay_context orelse return false;
        // Direct clone history and the four-slot iteration witness do not
        // cover a composed arbitrary-length continuation tuple. Reuse the
        // existing replay-equivalence proof at this ownership boundary so a
        // proven parameterized suffix is not cloned once per enclosing stop.
        return try replay_context.hasAuthenticatedParameterizedContinuationProjectionForEdge(
            self.analysis,
            reference,
            expected,
        );
    }

    // A same-entry parameterized continuation may be projected across a
    // different enclosing boundary only when the target is a transparent
    // forwarding block.  The tuple and edge witnesses establish which values
    // arrive, but they do not make an already-emitted block's instructions or
    // branch execute again.  Effectful/shared targets must be cloned or make
    // this structured plan fail so the caller can use its CFG fallback.
    fn authenticatedSameEntryParameterizedReentry(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
        arguments: ?[]const ir.ValueId,
        incoming: ?ir.CfgEdgeRef,
    ) BuildError!bool {
        if (!parameters_match or current != start or context.start != start or
            context.loop_exit != loop_exit or
            (context.stop == stop and context.continue_target == continue_target))
        {
            return false;
        }

        const current_arguments = arguments orelse return false;
        if (current.index() >= self.analysis.program.blocks.len) return false;
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or block.parameters.len == 0 or
            current_arguments.len != block.parameters.len or
            !node_split.parametersAreCanonical(self.analysis.program.values, block))
        {
            return false;
        }
        if (block.instructions.len != 0) return false;
        switch (block.terminator) {
            .jump => {},
            else => return false,
        }

        if (incoming == null) {
            return try self.hasAuthenticatedUniqueIncomingParameterizedBridge(
                current,
                context.parameter_arguments,
                arguments,
            );
        }
        const reference = incoming.?;
        if (reference.target != current) return false;
        self.trace_bridge_calls += 1;
        const bridge_start = structural_overlap.structuralPhaseNow();
        // The same-entry edge may be the composed state transition of a
        // parameterized continuation rather than a direct clone bridge.
        // Require the owner tuple and the complete iteration projection in
        // that case; do not infer reuse from reachability or raw equality.
        const result = try self.hasAuthenticatedContinuationBridgeForExpectedParameters(
            reference,
            context.parameter_arguments,
        );
        self.trace_bridge_ms += structural_overlap.structuralPhaseMillis(bridge_start);
        return result;
    }

    // A parameterized branch header can be revisited from its own region
    // after an effectful nested path produces a distinct tuple.  This is a
    // loop-carried state transfer, not ordinary parameter equality: require
    // a canonical formal tuple, a genuine SCC backedge, one exact owner
    // entry, and the existing solver-neutral replay proof for that edge.
    fn authenticatedSameContextDistinctParameterizedReentry(
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
        if (parameters_match or current != start or context.start != current or
            context.stop != stop or context.loop_exit != loop_exit or
            context.continue_target != continue_target)
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
        if (current.index() >= self.analysis.program.blocks.len) return false;
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or block.parameters.len == 0 or
            !node_split.parametersAreCanonical(self.analysis.program.values, block))
        {
            return false;
        }

        const expected = context.parameter_arguments orelse return false;
        if (expected.len != block.parameters.len) return false;
        const incoming_edge = cfg_edge.value(self.analysis.program, reference) orelse return false;
        if (incoming_edge.target != current or
            incoming_edge.arguments.len != block.parameters.len or
            std.mem.eql(ir.ValueId, expected, incoming_edge.arguments))
        {
            return false;
        }

        var owner_reference = context.entry_reference;
        if (owner_reference == null) {
            var recovered: ?ir.CfgEdgeRef = null;
            for (0..self.analysis.predecessorCount(current)) |predecessor_index| {
                const predecessor = self.analysis.predecessorAt(current, predecessor_index) orelse continue;
                if (!self.analysis.isReachable(predecessor) or
                    try self.analysis.canReach(current, predecessor)) continue;
                const candidate = directEdgeReference(
                    self.analysis.program,
                    .{ .block = predecessor },
                    current,
                ) orelse continue;
                const candidate_edge = cfg_edge.value(self.analysis.program, candidate) orelse continue;
                if (!std.mem.eql(ir.ValueId, candidate_edge.arguments, expected)) continue;
                if (recovered != null) return false;
                recovered = candidate;
            }
            owner_reference = recovered;
        }
        const owner = owner_reference orelse return false;
        if (owner.target != current or std.meta.eql(owner, reference)) return false;
        const owner_edge = cfg_edge.value(self.analysis.program, owner) orelse return false;
        if (owner_edge.target != current or
            owner_edge.arguments.len != block.parameters.len or
            !std.mem.eql(ir.ValueId, owner_edge.arguments, expected) or
            std.mem.eql(ir.ValueId, owner_edge.arguments, incoming_edge.arguments))
        {
            return false;
        }

        const replay = self.replay_context orelse return false;
        const result = try replay.hasAuthenticatedParameterizedContinuationProjectionForEdge(
            self.analysis,
            reference,
            owner_edge.arguments,
        );
        structural_overlap.traceStructural(
            "structural_phase same_context_parameterized_reentry current={} owner_source={} incoming_source={} result={} owner_arguments={any} incoming_arguments={any}\n",
            .{
                current.index(),
                owner.source.index(),
                reference.source.index(),
                result,
                owner_edge.arguments,
                incoming_edge.arguments,
            },
        );
        return result;
    }

    // A structured loop transfer can first visit a parameterized block after
    // the original traversal edge was cleared. Recover the owner edge only
    // when the live CFG has exactly one reachable predecessor outside the
    // current SCC and its complete tuple differs from the incoming edge.
    // Ambiguous or same-tuple predecessors remain unauthenticated.
    fn recoverUniqueOwnerEntryReference(
        self: *Builder,
        current: ir.BlockId,
        context: VisitContext,
        incoming: ir.CfgEdgeRef,
    ) BuildError!?ir.CfgEdgeRef {
        if (incoming.target != current) return null;
        if (isParameterizedNumericTransitionHeader(self.analysis.program, current) and
            self.analysis.predecessorCount(current) > 1)
        {
            structural_overlap.traceStructural(
                "structural_phase owner_edge_recovery_enter current={} context_start={} context_entry_source={?} incoming_source={}\n",
                .{
                    current.index(),
                    context.start.index(),
                    if (context.entry_reference) |reference| reference.source.index() else null,
                    incoming.source.index(),
                },
            );
        }
        if (context.entry_reference) |reference| {
            return if (reference.target == current) reference else null;
        }
        const current_block = if (current.index() < self.analysis.program.blocks.len)
            self.analysis.program.blocks[current.index()]
        else
            return null;
        if (current_block.id != current or current_block.parameters.len == 0) return null;
        const incoming_edge = cfg_edge.value(self.analysis.program, incoming) orelse return null;
        const trace_owner_candidates = isParameterizedNumericTransitionHeader(self.analysis.program, current) and
            self.analysis.predecessorCount(current) > 1 and
            try self.analysis.canReach(current, incoming.source) and
            try self.analysis.canReach(incoming.source, current);
        // A loop can leave a parameterized continuation through several
        // authenticated arms after the structured traversal has cleared its
        // transient entry tuple. Those arms are interchangeable only when
        // they are direct rewrites of the same canonical target in one split
        // group. Keep the ordinary unique-owner rule for every other shape.
        const allow_shared_node_split_arms =
            isParameterizedNumericTransitionHeader(self.analysis.program, current) and
            context.parameter_arguments == null;
        var shared_node_split_source: ?ir.BlockId = null;
        var shared_node_split_group: ?ir.NodeSplitGroupId = null;
        if (trace_owner_candidates) {
            structural_overlap.traceStructural(
                "structural_phase owner_edge_candidates current={} context_start={} incoming_source={} incoming_arguments={any}\n",
                .{ current.index(), context.start.index(), incoming.source.index(), incoming_edge.arguments },
            );
        }

        var recovered: ?ir.CfgEdgeRef = null;
        for (0..self.analysis.predecessorCount(current)) |predecessor_index| {
            const predecessor = self.analysis.predecessorAt(current, predecessor_index) orelse continue;
            const reference = directEdgeReference(
                self.analysis.program,
                .{ .block = predecessor },
                current,
            ) orelse continue;
            if (std.meta.eql(reference, incoming) or
                !self.analysis.isReachable(predecessor) or
                !try self.analysis.canReach(context.start, predecessor) or
                (context.start != predecessor and
                    !try self.analysis.canReachAvoiding(context.start, predecessor, current)) or
                try self.analysis.canReach(current, predecessor))
            {
                if (trace_owner_candidates) {
                    structural_overlap.traceStructural(
                        "structural_phase owner_edge_candidate source={} accepted_by_reachability=false context_to_source={} source_to_current={} current_to_source={} arguments={any}\n",
                        .{
                            predecessor.index(),
                            try self.analysis.canReach(context.start, predecessor),
                            try self.analysis.canReach(predecessor, current),
                            try self.analysis.canReach(current, predecessor),
                            (cfg_edge.value(self.analysis.program, reference) orelse continue).arguments,
                        },
                    );
                }
                continue;
            }
            const owner_edge = cfg_edge.value(self.analysis.program, reference) orelse continue;
            if (trace_owner_candidates) {
                const iteration_projection = if (self.replay_context) |replay|
                    try replay.hasAuthenticatedIterationContextualProjectionForEdge(
                        self.analysis,
                        incoming,
                        owner_edge.arguments,
                    )
                else
                    false;
                const continuation_bridge = try self.hasAuthenticatedContinuationBridge(reference);
                structural_overlap.traceStructural(
                    "structural_phase owner_edge_candidate source={} accepted_by_reachability=true continuation_bridge={} iteration_projection={} arguments={any}\n",
                    .{ predecessor.index(), continuation_bridge, iteration_projection, owner_edge.arguments },
                );
            }
            if (owner_edge.target != current or
                owner_edge.arguments.len != current_block.parameters.len or
                owner_edge.arguments.len != incoming_edge.arguments.len or
                std.mem.eql(ir.ValueId, owner_edge.arguments, incoming_edge.arguments))
            {
                continue;
            }
            if (allow_shared_node_split_arms) {
                var found_split_arm = false;
                var split_source: ?ir.BlockId = null;
                var split_group: ?ir.NodeSplitGroupId = null;
                for (self.analysis.program.edge_rewrites) |rewrite| {
                    if (rewrite.rule != .node_split or
                        rewrite.source != reference.source or
                        rewrite.kind != reference.kind or
                        rewrite.to.target != current or
                        !std.mem.eql(ir.ValueId, rewrite.to.arguments, owner_edge.arguments) or
                        rewrite.node_split_group == null)
                    {
                        continue;
                    }
                    if (found_split_arm) return null;
                    found_split_arm = true;
                    split_source = rewrite.from.target;
                    split_group = rewrite.node_split_group;
                }
                if (!found_split_arm) return null;
                if (shared_node_split_source) |source| {
                    if (source != split_source.? or shared_node_split_group.? != split_group.?) return null;
                } else {
                    shared_node_split_source = split_source;
                    shared_node_split_group = split_group;
                }
            }
            if (recovered != null and !allow_shared_node_split_arms) return null;
            recovered = reference;
        }
        if (recovered) |reference| {
            structural_overlap.traceStructural(
                "structural_phase recovered_unique_owner_edge current={} source={} target={}\\n",
                .{ current.index(), reference.source.index(), reference.target.index() },
            );
        }
        return recovered;
    }

    // An already-owned parameterized continuation can be reached as the
    // empty remainder of a region whose start differs from the owner.  The
    // ordinary empty projection only accepts a direct clone bridge.  Permit
    // this loop-carried form when the incoming edge is in the same SCC and
    // the complete owner tuple is authenticated by replay or iteration
    // projection.  Reverse reachability is essential: without it, this
    // would silently erase an acyclic effectful prefix.
    fn authenticatedSameSccParameterizedReentry(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
        incoming: ?ir.CfgEdgeRef,
    ) BuildError!bool {
        if (context.start == start or
            context.loop_exit != loop_exit or
            context.continue_target != continue_target)
        {
            return false;
        }
        const reference = incoming orelse return false;
        if (reference.target != current or
            !try self.analysis.canReach(current, reference.source))
        {
            return false;
        }
        if (current.index() >= self.analysis.program.blocks.len) return false;
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or block.parameters.len == 0 or
            !node_split.parametersAreCanonical(self.analysis.program.values, block))
        {
            return false;
        }
        const owner_reference = (try self.recoverUniqueOwnerEntryReference(
            current,
            context,
            reference,
        )) orelse return false;
        const owner_edge = cfg_edge.value(self.analysis.program, owner_reference) orelse return false;
        const incoming_edge = cfg_edge.value(self.analysis.program, reference) orelse return false;
        if (owner_edge.target != current or
            owner_edge.arguments.len != block.parameters.len or
            incoming_edge.target != current or
            incoming_edge.arguments.len != block.parameters.len)
        {
            return false;
        }
        // A numeric transition has a stronger solver-neutral witness than a
        // generic continuation bridge: its complete owner tuple is replayed
        // through the transition's normalized result tuple. Reuse that proof
        // for a distinct-tuple same-SCC reentry after the surrounding
        // ownership and reverse-reachability checks above have authenticated
        // the boundary.
        if (!parameters_match and
            try self.authenticatedDistinctNumericTuple(current, context, reference, parameters_match))
        {
            return true;
        }
        // A nested numeric loop can carry a fresh tuple through a
        // parameterized carrier before returning to an already-owned outer
        // header. The carrier proof is independent of the enclosing stop,
        // but it must still agree with the owner context's exact entry tuple
        // when that tuple survived the structured handoff. A shared split-arm
        // handoff has no single owner tuple; the carrier proof authenticates
        // the incoming state directly in that bounded case.
        if (!parameters_match and isParameterizedNumericTransitionHeader(self.analysis.program, current)) {
            if (context.parameter_arguments) |expected| {
                if (std.mem.eql(ir.ValueId, expected, owner_edge.arguments)) {
                    const replay = self.replay_context orelse return false;
                    if (try replay.hasAuthenticatedNumericIterationCarrierReentryForEdge(
                        self.analysis,
                        current,
                        reference,
                    )) return true;
                }
            } else {
                const replay = self.replay_context orelse return false;
                if (try replay.hasAuthenticatedNumericIterationCarrierReentryForEdge(
                    self.analysis,
                    current,
                    reference,
                )) return true;
            }
        }
        self.trace_bridge_calls += 1;
        const bridge_start = structural_overlap.structuralPhaseNow();
        const result = if (parameters_match)
            try self.hasAuthenticatedContinuationBridgeForExpectedParameters(
                reference,
                context.parameter_arguments,
            )
        else if (isParameterizedNumericTransitionHeader(self.analysis.program, current)) blk: {
            const replay = self.replay_context orelse break :blk false;
            break :blk try replay.hasAuthenticatedIterationContextualProjectionForEdge(
                self.analysis,
                reference,
                owner_edge.arguments,
            );
        } else if (!std.mem.eql(ir.ValueId, owner_edge.arguments, incoming_edge.arguments)) blk: {
            // The owner region entered this parameterized block through an
            // edge-local tuple even though its outer region had no formals.
            // Require the live reentry to be an authenticated projection of
            // that exact owner tuple; equality, reachability, and type shape
            // alone are deliberately insufficient.
            const replay = self.replay_context orelse break :blk false;
            break :blk try replay.hasAuthenticatedParameterizedContinuationProjectionForEdge(
                self.analysis,
                reference,
                owner_edge.arguments,
            );
        } else false;
        self.trace_bridge_ms += structural_overlap.structuralPhaseMillis(bridge_start);
        if (result) return true;
        if (!parameters_match) return false;
        const expected = context.parameter_arguments orelse return false;
        const replay_context = self.replay_context orelse return false;
        return try replay_context.hasAuthenticatedParameterizedContinuationProjectionForEdge(
            self.analysis,
            reference,
            expected,
        );
    }

    // A cloned effectful prefix can enter an already-owned parameterized
    // header from outside that header's SCC. Preserve the prefix nodes and
    // reuse only the authenticated header handoff; SCC reachability is not
    // sufficient for this case.
    fn authenticatedParameterizedCloneHandoffReentry(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
        direct_projection: bool,
        incoming: ?ir.CfgEdgeRef,
    ) BuildError!bool {
        if (parameters_match or
            !direct_projection or
            current == start or
            context.start == start or
            context.start == current or
            context.stop == stop or
            context.loop_exit != loop_exit or
            context.continue_target != continue_target)
        {
            return false;
        }

        const reference = incoming orelse return false;
        if (reference.target != current) return false;
        const owner_reference = (try self.recoverUniqueOwnerEntryReference(
            current,
            context,
            reference,
        )) orelse return false;
        const owner_arguments = context.parameter_arguments orelse return false;
        const owner_edge = cfg_edge.value(self.analysis.program, owner_reference) orelse return false;
        if (!std.mem.eql(ir.ValueId, owner_arguments, owner_edge.arguments)) return false;
        const replay_context = self.replay_context orelse return false;
        return try replay_context.hasAuthenticatedParameterizedCloneHandoffForEdge(
            self.analysis,
            owner_reference,
            reference,
        );
    }

    // A parameterized numeric header can be revisited from a different
    // region start while retaining the same enclosing stop. This is only a
    // loop-carried state transfer: require a direct entry projection, a
    // distinct tuple, a genuine SCC edge, and the owner/tuple proof above.
    fn authenticatedSameStopDistinctNumericReentry(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
        direct_projection: bool,
        incoming: ?ir.CfgEdgeRef,
    ) BuildError!bool {
        if (parameters_match or
            !direct_projection or
            current == start or
            context.start == start or
            context.start == current or
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
        return try self.authenticatedSameSccParameterizedReentry(
            current,
            start,
            loop_exit,
            continue_target,
            context,
            parameters_match,
            reference,
        );
    }

    // A nonempty region can revisit an already-owned numeric transition from
    // the transition's own context without changing its enclosing boundary.
    // Keep this exception narrower than the general same-SCC predicate: the
    // current block must be a parameterized numeric header, the incoming edge
    // must be in the same SCC, and the existing owner/tuple proof must pass.
    fn authenticatedSameBoundaryNumericReentry(
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
        if (context.start != current or
            start == current or
            context.stop != stop or
            context.loop_exit != loop_exit or
            context.continue_target != continue_target or
            !parameters_match or
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
        return try self.authenticatedSameSccParameterizedReentry(
            current,
            start,
            loop_exit,
            continue_target,
            context,
            parameters_match,
            reference,
        );
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

    // A parameterized numeric header can already be owned by the current
    // region while an effectful prefix reaches it with a distinct SSA tuple.
    // Reuse this entry only when the prefix is acyclic relative to the header
    // and the existing replay proof authenticates the complete tuple.
    fn authenticatedSameContextDistinctNumericReentry(
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
        if (!parameters_match or
            current == start or
            context.start != start or
            context.stop != stop or
            context.loop_exit != loop_exit or
            context.continue_target != continue_target or
            !isParameterizedNumericTransitionHeader(self.analysis.program, current))
        {
            return false;
        }

        const reference = incoming orelse return false;
        if (reference.target != current or
            !try self.analysis.canReach(start, reference.source) or
            try self.analysis.canReach(current, reference.source))
        {
            return false;
        }

        if (current.index() >= self.analysis.program.blocks.len) return false;
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or
            block.function != self.analysis.function.id or
            block.parameters.len == 0 or
            !node_split.parametersAreCanonical(self.analysis.program.values, block))
        {
            return false;
        }

        const expected = context.parameter_arguments orelse return false;
        if (expected.len != block.parameters.len) return false;
        const edge = cfg_edge.value(self.analysis.program, reference) orelse return false;
        if (edge.target != current or
            edge.arguments.len != block.parameters.len or
            std.mem.eql(ir.ValueId, expected, edge.arguments))
        {
            return false;
        }

        const replay_context = self.replay_context orelse return false;
        return try replay_context.hasAuthenticatedParameterizedContinuationProjectionForEdge(
            self.analysis,
            reference,
            expected,
        );
    }

    // A numeric header can be reached again from an already-owned prefix in
    // the same visit context with the same canonical entry tuple.  This is a
    // projection of the existing loop, not a second execution of its header:
    // require the prefix to be reachable from the region start and require
    // the header to be unable to reach back into that prefix.
    fn authenticatedSameContextNumericReentry(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
        direct_projection: bool,
        incoming: ?ir.CfgEdgeRef,
    ) BuildError!bool {
        if (!direct_projection or
            !parameters_match or
            current == start or
            context.start != start or
            context.stop != stop or
            context.loop_exit != loop_exit or
            context.continue_target != continue_target or
            !isParameterizedNumericTransitionHeader(self.analysis.program, current))
        {
            return false;
        }

        const reference = incoming orelse return false;
        if (reference.target != current or
            !try self.analysis.canReach(start, reference.source) or
            try self.analysis.canReach(current, reference.source))
        {
            return false;
        }

        if (current.index() >= self.analysis.program.blocks.len) return false;
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or
            block.function != self.analysis.function.id or
            block.parameters.len == 0 or
            !node_split.parametersAreCanonical(self.analysis.program.values, block))
        {
            return false;
        }

        const expected = context.parameter_arguments orelse return false;
        const edge = cfg_edge.value(self.analysis.program, reference) orelse return false;
        return edge.target == current and
            edge.arguments.len == block.parameters.len and
            std.mem.eql(ir.ValueId, expected, edge.arguments);
    }

    // A numeric transition can be reached from a different region start
    // inside the same enclosing boundary while remaining in the header's SCC.
    // This is a loop-carried state projection, not ordinary same-context
    // reuse: require a direct continuation edge and the complete contextual
    // iteration proof before transferring ownership.
    fn authenticatedSameSccNumericReentry(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
        direct_projection: bool,
        incoming: ?ir.CfgEdgeRef,
    ) BuildError!bool {
        if (!direct_projection or
            !parameters_match or
            current == start or
            context.start == start or
            context.start == current or
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

        const expected = context.parameter_arguments orelse return false;
        const replay_context = self.replay_context orelse return false;
        if (!try replay_context.hasAuthenticatedIterationContextualProjectionForEdge(
            self.analysis,
            reference,
            expected,
        )) return false;

        return try self.authenticatedSameSccParameterizedReentry(
            current,
            start,
            loop_exit,
            continue_target,
            context,
            parameters_match,
            reference,
        );
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

    // A parameterized empty block that forwards its exact formal tuple is a
    // semantic identity. It may be reused across enclosing stop boundaries
    // without a clone bridge because it performs no work and cannot alter the
    // carried values. The successor still remains owned by the active region.
    fn identityParameterizedContinuationContextMatches(
        self: *const Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
        arguments: ?[]const ir.ValueId,
    ) bool {
        if (!parameters_match or current != start or context.start != start or
            stop == null or context.stop == stop or context.loop_exit != loop_exit or
            context.continue_target != continue_target)
        {
            return false;
        }
        const current_arguments = arguments orelse return false;
        if (current.index() >= self.analysis.program.blocks.len) return false;
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or block.parameters.len == 0 or
            current_arguments.len != block.parameters.len or
            !node_split.parametersAreCanonical(self.analysis.program.values, block))
        {
            return false;
        }
        return switch (block.terminator) {
            .jump => |edge| edge.target != current and
                edge.arguments.len == block.parameters.len and
                std.mem.eql(ir.ValueId, edge.arguments, block.parameters),
            .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => false,
        };
    }

    // A branch join can clear the live incoming edge while retaining the
    // parameter tuple. Recover that edge only for a single reachable
    // predecessor whose tuple matches both visit contexts and whose clone
    // bridge is independently authenticated. Ambiguous joins stay owned.
    fn hasAuthenticatedUniqueIncomingParameterizedBridge(
        self: *Builder,
        current: ir.BlockId,
        expected_arguments: ?[]const ir.ValueId,
        actual_arguments: ?[]const ir.ValueId,
    ) BuildError!bool {
        const expected = expected_arguments orelse return false;
        const actual = actual_arguments orelse return false;
        if (expected.len == 0 or actual.len == 0 or current.index() >= self.analysis.program.blocks.len) return false;
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or block.parameters.len == 0 or
            expected.len != block.parameters.len or actual.len != block.parameters.len or
            !node_split.parametersAreCanonical(self.analysis.program.values, block))
        {
            return false;
        }

        var selected: ?ir.CfgEdgeRef = null;
        for (0..self.analysis.predecessorCount(current)) |predecessor_index| {
            const predecessor = self.analysis.predecessorAt(current, predecessor_index) orelse return false;
            if (!self.analysis.isReachable(predecessor)) continue;
            const reference = directEdgeReference(self.analysis.program, .{ .block = predecessor }, current) orelse continue;
            const edge = cfg_edge.value(self.analysis.program, reference) orelse continue;
            if (edge.target != current or edge.arguments.len != block.parameters.len or
                !try self.parameterProjectionMatches(current, expected, edge.arguments) or
                !try self.parameterProjectionMatches(current, actual, edge.arguments))
            {
                continue;
            }
            self.trace_bridge_calls += 1;
            const bridge_start = structural_overlap.structuralPhaseNow();
            const authenticated = try self.hasAuthenticatedContinuationBridge(reference);
            self.trace_bridge_ms += structural_overlap.structuralPhaseMillis(bridge_start);
            if (!authenticated) continue;
            if (selected != null) return false;
            selected = reference;
        }
        return selected != null;
    }

    // A previously owned parameterized continuation may also be reached after
    // a nonempty prefix. Reuse that entry only when the prefix already owns an
    // exact incoming-edge projection and the edge is an authenticated clone
    // bridge or complete iteration-context projection. This composes the
    // prefix with the existing continuation without treating an effectful or
    // value-carrying block as transparent.
    fn authenticatedVisitedParameterizedContinuationProjection(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
        arguments: ?[]const ir.ValueId,
        incoming: ?ir.CfgEdgeRef,
        projection_available: bool,
        entry_authenticated: bool,
    ) BuildError!bool {
        if (!projection_available or context.start == start or
            context.loop_exit != loop_exit)
        {
            return false;
        }
        const authenticated_iteration_entry = entry_authenticated and
            isParameterizedNumericTransitionHeader(self.analysis.program, current);
        const distinct_numeric_tuple = try self.authenticatedDistinctNumericTuple(
            current,
            context,
            incoming,
            parameters_match,
        );
        if (!parameters_match and !distinct_numeric_tuple) return false;

        if (context.start == current) {
            if (context.stop == stop and context.continue_target == continue_target) return false;
        } else {
            const owner_arguments = context.parameter_arguments orelse return false;
            if (owner_arguments.len == 0 or !try self.analysis.canReach(context.start, current)) return false;
            if (!authenticated_iteration_entry and
                (try self.canReachWithoutContinuationBoundary(current, context.start, continue_target) or
                    try self.canReachWithoutContinuationBoundary(current, start, continue_target)))
            {
                return false;
            }
        }

        const current_arguments = arguments orelse return false;
        if (current.index() >= self.analysis.program.blocks.len) return false;
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or block.parameters.len == 0 or
            current_arguments.len != block.parameters.len or
            !node_split.parametersAreCanonical(self.analysis.program.values, block))
        {
            return false;
        }

        const reference = incoming orelse return false;
        if (reference.target != current) return false;
        self.trace_bridge_calls += 1;
        const bridge_start = structural_overlap.structuralPhaseNow();
        const result = if (authenticated_iteration_entry or distinct_numeric_tuple)
            true
        else
            try self.hasAuthenticatedContinuationBridgeForExpectedParameters(
                reference,
                context.parameter_arguments,
            );
        self.trace_bridge_ms += structural_overlap.structuralPhaseMillis(bridge_start);
        return result;
    }

    // A same-entry region may be revisited with a different stop only when
    // the entry contributes no values, effects, or control decision. A plain
    // empty jump is a transparent ownership boundary; its outgoing edge may
    // carry a canonical tuple into the successor. An empty branch or terminal
    // block still changes control flow and must remain a collision.
    fn transparentEmptyContinuationContextMatches(
        self: *const Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
    ) bool {
        if (!parameters_match or current != start or context.start != start or
            stop == null or context.stop == null or context.stop == stop)
        {
            return false;
        }
        return self.transparentEmptyJumpWithCanonicalSuccessor(current);
    }

    // An empty forwarder may be the final boundary of an earlier ownership
    // context. Reuse that boundary across a different loop context only when
    // the owner had no loop controls and the forwarder lands exactly on the
    // owner's stop. This keeps ordinary control-context mismatches as
    // collisions while admitting a proof-backed empty stop crossing.
    fn transparentEmptyOwnedStopContextMatches(
        self: *const Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
    ) bool {
        if (!parameters_match or current != start or context.start != start or
            stop == null or context.stop == null or context.stop == stop or
            context.stop == current or context.loop_exit != null or
            context.continue_target != null)
        {
            return false;
        }
        if (!self.transparentEmptyJumpWithCanonicalSuccessor(current)) return false;
        const block = self.analysis.program.blocks[current.index()];
        const outgoing = switch (block.terminator) {
            .jump => |edge| edge,
            else => return false,
        };
        return outgoing.target == context.stop.?;
    }

    // The same owner-stop proof applies after a nonempty prefix has already
    // been emitted.  The current block must be the previously owned empty
    // entry itself; its owner had no loop controls, and its canonical jump
    // must land exactly on the owner's stop.  The caller preserves the live
    // edge into this block as the projection boundary.
    fn transparentEmptyOwnedStopAfterPrefixContextMatches(
        self: *const Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
    ) bool {
        if (!parameters_match or current == start or context.start != current or
            stop == null or context.stop == null or context.stop == stop or
            context.stop == current or context.loop_exit != null or
            context.continue_target != null)
        {
            return false;
        }
        if (!self.transparentEmptyJumpWithCanonicalSuccessor(current)) return false;
        const block = self.analysis.program.blocks[current.index()];
        const outgoing = switch (block.terminator) {
            .jump => |edge| edge,
            else => return false,
        };
        return outgoing.target == context.stop.?;
    }

    // An empty forwarder can be the owned entry of a parameterized numeric
    // transition. Reusing that entry across a different incoming context is
    // safe only when the forwarder has no state of its own, both contexts
    // share the same stop, and the incoming path is in the same SCC as the
    // canonical numeric successor. The direct predecessor projection remains
    // the caller's additional proof.
    fn authenticatedEmptyNumericForwarderReentry(
        self: *const Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
        incoming: ?ir.CfgEdgeRef,
    ) BuildError!bool {
        if (!parameters_match or current == start or context.start != current or
            context.stop == null or context.stop != stop or
            context.loop_exit != null or context.continue_target != null)
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
        if (current.index() >= self.analysis.program.blocks.len) return false;
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or block.function != self.analysis.function.id or
            block.parameters.len != 0 or block.instructions.len != 0)
        {
            return false;
        }
        const incoming_edge = cfg_edge.value(self.analysis.program, reference) orelse return false;
        if (incoming_edge.target != current or incoming_edge.arguments.len != 0) return false;

        const outgoing = switch (block.terminator) {
            .jump => |edge| edge,
            .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
        };
        if (outgoing.target == current or
            outgoing.target.index() >= self.analysis.program.blocks.len)
        {
            return false;
        }
        const successor = self.analysis.program.blocks[outgoing.target.index()];
        if (successor.id != outgoing.target or successor.function != block.function or
            !isParameterizedNumericTransitionHeader(self.analysis.program, outgoing.target) or
            !node_split.parametersAreCanonical(self.analysis.program.values, successor) or
            outgoing.arguments.len != successor.parameters.len)
        {
            return false;
        }
        return try self.analysis.canReach(outgoing.target, current);
    }

    // A previously owned empty continuation may also be reached after the
    // current region has already emitted its predecessor. Reuse that boundary
    // only when the predecessor supplies an exact owned edge projection and
    // the empty block forwards a valid successor tuple.
    fn transparentEmptyVisitedContinuationContextMatches(
        self: *const Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
        projection: ?VisitedEntryProjection,
    ) bool {
        if (!parameters_match or context.start == start or context.stop == stop or
            context.stop == null or stop == null or context.loop_exit != loop_exit or
            context.continue_target != continue_target)
        {
            return false;
        }
        const entry_projection = projection orelse return false;
        switch (entry_projection.projection) {
            .edge => |edge| {
                if (edge.target != current or edge.arguments.len != 0) return false;
            },
            .transferred => return false,
        }
        return self.transparentEmptyJumpWithCanonicalSuccessor(current);
    }

    // A shared zero-result terminal has no context-bearing state.  Once its
    // incoming edge is owned by the current structured prefix, reusing the
    // already-visited terminal is equivalent to returning from a fresh clone.
    // Keep this narrower than general terminal projection: parameters,
    // instructions, returned values, packs, and errors all carry semantics
    // that may differ across incoming contexts.
    fn emptyReturnTerminalProjection(
        self: *const Builder,
        current: ir.BlockId,
        arguments: ?[]const ir.ValueId,
        previous: Node,
    ) ?TerminalProjection {
        if (arguments) |values| if (values.len != 0) return null;
        if (current.index() >= self.analysis.program.blocks.len) return null;
        const block = self.analysis.program.blocks[current.index()];
        if (block.id != current or block.parameters.len != 0 or block.instructions.len != 0) return null;
        switch (block.terminator) {
            .return_values => |values| if (values.len != 0) return null,
            .return_pack, .return_expanded, .throw_error, .jump, .branch, .unreachable_block => return null,
        }
        const transfer = finalContinueProjection(self.analysis.program, previous, current) orelse return null;
        return .{
            .terminal = current,
            .edge = switch (transfer) {
                .edge => |edge| edge,
                .transferred => null,
            },
        };
    }

    fn hasLiveIncomingArguments(
        self: *const Builder,
        target: ir.BlockId,
        arguments: []const ir.ValueId,
    ) bool {
        if (target.index() >= self.analysis.program.blocks.len) return false;
        const target_block = self.analysis.program.blocks[target.index()];
        if (target_block.id != target or arguments.len != target_block.parameters.len) return false;

        for (self.analysis.program.blocks) |source| {
            if (source.function != target_block.function or
                !self.analysis.isReachable(source.id)) continue;
            switch (source.terminator) {
                .jump => |edge| {
                    if (edge.target == target and std.mem.eql(ir.ValueId, edge.arguments, arguments)) return true;
                },
                .branch => |branch| {
                    if ((branch.then_edge.target == target and
                        std.mem.eql(ir.ValueId, branch.then_edge.arguments, arguments)) or
                        (branch.else_edge.target == target and
                            std.mem.eql(ir.ValueId, branch.else_edge.arguments, arguments))) return true;
                },
                .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
            }
        }
        return false;
    }

    const ParameterUseDetector = struct {
        parameters: []const ir.ValueId,
        found: bool = false,

        pub fn value(self: *ParameterUseDetector, value_id: ir.ValueId) void {
            if (self.found) return;
            for (self.parameters) |parameter| {
                if (parameter == value_id) {
                    self.found = true;
                    return;
                }
            }
        }

        pub fn pack(_: *ParameterUseDetector, _: ir.ValuePackId) void {}
        pub fn place(_: *ParameterUseDetector, _: ir.PlaceId) void {}
    };

    const ParameterDependencyDetector = struct {
        builder: *const Builder,
        parameters: []const ir.ValueId,
        additional_parameters: []const ir.ValueId = &.{},
        states: []u8,
        found: bool = false,

        pub fn value(self: *ParameterDependencyDetector, value_id: ir.ValueId) void {
            if (!self.found and self.builder.valueDependsOnParameterSets(
                value_id,
                self.parameters,
                self.additional_parameters,
                self.states,
            )) {
                self.found = true;
            }
        }

        pub fn pack(self: *ParameterDependencyDetector, _: ir.ValuePackId) void {
            // A pack can carry a tuple dependency without exposing a scalar
            // operand to the visitor.  Prefix replay does not need packs.
            self.found = true;
        }

        pub fn place(_: *ParameterDependencyDetector, _: ir.PlaceId) void {}
    };

    fn valueDependsOnParameterSets(
        self: *const Builder,
        value_id: ir.ValueId,
        parameters: []const ir.ValueId,
        additional_parameters: []const ir.ValueId,
        states: []u8,
    ) bool {
        for (parameters) |parameter| if (parameter == value_id) return true;
        for (additional_parameters) |parameter| if (parameter == value_id) return true;
        if (value_id.index() >= self.analysis.program.values.len or
            value_id.index() >= states.len)
        {
            return true;
        }
        if (states[value_id.index()] == 1) return true;
        if (states[value_id.index()] == 2) return false;
        if (states[value_id.index()] == 3) return true;
        states[value_id.index()] = 1;

        const value = self.analysis.program.values[value_id.index()];
        const depends = switch (value.origin) {
            .parameter, .capture => false,
            .block_parameter => true,
            .instruction_result => |origin| blk: {
                if (origin.instruction.index() >= self.analysis.program.instructions.len) break :blk true;
                const instruction = self.analysis.program.instructions[origin.instruction.index()];
                if (instruction.id != origin.instruction) break :blk true;
                var detector = ParameterDependencyDetector{
                    .builder = self,
                    .parameters = parameters,
                    .additional_parameters = additional_parameters,
                    .states = states,
                };
                runtime_uses.visitOperationUses(instruction.operation, &detector);
                break :blk detector.found;
            },
        };
        states[value_id.index()] = if (depends) 3 else 2;
        return depends;
    }

    // A same-entry continuation can be re-entered from a nested numeric
    // transition with a fresh tuple even when the owner region contains a
    // branch and therefore is not a linear suffix.  Authenticate this only
    // when the incoming edge is an existing replay bridge and a bounded path
    // from the owner reaches a numeric transition that can reach the incoming
    // source.  The path may select a branch, but every selected block must be
    // parameter-independent until the transition forwards the owner's tuple.
    fn authenticatedParameterizedNestedIterationReentry(
        self: *Builder,
        current: ir.BlockId,
        stop: ?ir.BlockId,
        owner_arguments: []const ir.ValueId,
        current_arguments: []const ir.ValueId,
        incoming: ir.CfgEdgeRef,
    ) BuildError!bool {
        if (incoming.target != current or incoming.source == current or
            current.index() >= self.analysis.program.blocks.len or
            !self.analysis.isReachable(current) or
            !self.analysis.isReachable(incoming.source) or
            isParameterizedNumericTransitionHeader(self.analysis.program, current))
        {
            return false;
        }
        const current_block = self.analysis.program.blocks[current.index()];
        if (current_block.id != current or current_block.function != self.analysis.function.id or
            current_block.parameters.len == 0 or
            current_block.parameters.len != owner_arguments.len or
            current_block.parameters.len != current_arguments.len or
            !node_split.parametersAreCanonical(self.analysis.program.values, current_block) or
            !self.hasLiveIncomingArguments(current, owner_arguments))
        {
            return false;
        }
        const incoming_edge = cfg_edge.value(self.analysis.program, incoming) orelse return false;
        if (incoming_edge.target != current or
            !std.mem.eql(ir.ValueId, incoming_edge.arguments, current_arguments) or
            !try self.hasAuthenticatedContinuationBridge(incoming))
        {
            return false;
        }
        for (current_block.parameters, owner_arguments, current_arguments) |formal, owner, actual| {
            if (!structural_overlap.continuationParameterAcceptsValueType(
                self.analysis.program,
                formal,
                owner,
            ) or !structural_overlap.continuationParameterAcceptsValueType(
                self.analysis.program,
                formal,
                actual,
            )) return false;
        }

        const seen = try self.allocator.alloc(bool, self.analysis.function.blocks.len);
        defer self.allocator.free(seen);
        @memset(seen, false);
        var pending: std.ArrayList(ir.BlockId) = .empty;
        defer pending.deinit(self.allocator);
        const current_index = self.analysis.blockIndex(current) orelse return false;
        seen[current_index] = true;
        try pending.append(self.allocator, current);

        var found_transition = false;
        var has_effect = false;
        var pending_index: usize = 0;
        while (pending_index < pending.items.len) : (pending_index += 1) {
            const block_id = pending.items[pending_index];
            const block_index = self.analysis.blockIndex(block_id) orelse return false;
            if (block_id.index() >= self.analysis.program.blocks.len) return false;
            const block = self.analysis.program.blocks[block_id.index()];
            if (block.id != block_id or block.function != self.analysis.function.id) return false;

            // A parameterized block other than the owner is an opaque state
            // transfer here. The selected proof path must expose the numeric
            // transition directly rather than guessing through another tuple.
            if (block_id != current and block.parameters.len != 0) continue;

            var detector = ParameterUseDetector{ .parameters = current_block.parameters };
            for (block.instructions) |instruction_id| {
                if (instruction_id.index() >= self.analysis.program.instructions.len) return false;
                const instruction = self.analysis.program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id or instruction.block != block_id) return false;
                runtime_uses.visitOperationUses(instruction.operation, &detector);
                if (proof_effect_closure.hasObservableEffects(instruction.effects)) has_effect = true;
            }
            if (detector.found) continue;

            var outgoing: [2]?ir.Edge = .{ null, null };
            switch (block.terminator) {
                .jump => |edge| outgoing[0] = edge,
                .branch => |branch| {
                    outgoing[0] = branch.then_edge;
                    outgoing[1] = branch.else_edge;
                },
                .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => continue,
            }
            for (outgoing) |maybe_edge| {
                const edge = maybe_edge orelse continue;
                if (edge.target == current or
                    (stop != null and edge.target == stop.?) or
                    edge.target.index() >= self.analysis.program.blocks.len)
                {
                    continue;
                }
                const target_block = self.analysis.program.blocks[edge.target.index()];
                if (target_block.id != edge.target or target_block.function != self.analysis.function.id) return false;
                if (isParameterizedNumericTransitionHeader(self.analysis.program, edge.target)) {
                    if (!std.mem.eql(ir.ValueId, edge.arguments, current_block.parameters) or
                        !try self.analysis.canReach(edge.target, incoming.source))
                    {
                        continue;
                    }
                    found_transition = true;
                    continue;
                }
                const target_index = self.analysis.blockIndex(edge.target) orelse return false;
                if (seen[target_index]) continue;
                seen[target_index] = true;
                try pending.append(self.allocator, edge.target);
            }
            _ = block_index;
        }
        return found_transition and has_effect;
    }

    fn authenticatedSameEntryNestedIterationReentry(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        context: VisitContext,
        parameters_match: bool,
        arguments: ?[]const ir.ValueId,
        incoming: ?ir.CfgEdgeRef,
    ) BuildError!bool {
        if (parameters_match or current != start or context.start != start or
            context.loop_exit != loop_exit or context.continue_target != continue_target or
            (context.stop == stop and context.continue_target == continue_target))
        {
            return false;
        }
        const owner_arguments = context.parameter_arguments orelse return false;
        const current_arguments = arguments orelse return false;
        const reference = incoming orelse return false;
        return try self.authenticatedParameterizedNestedIterationReentry(
            current,
            stop,
            owner_arguments,
            current_arguments,
            reference,
        );
    }

    // A shared effectful suffix can be rebound to a distinct incoming tuple
    // only when its instructions are parametric in the carried state.  The
    // proof is intentionally narrower than value projection: it authenticates
    // both live entries, rejects direct parameter reads, permits only a linear
    // visited path, and requires the original canonical tuple at the terminal
    // boundary.  This preserves the suffix's effects while making the carried
    // state transfer explicit.
    fn parameterizedEffectfulSuffixCanRebind(
        self: *Builder,
        current: ir.BlockId,
        stop: ?ir.BlockId,
        owner_arguments: []const ir.ValueId,
        current_arguments: []const ir.ValueId,
        incoming: ir.CfgEdgeRef,
    ) BuildError!bool {
        const stop_id = stop orelse return false;
        if (incoming.target != current or current.index() >= self.analysis.program.blocks.len) return false;
        const current_block = self.analysis.program.blocks[current.index()];
        if (current_block.id != current or current_block.function != self.analysis.function.id or
            current_block.parameters.len == 0 or
            current_block.parameters.len != owner_arguments.len or
            current_block.parameters.len != current_arguments.len or
            !node_split.parametersAreCanonical(self.analysis.program.values, current_block) or
            !self.analysis.isReachable(current) or
            !self.hasLiveIncomingArguments(current, owner_arguments))
        {
            return false;
        }

        const incoming_edge = cfg_edge.value(self.analysis.program, incoming) orelse return false;
        if (incoming_edge.target != current or
            !std.mem.eql(ir.ValueId, incoming_edge.arguments, current_arguments)) return false;

        for (current_block.parameters, owner_arguments, current_arguments) |formal, owner, actual| {
            if (!structural_overlap.continuationParameterAcceptsValueType(
                self.analysis.program,
                formal,
                owner,
            ) or !structural_overlap.continuationParameterAcceptsValueType(
                self.analysis.program,
                formal,
                actual,
            )) return false;
        }

        const seen = try self.allocator.alloc(bool, self.analysis.function.blocks.len);
        defer self.allocator.free(seen);
        @memset(seen, false);

        var cursor = current;
        var effectful = false;
        while (true) {
            const local_index = self.analysis.blockIndex(cursor) orelse return false;
            if (seen[local_index] or !self.visited[local_index]) return false;
            seen[local_index] = true;

            const block = self.analysis.program.blocks[cursor.index()];
            if (block.id != cursor or block.function != self.analysis.function.id or
                (block.parameters.len != 0 and
                    !node_split.parametersAreCanonical(self.analysis.program.values, block))) return false;

            for (block.instructions) |instruction_id| {
                if (instruction_id.index() >= self.analysis.program.instructions.len) return false;
                const instruction = self.analysis.program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id or instruction.block != cursor) return false;
                var detector = ParameterUseDetector{ .parameters = block.parameters };
                runtime_uses.visitOperationUses(instruction.operation, &detector);
                if (detector.found) return false;
                effectful = true;
            }

            switch (block.terminator) {
                .jump => |edge| {
                    if (edge.target.index() >= self.analysis.program.blocks.len or
                        edge.target == cursor) return false;
                    const target_block = self.analysis.program.blocks[edge.target.index()];
                    if (target_block.id != edge.target or target_block.function != self.analysis.function.id or
                        edge.arguments.len != target_block.parameters.len) return false;

                    if (edge.target == stop_id) {
                        if (!effectful or target_block.parameters.len != current_block.parameters.len or
                            !std.mem.eql(ir.ValueId, edge.arguments, current_block.parameters)) return false;
                        return true;
                    }

                    // A nonterminal parameterized hop is accepted only when
                    // it forwards the current canonical tuple positionally.
                    if (target_block.parameters.len != 0 and
                        (!node_split.parametersAreCanonical(self.analysis.program.values, target_block) or
                            !std.mem.eql(ir.ValueId, edge.arguments, block.parameters) and
                                !std.mem.eql(ir.ValueId, edge.arguments, current_block.parameters))) return false;
                    if (target_block.parameters.len == 0 and edge.arguments.len != 0) return false;
                    cursor = edge.target;
                },
                .return_values, .return_pack, .return_expanded, .throw_error, .branch, .unreachable_block => return false,
            }
        }
    }

    const AuthenticatedEffectfulPrefixReplay = struct {
        nodes: []Node,
        source: ir.BlockId,
        next: ir.BlockId,
        arguments: []const ir.ValueId,
    };

    // A node-split clone may execute an equivalent zero-parameter entry and
    // then rejoin an already-owned linear suffix under a different structural
    // stop.  Permit that handoff only when the clone entry itself is
    // authenticated and its mapped outgoing edge is the owner's exact edge.
    // This keeps a changed stop from becoming a reachability-only sharing
    // rule.
    fn authenticatedZeroParameterCloneEntryMatchesOwner(
        self: *Builder,
        start: ir.BlockId,
        current: ir.BlockId,
        owner_start: ir.BlockId,
        incoming: ir.CfgEdgeRef,
    ) BuildError!bool {
        if (start == owner_start or incoming.source != start or incoming.target != current) return false;
        const replay = self.replay_context orelse return false;
        var authenticated_clone_entry = false;
        if (try self.uniqueIncomingReference(start)) |entry| {
            if (try replay.authenticatedContinuationCloneForEdge(self.analysis, entry)) |projection| {
                authenticated_clone_entry = projection.root == owner_start;
            }
        }
        if (!authenticated_clone_entry) {
            // A later node-split can leave the canonical root with multiple
            // incoming edges while its owner clone still has one authenticated
            // entry.  Validate that reverse projection as the same bounded
            // clone witness instead of treating the shared root as ambiguous.
            if (try self.uniqueIncomingReference(owner_start)) |entry| {
                if (try replay.authenticatedContinuationCloneForEdge(self.analysis, entry)) |projection| {
                    authenticated_clone_entry = projection.root == start;
                }
            }
        }
        if (!authenticated_clone_entry) {
            // A shared clone target can have several authenticated arms in one
            // split group.  The incoming arm may itself be a nested clone, so
            // a unique root check is too strict; require the complete shared
            // target and nested-edge proof instead.
            authenticated_clone_entry = try replay.hasAuthenticatedSharedCloneTargetArmForEdge(
                self.analysis,
                owner_start,
                incoming,
            );
        }
        if (!authenticated_clone_entry) return false;
        if (owner_start.index() >= self.analysis.program.blocks.len or
            start.index() >= self.analysis.program.blocks.len)
        {
            return false;
        }

        const owner_block = self.analysis.program.blocks[owner_start.index()];
        const clone_block = self.analysis.program.blocks[start.index()];
        if (!node_split.entryShapeMatches(self.analysis.program, owner_block, clone_block)) return false;

        const owner_reference = directEdgeReference(
            self.analysis.program,
            .{ .block = owner_start },
            current,
        ) orelse return false;
        const owner_edge = cfg_edge.value(self.analysis.program, owner_reference) orelse return false;
        const incoming_edge = cfg_edge.value(self.analysis.program, incoming) orelse return false;
        return owner_edge.target == current and
            incoming_edge.target == current and
            std.mem.eql(ir.ValueId, owner_edge.arguments, incoming_edge.arguments);
    }

    const StopBoundaryUseDetector = struct {
        builder: *const Builder,
        boundary: ir.BlockId,
        boundary_parameters: []const ir.ValueId,
        use_block: ir.BlockId,
        use_position: usize,
        use_instruction: ?ir.InstructionId,
        valid: bool = true,

        pub fn value(self: *StopBoundaryUseDetector, value_id: ir.ValueId) void {
            if (self.valid and !self.builder.valueAvailableThroughBoundary(
                self.boundary,
                self.boundary_parameters,
                self.use_block,
                self.use_position,
                value_id,
            )) self.valid = false;
        }

        pub fn pack(self: *StopBoundaryUseDetector, pack_id: ir.ValuePackId) void {
            if (self.valid and !self.builder.packAvailableThroughBoundary(
                self.boundary,
                self.use_block,
                self.use_position,
                pack_id,
            )) self.valid = false;
        }

        pub fn place(self: *StopBoundaryUseDetector, place_id: ir.PlaceId) void {
            if (self.valid and !self.builder.placeAvailableThroughBoundary(
                self.boundary,
                self.use_block,
                self.use_position,
                self.use_instruction,
                place_id,
            )) self.valid = false;
        }
    };

    fn instructionPrecedesUse(
        self: *const Builder,
        definition: ir.InstructionId,
        use_block: ir.BlockId,
        use_position: usize,
        use_instruction: ?ir.InstructionId,
        allow_same_instruction: bool,
    ) bool {
        if (allow_same_instruction and use_instruction != null and
            use_instruction.? == definition) return true;
        if (use_block.index() >= self.analysis.program.blocks.len) return false;
        const block = self.analysis.program.blocks[use_block.index()];
        if (block.id != use_block) return false;
        for (block.instructions, 0..) |instruction_id, position| {
            if (instruction_id != definition) continue;
            return position < use_position;
        }
        return false;
    }

    fn valueAvailableThroughBoundary(
        self: *const Builder,
        boundary: ir.BlockId,
        boundary_parameters: []const ir.ValueId,
        use_block: ir.BlockId,
        use_position: usize,
        value_id: ir.ValueId,
    ) bool {
        if (value_id.index() >= self.analysis.program.values.len) return false;
        const value = self.analysis.program.values[value_id.index()];
        if (value.id != value_id or value.function != self.analysis.function.id) return false;
        for (boundary_parameters) |parameter| if (parameter == value_id) return true;

        return switch (value.origin) {
            .parameter, .capture => true,
            .block_parameter => |origin| blk: {
                if (origin.block.index() >= self.analysis.program.blocks.len) break :blk false;
                const origin_block = self.analysis.program.blocks[origin.block.index()];
                if (origin_block.id != origin.block or origin_block.function != self.analysis.function.id or
                    origin.index >= origin_block.parameters.len or
                    origin_block.parameters[origin.index] != value_id) break :blk false;
                if (origin.block == boundary) break :blk false;
                if (origin.block == use_block) break :blk true;
                break :blk self.analysis.dominates(boundary, origin.block) and
                    self.analysis.dominates(origin.block, use_block);
            },
            .instruction_result => |origin| blk: {
                if (origin.instruction.index() >= self.analysis.program.instructions.len) break :blk false;
                const definition = self.analysis.program.instructions[origin.instruction.index()];
                if (definition.id != origin.instruction or definition.block.index() >= self.analysis.program.blocks.len) break :blk false;
                if (definition.block == use_block) break :blk self.instructionPrecedesUse(
                    origin.instruction,
                    use_block,
                    use_position,
                    null,
                    false,
                );
                break :blk self.analysis.dominates(boundary, definition.block) and
                    self.analysis.dominates(definition.block, use_block);
            },
        };
    }

    fn packAvailableThroughBoundary(
        self: *const Builder,
        boundary: ir.BlockId,
        use_block: ir.BlockId,
        use_position: usize,
        pack_id: ir.ValuePackId,
    ) bool {
        if (pack_id.index() >= self.analysis.program.value_packs.len) return false;
        const pack = self.analysis.program.value_packs[pack_id.index()];
        if (pack.id != pack_id or pack.function != self.analysis.function.id) return false;
        return switch (pack.origin) {
            .varargs => |function_id| function_id == self.analysis.function.id,
            .instruction_result => |instruction_id| blk: {
                if (instruction_id.index() >= self.analysis.program.instructions.len) break :blk false;
                const definition = self.analysis.program.instructions[instruction_id.index()];
                if (definition.id != instruction_id or definition.block.index() >= self.analysis.program.blocks.len) break :blk false;
                if (definition.block == use_block) break :blk self.instructionPrecedesUse(
                    instruction_id,
                    use_block,
                    use_position,
                    null,
                    false,
                );
                break :blk self.analysis.dominates(boundary, definition.block) and
                    self.analysis.dominates(definition.block, use_block);
            },
        };
    }

    fn placeAvailableThroughBoundary(
        self: *const Builder,
        boundary: ir.BlockId,
        use_block: ir.BlockId,
        use_position: usize,
        use_instruction: ?ir.InstructionId,
        place_id: ir.PlaceId,
    ) bool {
        if (place_id.index() >= self.analysis.program.places.len) return false;
        const place = self.analysis.program.places[place_id.index()];
        if (place.id != place_id or place.function != self.analysis.function.id) return false;
        return switch (place.origin) {
            .local, .capture => true,
            .instruction => |instruction_id| blk: {
                if (instruction_id.index() >= self.analysis.program.instructions.len) break :blk false;
                const definition = self.analysis.program.instructions[instruction_id.index()];
                if (definition.id != instruction_id or definition.block.index() >= self.analysis.program.blocks.len) break :blk false;
                if (definition.block == use_block) break :blk self.instructionPrecedesUse(
                    instruction_id,
                    use_block,
                    use_position,
                    use_instruction,
                    true,
                );
                break :blk self.analysis.dominates(boundary, definition.block) and
                    self.analysis.dominates(definition.block, use_block);
            },
        };
    }

    fn parameterizedStopBoundaryHasContextClosure(
        self: *Builder,
        boundary: ir.BlockId,
        boundary_parameters: []const ir.ValueId,
    ) BuildError!bool {
        const boundary_index = self.analysis.blockIndex(boundary) orelse return false;
        if (self.stop_boundary_closure) |cache| if (cache[boundary_index]) |result| return result;

        const seen = try self.allocator.alloc(bool, self.analysis.function.blocks.len);
        defer self.allocator.free(seen);
        @memset(seen, false);
        const queue = try self.allocator.alloc(ir.BlockId, self.analysis.function.blocks.len);
        defer self.allocator.free(queue);
        seen[boundary_index] = true;
        queue[0] = boundary;
        var queue_length: usize = 1;
        var queue_index: usize = 0;
        var valid = true;

        while (queue_index < queue_length and valid) : (queue_index += 1) {
            const block_id = queue[queue_index];
            const local_index = self.analysis.blockIndex(block_id) orelse {
                valid = false;
                break;
            };
            if (block_id.index() >= self.analysis.program.blocks.len or
                !self.analysis.isReachable(block_id))
            {
                valid = false;
                break;
            }
            const block = self.analysis.program.blocks[block_id.index()];
            if (block.id != block_id or block.function != self.analysis.function.id) {
                valid = false;
                break;
            }

            for (block.instructions) |instruction_id| {
                if (instruction_id.index() >= self.analysis.program.instructions.len) {
                    valid = false;
                    break;
                }
                const instruction = self.analysis.program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id or instruction.block != block_id) {
                    valid = false;
                    break;
                }
                var detector = StopBoundaryUseDetector{
                    .builder = self,
                    .boundary = boundary,
                    .boundary_parameters = boundary_parameters,
                    .use_block = block_id,
                    .use_position = undefined,
                    .use_instruction = instruction_id,
                };
                detector.use_position = for (block.instructions, 0..) |candidate, position| {
                    if (candidate == instruction_id) break position;
                } else {
                    valid = false;
                    break;
                };
                runtime_uses.visitOperationUses(instruction.operation, &detector);
                if (!detector.valid) {
                    valid = false;
                    break;
                }
            }
            if (!valid) break;

            var terminator_detector = StopBoundaryUseDetector{
                .builder = self,
                .boundary = boundary,
                .boundary_parameters = boundary_parameters,
                .use_block = block_id,
                .use_position = block.instructions.len,
                .use_instruction = null,
            };
            runtime_uses.visitTerminatorUses(block.terminator, &terminator_detector);
            if (!terminator_detector.valid) {
                valid = false;
                break;
            }

            var successors: [2]ir.BlockId = undefined;
            var successor_count: usize = 0;
            switch (block.terminator) {
                .jump => |edge| {
                    successors[0] = edge.target;
                    successor_count = 1;
                },
                .branch => |branch| {
                    successors[0] = branch.then_edge.target;
                    successors[1] = branch.else_edge.target;
                    successor_count = 2;
                },
                .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
            }
            for (successors[0..successor_count]) |successor| {
                const successor_index = self.analysis.blockIndex(successor) orelse {
                    valid = false;
                    break;
                };
                if (successor_index >= seen.len or seen[successor_index]) continue;
                if (queue_length >= queue.len) {
                    valid = false;
                    break;
                }
                seen[successor_index] = true;
                queue[queue_length] = successor;
                queue_length += 1;
            }
            _ = local_index;
        }

        if (self.stop_boundary_closure) |cache| cache[boundary_index] = valid;
        return valid;
    }

    // A parameter-independent prefix may be replayed before handing control
    // back to the ordinary structurer at its first branch or numeric
    // transition. This is narrower than terminal replay: the entry tuple must
    // be a distinct, authenticated live tuple, every replayed block must
    // already be owned and linear, and the prefix must contain an observable
    // effect. Canonical parameterized hops are allowed to rename the carried
    // tuple, but their own formals are included in dependency checks and their
    // outgoing edge must forward the complete positional tuple. The decision
    // block itself is never projected here; the caller resumes normal
    // ownership checks there.
    fn authenticatedEffectfulPrefixReplay(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        owner_context: VisitContext,
        current_arguments: []const ir.ValueId,
        incoming: ir.CfgEdgeRef,
    ) BuildError!?AuthenticatedEffectfulPrefixReplay {
        return self.authenticatedEffectfulPrefixReplayImpl(
            current,
            start,
            stop,
            null,
            null,
            owner_context,
            current_arguments,
            incoming,
            false,
        );
    }

    // A same-entry parameterized prefix may be replayed when it hands off
    // unchanged canonical state to a semantic iteration header.  This keeps
    // the effectful prefix in the current arm without projecting the header
    // or its control decisions across an equal or different boundary.
    fn authenticatedSameEntryParameterizedPrefixReplay(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        owner_context: VisitContext,
        current_arguments: []const ir.ValueId,
        incoming: ir.CfgEdgeRef,
    ) BuildError!?AuthenticatedEffectfulPrefixReplay {
        if (current != start or owner_context.start != start or
            owner_context.loop_exit != loop_exit or
            owner_context.continue_target != continue_target)
        {
            return null;
        }
        return self.authenticatedEffectfulPrefixReplayImpl(
            current,
            start,
            stop,
            loop_exit,
            continue_target,
            owner_context,
            current_arguments,
            incoming,
            true,
        );
    }

    fn authenticatedEffectfulPrefixReplayImpl(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        owner_context: VisitContext,
        current_arguments: []const ir.ValueId,
        incoming: ir.CfgEdgeRef,
        allow_same_entry_handoff: bool,
    ) BuildError!?AuthenticatedEffectfulPrefixReplay {
        const same_entry = current == start and owner_context.start == start;
        if (incoming.target != current or
            (!allow_same_entry_handoff and (current == start or owner_context.start == start)) or
            (allow_same_entry_handoff and !same_entry) or
            current.index() >= self.analysis.program.blocks.len)
        {
            return null;
        }

        const current_block = self.analysis.program.blocks[current.index()];
        const owner_arguments = owner_context.parameter_arguments orelse return null;
        if (current_block.id != current or current_block.function != self.analysis.function.id or
            current_block.parameters.len == 0 or
            current_block.parameters.len != owner_arguments.len or
            current_block.parameters.len != current_arguments.len or
            !node_split.parametersAreCanonical(self.analysis.program.values, current_block) or
            std.mem.eql(ir.ValueId, owner_arguments, current_arguments) or
            !self.analysis.isReachable(current) or
            !self.hasLiveIncomingArguments(current, owner_arguments))
        {
            return null;
        }

        const incoming_edge = cfg_edge.value(self.analysis.program, incoming) orelse return null;
        if (incoming_edge.target != current or
            !std.mem.eql(ir.ValueId, incoming_edge.arguments, current_arguments)) return null;

        for (current_block.parameters, owner_arguments, current_arguments) |formal, owner, actual| {
            if (!structural_overlap.continuationParameterAcceptsValueType(
                self.analysis.program,
                formal,
                owner,
            ) or !structural_overlap.continuationParameterAcceptsValueType(
                self.analysis.program,
                formal,
                actual,
            )) return null;
        }

        const seen = try self.allocator.alloc(bool, self.analysis.function.blocks.len);
        defer self.allocator.free(seen);
        @memset(seen, false);
        const dependency_states = try self.allocator.alloc(u8, self.analysis.program.values.len);
        defer self.allocator.free(dependency_states);
        @memset(dependency_states, 0);

        var replay: std.ArrayList(Node) = .empty;
        defer replay.deinit(self.allocator);
        var cursor = current;
        var forwarded_parameters = current_block.parameters;
        var effectful = false;
        while (true) {
            const local_index = self.analysis.blockIndex(cursor) orelse return null;
            if (seen[local_index] or !self.visited[local_index]) return null;
            seen[local_index] = true;

            const block = self.analysis.program.blocks[cursor.index()];
            if (block.id != cursor or block.function != self.analysis.function.id or
                (block.parameters.len != 0 and
                    (!node_split.parametersAreCanonical(self.analysis.program.values, block) or
                        block.parameters.len != forwarded_parameters.len))) return null;

            for (block.instructions) |instruction_id| {
                if (instruction_id.index() >= self.analysis.program.instructions.len) return null;
                const instruction = self.analysis.program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id or instruction.block != cursor) return null;
                var detector = ParameterDependencyDetector{
                    .builder = self,
                    .parameters = forwarded_parameters,
                    .additional_parameters = block.parameters,
                    .states = dependency_states,
                };
                runtime_uses.visitOperationUses(instruction.operation, &detector);
                if (detector.found) return null;
                if (proof_effect_closure.hasObservableEffects(instruction.effects)) effectful = true;
            }

            try replay.append(self.allocator, .{ .block = cursor });

            switch (block.terminator) {
                .jump => |edge| {
                    if (edge.target.index() >= self.analysis.program.blocks.len or edge.target == cursor) return null;
                    const target = self.analysis.program.blocks[edge.target.index()];
                    if (target.id != edge.target or target.function != self.analysis.function.id or
                        edge.arguments.len != target.parameters.len or
                        (stop != null and edge.target == stop.?)) return null;

                    // A numeric transition is the next semantic decision,
                    // never an intermediate replay node. Same-entry replay
                    // may hand off to it, but only after the active tuple has
                    // been forwarded positionally through every prior hop.
                    if (structural_overlap.isIterationTransitionHeader(self.analysis.program, edge.target)) {
                        if (!allow_same_entry_handoff or
                            (loop_exit != null and edge.target == loop_exit.?) or
                            (continue_target != null and edge.target == continue_target.?) or
                            !node_split.parametersAreCanonical(self.analysis.program.values, target) or
                            target.parameters.len != forwarded_parameters.len or
                            !std.mem.eql(ir.ValueId, edge.arguments, forwarded_parameters)) return null;
                        for (target.parameters, forwarded_parameters) |formal, argument| {
                            if (!structural_overlap.continuationParameterAcceptsValueType(
                                self.analysis.program,
                                formal,
                                argument,
                            )) return null;
                        }
                        if (!effectful) return null;
                        return .{
                            .nodes = try replay.toOwnedSlice(self.allocator),
                            .source = cursor,
                            .next = edge.target,
                            .arguments = edge.arguments,
                        };
                    }

                    if (target.terminator == .branch) {
                        if (!effectful or target.parameters.len != 0) return null;
                        const branch = switch (target.terminator) {
                            .branch => |value| value,
                            else => unreachable,
                        };
                        var detector = ParameterDependencyDetector{
                            .builder = self,
                            .parameters = forwarded_parameters,
                            .additional_parameters = target.parameters,
                            .states = dependency_states,
                        };
                        detector.value(branch.condition);
                        if (detector.found) return null;
                        return .{
                            .nodes = try replay.toOwnedSlice(self.allocator),
                            .source = cursor,
                            .next = edge.target,
                            .arguments = edge.arguments,
                        };
                    }
                    if (target.parameters.len != 0) {
                        if (!node_split.parametersAreCanonical(self.analysis.program.values, target) or
                            target.parameters.len != forwarded_parameters.len or
                            !std.mem.eql(ir.ValueId, edge.arguments, forwarded_parameters)) return null;
                        for (target.parameters, forwarded_parameters) |formal, argument| {
                            if (!structural_overlap.continuationParameterAcceptsValueType(
                                self.analysis.program,
                                formal,
                                argument,
                            )) return null;
                        }
                        forwarded_parameters = target.parameters;
                    }
                    cursor = edge.target;
                },
                .return_values, .return_pack, .return_expanded, .throw_error, .branch, .unreachable_block => return null,
            }
        }
    }

    // A zero-parameter effectful suffix can be replayed when two paths enter
    // the same linear body inside one SCC and retain the same enclosing
    // control boundary.  The suffix is emitted in the current arm; its first
    // branch or authenticated numeric header remains the next structural
    // decision.  This does not infer values: every edge is checked against
    // the successor formals, and a numeric handoff reuses the existing
    // iteration projection proof for the already-owned header.
    fn authenticatedEffectfulZeroParameterPrefixReplay(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        owner_context: VisitContext,
        current_arguments: []const ir.ValueId,
        incoming: ir.CfgEdgeRef,
    ) BuildError!?AuthenticatedEffectfulPrefixReplay {
        const trace_index = self.trace_zero_parameter_replay_calls;
        self.trace_zero_parameter_replay_calls += 1;
        const trace = trace_index < 128;
        if (trace) {
            structural_overlap.traceStructural("structural_phase zero_parameter_replay_enter call={} current={} start={} stop={?} loop_exit={?} continue_target={?} owner_start={} owner_stop={?} owner_loop_exit={?} owner_continue_target={?} current_arguments={} owner_arguments={} incoming_source={} incoming_target={}\n", .{
                trace_index,
                current.index(),
                start.index(),
                if (stop) |value| value.index() else null,
                if (loop_exit) |value| value.index() else null,
                if (continue_target) |value| value.index() else null,
                owner_context.start.index(),
                if (owner_context.stop) |value| value.index() else null,
                if (owner_context.loop_exit) |value| value.index() else null,
                if (owner_context.continue_target) |value| value.index() else null,
                current_arguments.len,
                if (owner_context.parameter_arguments) |values| values.len else 0,
                incoming.source.index(),
                incoming.target.index(),
            });
        }
        const authenticated_clone_entry = if (owner_context.stop != stop and
            owner_context.loop_exit == loop_exit and
            owner_context.continue_target == continue_target)
            try self.authenticatedZeroParameterCloneEntryMatchesOwner(
                start,
                current,
                owner_context.start,
                incoming,
            )
        else
            false;
        if (current == start or owner_context.start == start or
            owner_context.start == current or
            (owner_context.stop != stop and !authenticated_clone_entry) or
            owner_context.loop_exit != loop_exit or
            owner_context.continue_target != continue_target or
            current_arguments.len != 0 or
            (owner_context.parameter_arguments != null and
                owner_context.parameter_arguments.?.len != 0) or
            incoming.source != start or incoming.target != current)
        {
            if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=entry_shape authenticated_clone_entry={}\n", .{ trace_index, authenticated_clone_entry });
            return null;
        }
        const reaches_start_current = try self.analysis.canReach(start, current);
        const reaches_current_start = try self.analysis.canReach(current, start);
        const reaches_owner_current = try self.analysis.canReach(owner_context.start, current);
        const reaches_current_owner = try self.analysis.canReach(current, owner_context.start);
        if (!reaches_start_current or !reaches_current_start or
            !reaches_owner_current or !reaches_current_owner)
        {
            if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=scc reaches_start_current={} reaches_current_start={} reaches_owner_current={} reaches_current_owner={}\n", .{
                trace_index,
                reaches_start_current,
                reaches_current_start,
                reaches_owner_current,
                reaches_current_owner,
            });
            return null;
        }

        const incoming_edge = cfg_edge.value(self.analysis.program, incoming) orelse return null;
        if (incoming_edge.target != current or incoming_edge.arguments.len != 0) {
            if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=incoming_edge target={} arguments={}\n", .{
                trace_index,
                incoming_edge.target.index(),
                incoming_edge.arguments.len,
            });
            return null;
        }

        const seen = try self.allocator.alloc(bool, self.analysis.function.blocks.len);
        defer self.allocator.free(seen);
        @memset(seen, false);

        var replay: std.ArrayList(Node) = .empty;
        defer replay.deinit(self.allocator);
        var cursor = current;
        var effectful = false;
        while (true) {
            const local_index = self.analysis.blockIndex(cursor) orelse return null;
            if (seen[local_index] or !self.visited[local_index]) {
                if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=ownership block={} seen={} visited={}\n", .{
                    trace_index,
                    cursor.index(),
                    seen[local_index],
                    self.visited[local_index],
                });
                return null;
            }
            seen[local_index] = true;

            const block = self.analysis.program.blocks[cursor.index()];
            if (block.id != cursor or block.function != self.analysis.function.id or
                block.parameters.len != 0 or !self.analysis.isReachable(cursor))
            {
                if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=block_shape block={} parameters={} reachable={}\n", .{
                    trace_index,
                    cursor.index(),
                    block.parameters.len,
                    self.analysis.isReachable(cursor),
                });
                return null;
            }
            for (block.instructions) |instruction_id| {
                if (instruction_id.index() >= self.analysis.program.instructions.len) return null;
                const instruction = self.analysis.program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id or instruction.block != cursor) return null;
                if (proof_effect_closure.hasObservableEffects(instruction.effects)) effectful = true;
            }
            if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_step call={} block={} instructions={} effectful={} terminator={s}\n", .{
                trace_index,
                cursor.index(),
                block.instructions.len,
                effectful,
                @tagName(block.terminator),
            });
            try replay.append(self.allocator, .{ .block = cursor });

            const edge = switch (block.terminator) {
                .jump => |value| value,
                .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return null,
            };
            if (edge.target == cursor or edge.target.index() >= self.analysis.program.blocks.len or
                (loop_exit != null and edge.target == loop_exit.?) or
                (continue_target != null and edge.target == continue_target.?))
            {
                if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=boundary edge_target={} effectful={}\n", .{
                    trace_index,
                    edge.target.index(),
                    effectful,
                });
                return null;
            }

            const target_index = self.analysis.blockIndex(edge.target) orelse return null;
            const target = self.analysis.program.blocks[edge.target.index()];
            if (target.id != edge.target or target.function != self.analysis.function.id or
                edge.arguments.len != target.parameters.len)
            {
                if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=target_shape target={} arguments={} parameters={}\n", .{
                    trace_index,
                    edge.target.index(),
                    edge.arguments.len,
                    target.parameters.len,
                });
                return null;
            }

            // The caller's stop is an enclosing boundary, not a structural
            // decision owned by this replay. Preserve the real edge tuple and
            // hand control back to the caller when the effectful suffix lands
            // there. A parameterized boundary still needs canonical formals;
            // no value is synthesized by this projection. Its continuation
            // must also be closed over the boundary: otherwise a second
            // incoming context can reach uses of values that were defined
            // only on the replayed path.
            const canonical_parameters = target.parameters.len == 0 or
                node_split.parametersAreCanonical(self.analysis.program.values, target);
            if (stop != null and edge.target == stop.?) {
                const continuation_closed = if (target.parameters.len == 0)
                    true
                else
                    try self.parameterizedStopBoundaryHasContextClosure(edge.target, target.parameters);
                if (!effectful or !canonical_parameters or !continuation_closed) {
                    if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=stop_boundary effectful={} parameters={} canonical={} continuation_closed={}\n", .{
                        trace_index,
                        effectful,
                        target.parameters.len,
                        canonical_parameters,
                        continuation_closed,
                    });
                    return null;
                }
                if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_accept call={} kind=stop source={} next={} nodes={} arguments={}\n", .{
                    trace_index,
                    cursor.index(),
                    edge.target.index(),
                    replay.items.len,
                    edge.arguments.len,
                });
                return .{
                    .nodes = try replay.toOwnedSlice(self.allocator),
                    .source = cursor,
                    .next = edge.target,
                    .arguments = edge.arguments,
                };
            }

            if (target.parameters.len == 0) {
                switch (target.terminator) {
                    .branch => {
                        if (!effectful) {
                            if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=branch_without_effect block={}\n", .{ trace_index, edge.target.index() });
                            return null;
                        }
                        if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_accept call={} kind=branch source={} next={} nodes={}\n", .{
                            trace_index,
                            cursor.index(),
                            edge.target.index(),
                            replay.items.len,
                        });
                        return .{
                            .nodes = try replay.toOwnedSlice(self.allocator),
                            .source = cursor,
                            .next = edge.target,
                            .arguments = edge.arguments,
                        };
                    },
                    .jump => {
                        cursor = edge.target;
                        continue;
                    },
                    .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {
                        if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=terminal target={}\n", .{ trace_index, edge.target.index() });
                        return null;
                    },
                }
            }

            if (!isParameterizedNumericTransitionHeader(self.analysis.program, edge.target) or
                !node_split.parametersAreCanonical(self.analysis.program.values, target) or
                !effectful)
            {
                if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=numeric_handoff_shape target={} numeric={} canonical={} effectful={}\n", .{
                    trace_index,
                    edge.target.index(),
                    isParameterizedNumericTransitionHeader(self.analysis.program, edge.target),
                    node_split.parametersAreCanonical(self.analysis.program.values, target),
                    effectful,
                });
                return null;
            }
            const target_context = self.visited_contexts[target_index] orelse {
                if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=numeric_context_missing target={}\n", .{ trace_index, edge.target.index() });
                return null;
            };
            const expected = target_context.parameter_arguments orelse {
                if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=numeric_arguments_missing target={}\n", .{ trace_index, edge.target.index() });
                return null;
            };
            const context_matches = target_context.stop == stop and
                target_context.loop_exit == loop_exit and
                target_context.continue_target == continue_target;
            const edge_arity_matches = edge.arguments.len == target.parameters.len;
            const bridge_authenticated = try self.hasAuthenticatedContinuationBridgeForExpectedParameters(
                .{ .source = cursor, .kind = .jump, .target = edge.target },
                expected,
            );
            if ((!context_matches and !authenticated_clone_entry) or
                target_context.loop_exit != loop_exit or
                target_context.continue_target != continue_target or
                !edge_arity_matches or
                !bridge_authenticated)
            {
                if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=numeric_context_mismatch target={} context_matches={} authenticated_clone_entry={} target_stop={?} target_loop_exit={?} target_continue_target={?} edge_arguments_match={} bridge_authenticated={}\n", .{
                    trace_index,
                    edge.target.index(),
                    context_matches,
                    authenticated_clone_entry,
                    if (target_context.stop) |value| value.index() else null,
                    if (target_context.loop_exit) |value| value.index() else null,
                    if (target_context.continue_target) |value| value.index() else null,
                    edge_arity_matches,
                    bridge_authenticated,
                });
                return null;
            }
            if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_bridge call={} source={} target={} expected={} actual={} authenticated={}\n", .{
                trace_index,
                cursor.index(),
                edge.target.index(),
                expected.len,
                edge.arguments.len,
                bridge_authenticated,
            });
            if (expected.len != target.parameters.len or !bridge_authenticated) {
                if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_reject call={} reason=numeric_bridge target={} expected={} parameters={} authenticated={}\n", .{
                    trace_index,
                    edge.target.index(),
                    expected.len,
                    target.parameters.len,
                    bridge_authenticated,
                });
                return null;
            }
            if (trace) structural_overlap.traceStructural("structural_phase zero_parameter_replay_accept call={} kind=numeric source={} next={} nodes={}\n", .{
                trace_index,
                cursor.index(),
                edge.target.index(),
                replay.items.len,
            });
            return .{
                .nodes = try replay.toOwnedSlice(self.allocator),
                .source = cursor,
                .next = edge.target,
                .arguments = edge.arguments,
            };
        }
    }

    // An authenticated bridge can re-enter an already-owned linear suffix
    // from a different structured boundary. Emit the suffix in the current
    // arm, preserving its effects, instead of cloning the IR again. A
    // parameterized suffix additionally needs an exact remapped entry tuple,
    // canonical formals, matching edge arities, and a proof-backed path to
    // the current stop. Branches, loops, unvisited blocks, and terminal
    // shortcuts remain rejected because they carry control or ownership state
    // that this projection does not represent.
    const AuthenticatedTerminalReplay = struct {
        nodes: []Node,
        terminal: ?TerminalProjection,
    };

    fn valueProducedByReplayNodes(
        self: *const Builder,
        value_id: ir.ValueId,
        nodes: []const Node,
    ) bool {
        if (value_id.index() >= self.analysis.program.values.len) return false;
        const value = self.analysis.program.values[value_id.index()];
        const origin = switch (value.origin) {
            .instruction_result => |result| result,
            else => return false,
        };
        if (value.id != value_id or value.function != self.analysis.function.id or
            origin.instruction.index() >= self.analysis.program.instructions.len)
        {
            return false;
        }
        const instruction = self.analysis.program.instructions[origin.instruction.index()];
        if (instruction.id != origin.instruction or origin.index >= instruction.results.len or
            instruction.results[origin.index] != value_id)
        {
            return false;
        }
        for (nodes) |node| {
            if (node.blockId() == instruction.block) return true;
        }
        return false;
    }

    const AuthenticatedTerminalContinuationReplay = struct {
        nodes: []Node,
    };

    // A visited zero-parameter terminal may be reached after an already
    // emitted prefix through a different authenticated structural boundary.
    // Replay only a linear, visited terminal closure.  Every returned value
    // must be the exact result of an instruction in that closure; no value is
    // recovered from the owner path or synthesized at the boundary.
    fn authenticatedEffectfulTerminalContinuationReplay(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        continue_target: ?ir.BlockId,
        arguments: ?[]const ir.ValueId,
        incoming: ?ir.CfgEdgeRef,
        previous: Node,
    ) BuildError!?AuthenticatedTerminalContinuationReplay {
        const reference = incoming orelse return null;
        if (current == start or reference.target != current or
            (stop != null and current == stop.?) or
            (loop_exit != null and current == loop_exit.?) or
            (continue_target != null and current == continue_target.?))
        {
            return null;
        }

        const local_index = self.analysis.blockIndex(current) orelse return null;
        if (!self.visited[local_index] or !self.analysis.isReachable(current)) return null;
        const owner_context = self.visited_contexts[local_index] orelse return null;
        if (owner_context.start == start or owner_context.stop == stop or
            owner_context.loop_exit != loop_exit or
            owner_context.continue_target != continue_target or
            (owner_context.parameter_arguments != null and
                owner_context.parameter_arguments.?.len != 0) or
            (arguments != null and arguments.?.len != 0))
        {
            return null;
        }

        const current_block = self.analysis.program.blocks[current.index()];
        if (current_block.id != current or current_block.function != self.analysis.function.id or
            current_block.parameters.len != 0)
        {
            return null;
        }
        const incoming_edge = cfg_edge.value(self.analysis.program, reference) orelse return null;
        if (incoming_edge.target != current or incoming_edge.arguments.len != 0 or
            !try self.hasAuthenticatedContinuationBridge(reference))
        {
            return null;
        }
        const transfer = continuationProjectionForVisitedEntry(
            self.analysis.program,
            previous,
            current,
            reference,
            arguments,
        ) orelse return null;
        switch (transfer) {
            .edge => |edge| {
                if (edge.target != current or edge.arguments.len != 0) return null;
            },
            .transferred => return null,
        }

        const seen = try self.allocator.alloc(bool, self.analysis.function.blocks.len);
        defer self.allocator.free(seen);
        @memset(seen, false);

        var replay: std.ArrayList(Node) = .empty;
        defer replay.deinit(self.allocator);
        var cursor = current;
        var effectful = false;
        while (true) {
            const cursor_index = self.analysis.blockIndex(cursor) orelse return null;
            if (seen[cursor_index] or !self.visited[cursor_index] or
                !self.analysis.isReachable(cursor))
            {
                return null;
            }
            seen[cursor_index] = true;

            const block = self.analysis.program.blocks[cursor.index()];
            if (block.id != cursor or block.function != self.analysis.function.id or
                block.parameters.len != 0)
            {
                return null;
            }
            for (block.instructions) |instruction_id| {
                if (instruction_id.index() >= self.analysis.program.instructions.len) return null;
                const instruction = self.analysis.program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id or instruction.block != cursor) return null;
                if (proof_effect_closure.hasObservableEffects(instruction.effects)) effectful = true;
            }
            try replay.append(self.allocator, .{ .block = cursor });

            switch (block.terminator) {
                .return_values => |values| {
                    if (!effectful or values.len == 0) return null;
                    for (values) |value_id| {
                        if (!self.valueProducedByReplayNodes(value_id, replay.items)) return null;
                    }
                    return .{ .nodes = try replay.toOwnedSlice(self.allocator) };
                },
                .jump => |edge| {
                    if (edge.target == cursor or edge.target.index() >= self.analysis.program.blocks.len or
                        edge.target == stop or edge.target == loop_exit or edge.target == continue_target)
                    {
                        return null;
                    }
                    const target = self.analysis.program.blocks[edge.target.index()];
                    if (target.id != edge.target or target.function != self.analysis.function.id or
                        target.parameters.len != 0 or edge.arguments.len != 0)
                    {
                        return null;
                    }
                    cursor = edge.target;
                },
                .return_pack, .return_expanded, .throw_error, .branch, .unreachable_block => return null,
            }
        }
    }

    fn authenticatedEffectfulTerminalReplay(
        self: *Builder,
        current: ir.BlockId,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        arguments: ?[]const ir.ValueId,
        incoming: ?ir.CfgEdgeRef,
    ) BuildError!?AuthenticatedTerminalReplay {
        if (current != start) return null;
        const reference = incoming orelse return null;
        if (reference.target != current) return null;

        const current_index = self.analysis.blockIndex(current) orelse return null;
        const owner_context = self.visited_contexts[current_index] orelse return null;
        if (owner_context.start != current or owner_context.stop == stop) return null;
        const current_block = self.analysis.program.blocks[current.index()];
        if (current_block.id != current or current_block.function != self.analysis.function.id) return null;
        const parameterized = current_block.parameters.len != 0;
        if (parameterized) {
            const owner_arguments = owner_context.parameter_arguments orelse return null;
            const current_arguments = arguments orelse return null;
            const edge = cfg_edge.value(self.analysis.program, reference) orelse return null;
            const tuple_match = owner_arguments.len != 0 and
                current_arguments.len == current_block.parameters.len and
                node_split.parametersAreCanonical(self.analysis.program.values, current_block) and
                try self.parameterProjectionMatches(current, owner_arguments, current_arguments);
            const edge_tuple_match = std.mem.eql(ir.ValueId, edge.arguments, current_arguments);
            const parametric_rebind = if (!tuple_match and edge_tuple_match)
                try self.parameterizedEffectfulSuffixCanRebind(
                    current,
                    stop,
                    owner_arguments,
                    current_arguments,
                    reference,
                )
            else
                false;
            const bridge_authenticated = if (tuple_match and edge_tuple_match)
                (try self.hasAuthenticatedContinuationBridgeForExpectedParameters(reference, owner_arguments)) or
                    self.hasAuthenticatedEffectfulEntryBridge(reference, owner_arguments)
            else
                parametric_rebind;
            structural_overlap.traceStructural("structural_phase parameterized_effectful_replay_candidate current={} owner_stop={?} incoming_stop={?} parameters={} owner_arguments={} current_arguments={} tuple_match={} edge_tuple_match={} parametric_rebind={} bridge_authenticated={}\n", .{
                current.index(),
                if (owner_context.stop) |value| value.index() else null,
                if (stop) |value| value.index() else null,
                current_block.parameters.len,
                owner_arguments.len,
                current_arguments.len,
                tuple_match,
                edge_tuple_match,
                parametric_rebind,
                bridge_authenticated,
            });
            if ((!tuple_match and !parametric_rebind) or !edge_tuple_match or !bridge_authenticated) {
                return null;
            }
        } else {
            if (arguments) |values| if (values.len != 0) return null;
            if (owner_context.parameter_arguments) |values| if (values.len != 0) return null;
            if (!try self.hasAuthenticatedContinuationBridge(reference)) return null;
        }

        const seen = try self.allocator.alloc(bool, self.analysis.function.blocks.len);
        defer self.allocator.free(seen);
        @memset(seen, false);

        var replay: std.ArrayList(Node) = .empty;
        defer replay.deinit(self.allocator);
        var cursor = current;
        var effectful = false;
        while (true) {
            const local_index = self.analysis.blockIndex(cursor) orelse return null;
            if (seen[local_index] or !self.visited[local_index]) return null;
            seen[local_index] = true;

            const block = self.analysis.program.blocks[cursor.index()];
            if (block.id != cursor or block.function != self.analysis.function.id) return null;
            if (block.parameters.len != 0 and
                (!parameterized or !node_split.parametersAreCanonical(self.analysis.program.values, block))) return null;
            if (block.instructions.len != 0) effectful = true;
            try replay.append(self.allocator, .{ .block = cursor });

            switch (block.terminator) {
                .jump => |edge| {
                    if (edge.target.index() >= self.analysis.program.blocks.len) return null;
                    const target_block = self.analysis.program.blocks[edge.target.index()];
                    if (target_block.id != edge.target or target_block.function != self.analysis.function.id) return null;
                    if (edge.target == cursor) return null;
                    if (stop != null and edge.target == stop.?) {
                        if (edge.arguments.len != target_block.parameters.len or
                            (!parameterized and (edge.arguments.len != 0 or target_block.parameters.len != 0)) or
                            !effectful)
                        {
                            return null;
                        }
                        if (parameterized and target_block.parameters.len != 0) {
                            const canonical_stop_parameters =
                                node_split.parametersAreCanonical(self.analysis.program.values, target_block);
                            const continuation_closed = canonical_stop_parameters and
                                try self.parameterizedStopBoundaryHasContextClosure(
                                    edge.target,
                                    target_block.parameters,
                                );
                            if (!continuation_closed) {
                                structural_overlap.traceStructural("structural_phase parameterized_effectful_replay_reject start={} stop={} reason=stop_boundary canonical={} continuation_closed={} target_parameters={}\n", .{
                                    start.index(),
                                    stop.?.index(),
                                    canonical_stop_parameters,
                                    continuation_closed,
                                    target_block.parameters.len,
                                });
                                return null;
                            }
                        }
                        if (parameterized) {
                            structural_overlap.traceStructural("structural_phase parameterized_effectful_replay start={} stop={} nodes={} incoming_source={} incoming_target={}\n", .{
                                start.index(),
                                stop.?.index(),
                                replay.items.len,
                                reference.source.index(),
                                reference.target.index(),
                            });
                        }
                        return .{
                            .nodes = try replay.toOwnedSlice(self.allocator),
                            .terminal = null,
                        };
                    }
                    if (edge.arguments.len != target_block.parameters.len or
                        (!parameterized and edge.arguments.len != 0)) return null;
                    if (!self.visited[self.analysis.blockIndex(edge.target) orelse return null]) {
                        if (parameterized) return null;
                        switch (target_block.terminator) {
                            .return_values => |values| {
                                if (values.len != 0 or target_block.parameters.len != 0 or target_block.instructions.len != 0 or !effectful) return null;
                                return .{
                                    .nodes = try replay.toOwnedSlice(self.allocator),
                                    .terminal = .{ .terminal = edge.target, .edge = edge },
                                };
                            },
                            else => return null,
                        }
                    }
                    cursor = edge.target;
                },
                .return_values => |values| {
                    if (parameterized or values.len != 0 or !effectful) return null;
                    return .{
                        .nodes = try replay.toOwnedSlice(self.allocator),
                        .terminal = null,
                    };
                },
                .return_pack, .return_expanded, .throw_error, .branch, .unreachable_block => return null,
            }
        }
    }

    fn buildRegion(
        self: *Builder,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        allowed: ?[]const bool,
        loop_exit: ?ir.BlockId,
    ) BuildError!*Region {
        if (stop) |block| {
            const escape_target: EscapeTarget = .{ .block = block, .parent = null };
            return self.buildRegionImplWithEntryArguments(start, stop, allowed, loop_exit, &escape_target, null, false, null, null);
        }
        return self.buildRegionImplWithEntryArguments(start, stop, allowed, loop_exit, null, null, false, null, null);
    }

    fn buildLoopRegion(
        self: *Builder,
        start: ir.BlockId,
        stop: ir.BlockId,
        allowed: []const bool,
        loop_exit: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        entry_arguments: ?[]const ir.ValueId,
        entry_reference: ?ir.CfgEdgeRef,
    ) BuildError!*Region {
        const continue_escape: EscapeTarget = .{ .block = stop, .parent = escape_targets };
        const continue_target: EscapeTarget = .{ .block = stop, .parent = continue_targets };
        return self.buildRegionImplWithEntryArgumentsAndEdge(
            start,
            stop,
            allowed,
            loop_exit,
            &continue_escape,
            &continue_target,
            false,
            stop,
            entry_arguments,
            entry_reference,
        );
    }

    fn buildRegionIncludingStart(
        self: *Builder,
        start: ir.BlockId,
        stop: ir.BlockId,
        allowed: []const bool,
        loop_exit: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        continue_target: ir.BlockId,
        entry_arguments: ?[]const ir.ValueId,
        entry_reference: ?ir.CfgEdgeRef,
    ) BuildError!*Region {
        const forwarded_continue: EscapeTarget = .{ .block = continue_target, .parent = continue_targets };
        return self.buildRegionImplWithEntryArgumentsAndEdge(
            start,
            stop,
            allowed,
            loop_exit,
            escape_targets,
            &forwarded_continue,
            true,
            continue_target,
            entry_arguments,
            entry_reference,
        );
    }

    fn buildRegionImpl(
        self: *Builder,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        allowed: ?[]const bool,
        loop_exit: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        include_start_at_stop: bool,
        continue_target: ?ir.BlockId,
    ) BuildError!*Region {
        return self.buildRegionImplWithEntryArguments(
            start,
            stop,
            allowed,
            loop_exit,
            escape_targets,
            continue_targets,
            include_start_at_stop,
            continue_target,
            null,
        );
    }

    fn buildRegionImplWithEntryArguments(
        self: *Builder,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        allowed: ?[]const bool,
        loop_exit: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        include_start_at_stop: bool,
        continue_target: ?ir.BlockId,
        entry_arguments: ?[]const ir.ValueId,
    ) BuildError!*Region {
        return self.buildRegionImplWithEntryArgumentsAndEdge(
            start,
            stop,
            allowed,
            loop_exit,
            escape_targets,
            continue_targets,
            include_start_at_stop,
            continue_target,
            entry_arguments,
            null,
        );
    }

    fn buildRegionImplWithEntryArgumentsAndEdge(
        self: *Builder,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        allowed: ?[]const bool,
        loop_exit: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        include_start_at_stop: bool,
        continue_target: ?ir.BlockId,
        entry_arguments: ?[]const ir.ValueId,
        entry_reference: ?ir.CfgEdgeRef,
    ) BuildError!*Region {
        const checkpoint = self.beginMutation();
        errdefer self.rollbackMutation(checkpoint);
        const region = try self.buildRegionImplWithEntryArgumentsAndEdgeCore(
            start,
            stop,
            allowed,
            loop_exit,
            escape_targets,
            continue_targets,
            include_start_at_stop,
            continue_target,
            entry_arguments,
            entry_reference,
        );
        self.finishMutation(checkpoint);
        return region;
    }

    fn buildRegionImplWithEntryArgumentsAndEdgeCore(
        self: *Builder,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        allowed: ?[]const bool,
        loop_exit: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        include_start_at_stop: bool,
        continue_target: ?ir.BlockId,
        entry_arguments: ?[]const ir.ValueId,
        entry_reference: ?ir.CfgEdgeRef,
    ) BuildError!*Region {
        const region = try self.allocator.create(Region);
        errdefer self.allocator.destroy(region);
        var nodes: std.ArrayList(Node) = .empty;
        errdefer destroyNodeList(self.allocator, &nodes);

        var current = start;
        var current_arguments = entry_arguments;
        var current_incoming = entry_reference;
        var include_current = include_start_at_stop;
        const region_depth = self.trace_region_depth;
        self.trace_region_depth += 1;
        defer self.trace_region_depth = region_depth;
        errdefer {
            const local_index = self.analysis.blockIndex(current);
            structural_overlap.traceStructural("structural_phase region_failed function={} depth={} start={} stop={?} loop_exit={?} continue_target={?} current={} current_visited={} current_allowed={} nodes={} error=unsupported_or_oom\n", .{
                self.analysis.function.id.index(),
                region_depth,
                start.index(),
                if (stop) |value| value.index() else null,
                if (loop_exit) |value| value.index() else null,
                if (continue_target) |value| value.index() else null,
                current.index(),
                if (local_index) |index| self.visited[index] else false,
                if (local_index) |index| if (allowed) |membership| membership[index] else true else false,
                nodes.items.len,
            });
        }
        while (include_current or stop == null or current != stop.?) {
            // Including an unvisited start at its stop is the normal loop
            // header path.  A previously covered clone member must still run
            // the authenticated boundary projection, otherwise the include
            // flag bypasses every ownership proof and reports a false
            // collision before the region can reuse its clone group.
            const suppress_loop_detection = if (include_current) blk: {
                const initial_index = self.analysis.blockIndex(current) orelse return error.UnsupportedShape;
                break :blk !self.visited[initial_index];
            } else false;
            include_current = false;
            if (!suppress_loop_detection and
                (stop == null or current != stop.?) and
                isEscapeTarget(escape_targets, current))
            {
                const edge: ?ir.Edge = if (nodes.items.len == 0) null else projected: {
                    const projection = finalContinueProjection(
                        self.analysis.program,
                        nodes.items[nodes.items.len - 1],
                        current,
                    ) orelse return error.UnsupportedShape;
                    break :projected switch (projection) {
                        .edge => |value| value,
                        .transferred => null,
                    };
                };
                const projected = try finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                projected.escape_projection = .{ .target = current, .edge = edge };
                return projected;
            }
            if (!suppress_loop_detection and
                (stop == null or current != stop.?) and
                isEscapeTarget(continue_targets, current))
            {
                const edge: ?ir.Edge = if (nodes.items.len == 0) null else projected: {
                    const projection = finalContinueProjection(
                        self.analysis.program,
                        nodes.items[nodes.items.len - 1],
                        current,
                    ) orelse return error.UnsupportedShape;
                    break :projected switch (projection) {
                        .edge => |value| value,
                        .transferred => null,
                    };
                };
                const projected = try finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                projected.continue_projection = .{ .target = current, .edge = edge };
                return projected;
            }
            if (!suppress_loop_detection and
                (stop == null or current != stop.?) and
                loop_exit != null and current == loop_exit.?)
            {
                const edge: ?ir.Edge = if (nodes.items.len == 0) null else projected: {
                    const projection = finalContinueProjection(
                        self.analysis.program,
                        nodes.items[nodes.items.len - 1],
                        current,
                    ) orelse return error.UnsupportedShape;
                    break :projected switch (projection) {
                        .edge => |value| value,
                        .transferred => null,
                    };
                };
                const projected = try finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                projected.escape_projection = .{ .target = current, .edge = edge };
                return projected;
            }
            const local_index = self.analysis.blockIndex(current) orelse return error.UnsupportedShape;
            const region_step = self.trace_region_step_calls;
            self.trace_region_step_calls += 1;
            if (region_step < 256) {
                structural_overlap.traceStructural("structural_phase region_step function={} step={} depth={} start={} stop={?} current={} nodes={} suppress_loops={} visited={}\n", .{
                    self.analysis.function.id.index(),
                    region_step,
                    region_depth,
                    start.index(),
                    stop,
                    current.index(),
                    nodes.items.len,
                    suppress_loop_detection,
                    self.visited[local_index],
                });
            }
            // A covered clone group intentionally leaves non-entry members
            // without visit contexts.  Re-check the authenticated boundary
            // even when such a member is already marked visited; the proof
            // validates the complete clone group, root tuple, and incoming
            // edge before projecting it.  The old unvisited-only guard made
            // an effectful loop header in a previously covered group look
            // like an unexplained ownership collision.
            if (!suppress_loop_detection) {
                const boundary_projection = try self.authenticatedUnvisitedBoundaryProjection(
                    current,
                    start,
                    stop,
                    loop_exit,
                    continue_target,
                    escape_targets,
                    continue_targets,
                    current_arguments,
                    current_incoming,
                );
                if (current == start and self.visited[local_index] and
                    self.trace_visited_boundary_calls < 128)
                {
                    self.trace_visited_boundary_calls += 1;
                    structural_overlap.traceStructural("structural_phase clone_boundary_candidate current={} start={} visited={} context_present={} projection_present={} incoming_source={?} incoming_target={?} arguments={}\n", .{
                        current.index(),
                        start.index(),
                        self.visited[local_index],
                        self.visited_contexts[local_index] != null,
                        boundary_projection != null,
                        if (current_incoming) |reference| reference.source.index() else null,
                        if (current_incoming) |reference| reference.target.index() else null,
                        if (current_arguments) |values| values.len else 0,
                    });
                }
                if (boundary_projection) |projection| {
                    const projected = try finishRegion(
                        self.allocator,
                        region,
                        &nodes,
                        stop,
                        loop_exit,
                        continue_target,
                    );
                    if (projection.continue_projection) {
                        projected.continue_projection = .{
                            .target = projection.target,
                            .edge = projection.edge,
                        };
                    } else {
                        projected.escape_projection = .{
                            .target = projection.target,
                            .edge = projection.edge,
                        };
                    }
                    return projected;
                }
            }
            if (allowed) |membership| {
                // An already-owned continuation may be outside the current
                // region membership. Let the visited-entry projection below
                // authenticate that transfer; unvisited outside nodes still
                // require the terminal-path or collision handling here.
                if (!membership[local_index] and !self.visited[local_index]) {
                    if (try self.authenticatedTransparentOutsideProjection(
                        current,
                        stop,
                        loop_exit,
                        escape_targets,
                        continue_targets,
                        current_arguments,
                        current_incoming,
                        membership,
                    )) |edge| {
                        const source = current;
                        try self.markVisited(local_index);
                        try self.setVisitedContext(local_index, .{
                            .start = start,
                            .stop = stop,
                            .loop_exit = loop_exit,
                            .continue_target = continue_target,
                            .parameter_arguments = current_arguments,
                            .entry_reference = current_incoming,
                        });
                        try nodes.append(self.allocator, .{ .block = source });
                        current = edge.target;
                        current_arguments = edge.arguments;
                        current_incoming = .{
                            .source = source,
                            .kind = .jump,
                            .target = edge.target,
                        };
                        continue;
                    }
                    switch (try self.appendTerminalOutsideRegion(
                        &nodes,
                        current,
                        stop,
                        loop_exit,
                        escape_targets,
                        continue_targets,
                        current_arguments,
                        current_incoming,
                        membership,
                    )) {
                        .none => {},
                        .appended => return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target),
                        .projected => |projection| {
                            const projected = try finishRegion(
                                self.allocator,
                                region,
                                &nodes,
                                stop,
                                loop_exit,
                                continue_target,
                            );
                            projected.terminal_projection = projection;
                            return projected;
                        },
                    }
                    if (stop) |stop_id| {
                        const boundary_block = self.analysis.program.blocks[current.index()];
                        const boundary_edge = switch (boundary_block.terminator) {
                            .jump => |edge| edge,
                            else => return error.UnsupportedShape,
                        };
                        if (!self.visited[local_index] and
                            self.analysis.predecessorCount(current) == 1 and
                            self.analysis.dominates(start, current) and
                            boundary_edge.target == stop_id)
                        {
                            try self.markVisited(local_index);
                            try nodes.append(self.allocator, .{ .block = current });
                            return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                        }
                    }
                    try self.noteCollisionNode(
                        current,
                        if (nodes.items.len == 0) null else nodes.items[nodes.items.len - 1],
                        current_incoming,
                        .outside_region,
                        .{
                            .start = start,
                            .stop = stop,
                            .loop_exit = loop_exit,
                            .continue_target = continue_target,
                            .parameter_arguments = current_arguments,
                        },
                    );
                    return error.UnsupportedShape;
                }
            }
            if (!self.analysis.isReachable(current)) return error.UnsupportedShape;
            if (self.visited[local_index]) {
                if (nodes.items.len != 0) {
                    const previous = nodes.items[nodes.items.len - 1];
                    if (try self.authenticatedEffectfulTerminalContinuationReplay(
                        current,
                        start,
                        stop,
                        loop_exit,
                        continue_target,
                        current_arguments,
                        current_incoming,
                        previous,
                    )) |replay| {
                        defer self.allocator.free(replay.nodes);
                        try nodes.appendSlice(self.allocator, replay.nodes);
                        structural_overlap.traceStructural("structural_phase terminal_continuation_replay current={} start={} stop={?} nodes={} incoming_source={?} incoming_target={?}\n", .{
                            current.index(),
                            start.index(),
                            if (stop) |value| value.index() else null,
                            replay.nodes.len,
                            if (current_incoming) |reference| reference.source.index() else null,
                            if (current_incoming) |reference| reference.target.index() else null,
                        });
                        return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                    }
                }
                if (!suppress_loop_detection) {
                    if (continue_target != null and current == continue_target.?) {
                        const edge: ?ir.Edge = if (nodes.items.len == 0) null else edge: {
                            const projection = finalContinueProjection(
                                self.analysis.program,
                                nodes.items[nodes.items.len - 1],
                                current,
                            ) orelse return error.UnsupportedShape;
                            break :edge switch (projection) {
                                .edge => |value| value,
                                .transferred => null,
                            };
                        };
                        const projected = try finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                        projected.continue_projection = .{ .target = current, .edge = edge };
                        return projected;
                    }
                    if (continue_target) |continue_id| {
                        if (nodes.items.len != 0) {
                            if (try self.forwardingContinueProjectionAlloc(
                                nodes.items[nodes.items.len - 1],
                                current,
                                continue_id,
                                stop,
                                allowed,
                            )) |value| {
                                var forwarding = value;
                                errdefer forwarding.deinit(self.allocator);
                                const projected = try finishRegion(
                                    self.allocator,
                                    region,
                                    &nodes,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                );
                                projected.continue_projection = .{
                                    .target = continue_id,
                                    .edge = null,
                                    .forwarding = forwarding,
                                };
                                return projected;
                            }
                        }
                    }
                    if (stop) |stop_id| {
                        if (self.ownedTransparentStopEdge(current, stop_id, allowed)) |edge| {
                            if (edge.arguments.len == 0) {
                                return finishRegion(self.allocator, region, &nodes, current, loop_exit, continue_target);
                            }
                            const forwarded = try finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                            forwarded.stop_forwarding = current;
                            return forwarded;
                        }
                    }
                    if (!suppress_loop_detection and nodes.items.len != 0) {
                        const previous = nodes.items[nodes.items.len - 1];
                        if (try self.isOutsideEntryToOwnedLoopHeader(current, previous.blockId())) {
                            if (finalContinueProjection(self.analysis.program, previous, current)) |transfer| {
                                const projected = try finishRegion(
                                    self.allocator,
                                    region,
                                    &nodes,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                );
                                projected.escape_projection = .{
                                    .target = current,
                                    .edge = switch (transfer) {
                                        .edge => |edge| edge,
                                        .transferred => null,
                                    },
                                };
                                return projected;
                            }
                        }
                    }
                    if (nodes.items.len != 0) {
                        if (self.visited_contexts[local_index]) |context| {
                            const previous = nodes.items[nodes.items.len - 1];
                            const iteration_header = structural_overlap.isIterationTransitionHeader(
                                self.analysis.program,
                                current,
                            );
                            var projected_incoming = current_incoming;
                            var projected_arguments = current_arguments;
                            var authenticated_iteration_entry = false;
                            // A structured join can clear a parameterized
                            // entry to either null or an empty tuple. An
                            // empty tuple is not a valid entry for an
                            // iteration header, so let the authenticated
                            // predecessor recovery inspect the exact edge.
                            const missing_iteration_arguments = projected_arguments == null or
                                projected_arguments.?.len == 0;
                            if (iteration_header and projected_incoming == null and missing_iteration_arguments) {
                                if (try self.authenticatedUniqueIncomingIterationEntry(
                                    previous,
                                    current,
                                    context.parameter_arguments,
                                )) |entry| {
                                    projected_incoming = entry.reference;
                                    projected_arguments = entry.arguments;
                                    authenticated_iteration_entry = true;
                                }
                            } else if (iteration_header and
                                projected_incoming != null and
                                !missing_iteration_arguments and
                                context.start == current and
                                start != current and
                                context.stop == stop and
                                context.loop_exit == loop_exit and
                                context.continue_target == continue_target)
                            {
                                // Internal numeric reentry can retain its
                                // complete tuple while the structured
                                // predecessor still hides the iteration
                                // witness. Recover only the exact live edge;
                                // a different owned predecessor remains a
                                // collision.
                                if (try self.authenticatedUniqueIncomingIterationEntry(
                                    previous,
                                    current,
                                    context.parameter_arguments,
                                )) |entry| {
                                    const reference = projected_incoming.?;
                                    const same_reference = entry.reference.source == reference.source and
                                        entry.reference.kind == reference.kind and
                                        entry.reference.target == reference.target;
                                    const same_arguments = std.mem.eql(
                                        ir.ValueId,
                                        projected_arguments.?,
                                        entry.arguments,
                                    );
                                    if (same_reference and same_arguments) authenticated_iteration_entry = true;
                                }
                            }
                            const entry_projection = try self.visitedEntryContinuationProjection(
                                previous,
                                current,
                                projected_incoming,
                                projected_arguments,
                            );
                            if (entry_projection) |projection| {
                                if (projected_incoming == null) {
                                    projected_incoming = projection.recovered_context_reference;
                                }
                                if (projection.recovered_context_arguments) {
                                    projected_arguments = projection.arguments;
                                    try self.setVisitContextParameterArguments(local_index, projection.arguments);
                                }
                            }
                            const direct_projection = if (entry_projection) |projection|
                                projection.projection
                            else
                                null;
                            const projection_arguments = if (entry_projection) |projection|
                                projection.arguments
                            else
                                projected_arguments;
                            const context_arguments = if (context.parameter_arguments == null and
                                entry_projection != null and
                                entry_projection.?.recovered_context_arguments)
                                projection_arguments
                            else
                                context.parameter_arguments;
                            const comparison_context = VisitContext{
                                .start = context.start,
                                .stop = context.stop,
                                .loop_exit = context.loop_exit,
                                .continue_target = context.continue_target,
                                .parameter_arguments = context_arguments,
                                .entry_reference = context.entry_reference,
                            };
                            const parameters_match = try self.parameterProjectionMatches(
                                current,
                                context_arguments,
                                projection_arguments,
                            );
                            const same_control_context = context.stop == stop and
                                context.loop_exit == loop_exit and
                                context.continue_target == continue_target and
                                parameters_match;
                            const transparent_empty_visited_context =
                                self.transparentEmptyVisitedContinuationContextMatches(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    comparison_context,
                                    parameters_match,
                                    entry_projection,
                                );
                            // A cloned numeric transition owns a fresh state
                            // tuple on each entry. Permit that transition to
                            // escape a different enclosing region only when
                            // the tuple, control context, and incoming
                            // forwarding projection are authenticated.
                            const numeric_transition_projection = direct_projection != null;
                            const reaches_start_without_boundary = try self.canReachWithoutContinuationBoundary(
                                current,
                                start,
                                continue_target,
                            );
                            const reaches_context_start_without_boundary = try self.canReachWithoutContinuationBoundary(
                                current,
                                context.start,
                                continue_target,
                            );
                            const authenticated_numeric_reentry =
                                context.start != current and
                                context.stop != stop and
                                context.loop_exit == loop_exit and
                                context.continue_target == continue_target and
                                iteration_header and
                                parameters_match and
                                numeric_transition_projection and
                                (authenticated_iteration_entry or
                                    (!reaches_start_without_boundary and
                                        !reaches_context_start_without_boundary));
                            // An internal branch of the same numeric loop can
                            // re-enter the owned header with the same control
                            // boundary.  The owner context then starts at the
                            // current header, so the ordinary different-stop
                            // predicates above cannot admit it.  Require the
                            // complete authenticated entry proof plus an SCC
                            // edge; reachability in only one direction would
                            // incorrectly erase an acyclic effectful prefix.
                            const internal_numeric_reentry_reaches_source = if (projected_incoming) |reference|
                                try self.analysis.canReach(current, reference.source)
                            else
                                false;
                            const internal_numeric_reentry_reaches_current = if (projected_incoming) |reference|
                                try self.analysis.canReach(reference.source, current)
                            else
                                false;
                            const authenticated_internal_numeric_reentry =
                                context.start == current and
                                start != current and
                                context.stop == stop and
                                context.loop_exit == loop_exit and
                                context.continue_target == continue_target and
                                iteration_header and
                                parameters_match and
                                numeric_transition_projection and
                                authenticated_iteration_entry and
                                if (projected_incoming) |reference|
                                    reference.target == current and
                                        internal_numeric_reentry_reaches_source and
                                        internal_numeric_reentry_reaches_current
                                else
                                    false;
                            const authenticated_same_boundary_numeric_reentry =
                                try self.authenticatedSameBoundaryNumericReentry(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    context,
                                    parameters_match,
                                    projected_incoming,
                                );
                            const authenticated_internal_distinct_numeric_reentry =
                                try self.authenticatedInternalDistinctNumericReentry(
                                    current,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    context,
                                    parameters_match,
                                    projected_incoming,
                                );
                            const authenticated_same_context_distinct_numeric_reentry =
                                direct_projection != null and
                                try self.authenticatedSameContextDistinctNumericReentry(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    comparison_context,
                                    parameters_match,
                                    projected_incoming,
                                );
                            const authenticated_same_context_numeric_reentry =
                                try self.authenticatedSameContextNumericReentry(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    comparison_context,
                                    parameters_match,
                                    direct_projection != null,
                                    projected_incoming,
                                );
                            const authenticated_same_scc_numeric_reentry =
                                try self.authenticatedSameSccNumericReentry(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    comparison_context,
                                    parameters_match,
                                    direct_projection != null,
                                    projected_incoming,
                                );
                            const authenticated_same_stop_distinct_numeric_reentry =
                                try self.authenticatedSameStopDistinctNumericReentry(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    comparison_context,
                                    parameters_match,
                                    numeric_transition_projection,
                                    projected_incoming,
                                );
                            // A replay-authenticated loop edge can remain in
                            // the same SCC as the owned numeric header even
                            // when the generic boundary walk sees the old
                            // region start without crossing a boundary.  The
                            // reverse reachability check keeps this exception
                            // on a genuine loop-carried edge; the complete
                            // owner-tuple projection supplies the semantic
                            // proof.
                            const authenticated_same_scc_continuation =
                                context.start != current and
                                context.stop != stop and
                                context.loop_exit == loop_exit and
                                context.continue_target == continue_target and
                                iteration_header and
                                parameters_match and
                                numeric_transition_projection and
                                if (projected_incoming) |reference| blk: {
                                    if (reference.target != current or
                                        !try self.analysis.canReach(current, reference.source)) break :blk false;
                                    break :blk try self.authenticatedSameSccParameterizedReentry(
                                        current,
                                        start,
                                        loop_exit,
                                        continue_target,
                                        context,
                                        parameters_match,
                                        reference,
                                    );
                                } else false;
                            const authenticated_same_scc_distinct_tuple =
                                context.start != current and
                                context.stop != stop and
                                context.loop_exit == loop_exit and
                                context.continue_target == continue_target and
                                iteration_header and
                                !parameters_match and
                                numeric_transition_projection and
                                if (projected_incoming) |reference| blk: {
                                    if (reference.target != current or
                                        !try self.analysis.canReach(current, reference.source)) break :blk false;
                                    break :blk try self.authenticatedSameSccParameterizedReentry(
                                        current,
                                        start,
                                        loop_exit,
                                        continue_target,
                                        context,
                                        parameters_match,
                                        reference,
                                    );
                                } else false;
                            // A nonempty prefix can hand control back to an
                            // already-owned parameterized branch in the same
                            // SCC.  The empty-entry path already uses this
                            // proof; apply the same exact owner/tuple/replay
                            // contract before treating the shared branch as
                            // a fresh collision.
                            const authenticated_same_scc_parameterized_reentry =
                                !iteration_header and
                                if (projected_incoming) |reference| blk: {
                                    if (reference.target != current or
                                        !try self.analysis.canReach(current, reference.source)) break :blk false;
                                    break :blk try self.authenticatedSameSccParameterizedReentry(
                                        current,
                                        start,
                                        loop_exit,
                                        continue_target,
                                        context,
                                        parameters_match,
                                        reference,
                                    );
                                } else false;
                            const authenticated_parameterized_clone_handoff =
                                try self.authenticatedParameterizedCloneHandoffReentry(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    comparison_context,
                                    parameters_match,
                                    direct_projection != null,
                                    projected_incoming,
                                );
                            const authenticated_zero_parameter_loop_reentry =
                                direct_projection != null and
                                try self.authenticatedZeroParameterLoopHeaderReentry(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    comparison_context,
                                    parameters_match,
                                    projected_incoming,
                                );
                            const authenticated_independent_zero_parameter_loop_reentry =
                                direct_projection != null and
                                try self.authenticatedIndependentZeroParameterLoopReentry(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    escape_targets,
                                    continue_targets,
                                    comparison_context,
                                    parameters_match,
                                    projected_incoming,
                                );
                            const authenticated_visited_parameterized_projection =
                                blk: {
                                    const authenticated_entry_projection = authenticated_iteration_entry or
                                        if (entry_projection) |projection|
                                            projection.recovered_context_arguments
                                        else
                                            false;
                                    break :blk try self.authenticatedVisitedParameterizedContinuationProjection(
                                        current,
                                        start,
                                        stop,
                                        loop_exit,
                                        continue_target,
                                        comparison_context,
                                        parameters_match,
                                        projected_arguments,
                                        projected_incoming,
                                        direct_projection != null,
                                        authenticated_entry_projection,
                                    );
                                };
                            const authenticated_empty_numeric_forwarder =
                                direct_projection != null and
                                try self.authenticatedEmptyNumericForwarderReentry(
                                    current,
                                    start,
                                    stop,
                                    comparison_context,
                                    parameters_match,
                                    projected_incoming,
                                );
                            const transparent_empty_owned_stop_after_prefix =
                                self.transparentEmptyOwnedStopAfterPrefixContextMatches(
                                    current,
                                    start,
                                    stop,
                                    comparison_context,
                                    parameters_match,
                                );
                            if (iteration_header) {
                                structural_overlap.traceStructural("structural_phase numeric_reentry_candidate current={} start={} context_start={} stop={?} context_stop={?} parameters_match={} direct_projection={} visited_projection={} reaches_start_without_boundary={} reaches_context_start_without_boundary={} authenticated_iteration_entry={} authenticated_numeric_reentry={} authenticated_internal_numeric_reentry={} authenticated_same_boundary_numeric_reentry={} authenticated_internal_distinct_numeric_reentry={} authenticated_same_context_distinct_numeric_reentry={} authenticated_same_context_numeric_reentry={} authenticated_same_scc_numeric_reentry={} authenticated_same_stop_distinct_numeric_reentry={} internal_reentry_reaches_source={} internal_reentry_reaches_current={} authenticated_same_scc_continuation={} authenticated_same_scc_distinct_tuple={} authenticated_visited_parameterized={} incoming_source={?} incoming_target={?} current_arguments={} context_arguments={} current_parameters={any} projected_arguments={any} context_values={any}\\n", .{
                                    current.index(),
                                    start.index(),
                                    context.start.index(),
                                    if (stop) |value| value.index() else null,
                                    if (context.stop) |value| value.index() else null,
                                    parameters_match,
                                    direct_projection != null,
                                    authenticated_visited_parameterized_projection,
                                    reaches_start_without_boundary,
                                    reaches_context_start_without_boundary,
                                    authenticated_iteration_entry,
                                    authenticated_numeric_reentry,
                                    authenticated_internal_numeric_reentry,
                                    authenticated_same_boundary_numeric_reentry,
                                    authenticated_internal_distinct_numeric_reentry,
                                    authenticated_same_context_distinct_numeric_reentry,
                                    authenticated_same_context_numeric_reentry,
                                    authenticated_same_scc_numeric_reentry,
                                    authenticated_same_stop_distinct_numeric_reentry,
                                    internal_numeric_reentry_reaches_source,
                                    internal_numeric_reentry_reaches_current,
                                    authenticated_same_scc_continuation,
                                    authenticated_same_scc_distinct_tuple,
                                    authenticated_visited_parameterized_projection,
                                    if (projected_incoming) |reference| reference.source.index() else null,
                                    if (projected_incoming) |reference| reference.target.index() else null,
                                    if (projected_arguments) |values| values.len else 0,
                                    if (context.parameter_arguments) |values| values.len else 0,
                                    self.analysis.program.blocks[current.index()].parameters,
                                    projected_arguments orelse &.{},
                                    context_arguments orelse &.{},
                                });
                            }
                            if ((context.start != start and
                                ((same_control_context and
                                    !try self.analysis.canReach(current, start) and
                                    !try self.analysis.canReach(current, context.start)) or
                                    authenticated_numeric_reentry or
                                    authenticated_internal_numeric_reentry or
                                    authenticated_same_boundary_numeric_reentry or
                                    authenticated_internal_distinct_numeric_reentry or
                                    authenticated_same_scc_continuation or
                                    authenticated_same_scc_distinct_tuple or
                                    authenticated_same_scc_parameterized_reentry or
                                    authenticated_parameterized_clone_handoff or
                                    authenticated_same_stop_distinct_numeric_reentry or
                                    authenticated_zero_parameter_loop_reentry or
                                    authenticated_independent_zero_parameter_loop_reentry or
                                    authenticated_empty_numeric_forwarder or
                                    transparent_empty_owned_stop_after_prefix or
                                    transparent_empty_visited_context or
                                    authenticated_visited_parameterized_projection)) or
                                authenticated_same_context_distinct_numeric_reentry or
                                authenticated_same_context_numeric_reentry or
                                authenticated_same_scc_numeric_reentry)
                            {
                                const transfer: FinalContinueProjection = direct_projection orelse if (authenticated_same_scc_parameterized_reentry) blk: {
                                    const previous_node = nodes.items[nodes.items.len - 1];
                                    break :blk finalContinueProjection(
                                        self.analysis.program,
                                        previous_node,
                                        current,
                                    ) orelse return error.UnsupportedShape;
                                } else if (transparent_empty_owned_stop_after_prefix) blk: {
                                    const reference = current_incoming orelse return error.UnsupportedShape;
                                    if (reference.target != current) return error.UnsupportedShape;
                                    const edge = cfg_edge.value(self.analysis.program, reference) orelse
                                        return error.UnsupportedShape;
                                    break :blk .{ .edge = edge };
                                } else return error.UnsupportedShape;
                                const projected = try finishRegion(
                                    self.allocator,
                                    region,
                                    &nodes,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                );
                                projected.escape_projection = .{
                                    .target = current,
                                    .edge = switch (transfer) {
                                        .edge => |edge| edge,
                                        .transferred => null,
                                    },
                                };
                                return projected;
                            }
                        }
                    }
                    if (nodes.items.len == 0) {
                        if (self.visited_contexts[local_index]) |context| {
                            // An exact visit context identifies the same
                            // owned continuation. Reuse it as an empty
                            // projection; the caller still supplies and
                            // validates the incoming edge arguments.
                            const parameters_match = try self.parameterProjectionMatches(
                                current,
                                context.parameter_arguments,
                                current_arguments,
                            );
                            const exact_context = context.start == start and
                                context.stop == stop and
                                context.loop_exit == loop_exit and
                                context.continue_target == continue_target and
                                parameters_match;
                            const zero_argument_loop_context = self.zeroArgumentLoopContinuationContextMatches(
                                current,
                                start,
                                stop,
                                loop_exit,
                                continue_target,
                                context,
                                parameters_match,
                            );
                            const transparent_empty_context = context.stop != stop and
                                context.loop_exit == loop_exit and
                                context.continue_target == continue_target and
                                self.transparentEmptyContinuationContextMatches(
                                    current,
                                    start,
                                    stop,
                                    context,
                                    parameters_match,
                                );
                            const transparent_empty_owned_stop_context =
                                self.transparentEmptyOwnedStopContextMatches(
                                    current,
                                    start,
                                    stop,
                                    context,
                                    parameters_match,
                                );
                            const authenticated_same_entry_numeric_reentry =
                                try self.authenticatedSameEntryNumericReentry(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    context,
                                    parameters_match,
                                    current_incoming,
                                );
                            const authenticated_same_entry_parameterized_reentry =
                                try self.authenticatedSameEntryParameterizedReentry(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    context,
                                    parameters_match,
                                    current_arguments,
                                    current_incoming,
                                );
                            const authenticated_same_context_distinct_parameterized_reentry =
                                try self.authenticatedSameContextDistinctParameterizedReentry(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    context,
                                    parameters_match,
                                    current_incoming,
                                );
                            const authenticated_same_entry_nested_iteration_reentry =
                                try self.authenticatedSameEntryNestedIterationReentry(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    context,
                                    parameters_match,
                                    current_arguments,
                                    current_incoming,
                                );
                            const authenticated_same_scc_parameterized_reentry =
                                try self.authenticatedSameSccParameterizedReentry(
                                    current,
                                    start,
                                    loop_exit,
                                    continue_target,
                                    context,
                                    parameters_match,
                                    current_incoming,
                                );
                            const authenticated_internal_distinct_numeric_reentry =
                                try self.authenticatedInternalDistinctNumericReentry(
                                    current,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    context,
                                    parameters_match,
                                    current_incoming,
                                );
                            const identity_parameterized_continuation =
                                self.identityParameterizedContinuationContextMatches(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    context,
                                    parameters_match,
                                    current_arguments,
                                );
                            // An authenticated clone can re-enter a
                            // parameterized continuation with a different
                            // region boundary. The edge, rather than the
                            // remapped tuple alone, proves which clone owns
                            // this empty projection.
                            const authenticated_continuation = context.start != start and
                                context.loop_exit == loop_exit and
                                context.continue_target == continue_target and
                                parameters_match and
                                if (current_incoming) |reference| blk: {
                                    if (reference.target != current) break :blk false;
                                    self.trace_bridge_calls += 1;
                                    const bridge_start = structural_overlap.structuralPhaseNow();
                                    const result = try self.hasAuthenticatedContinuationBridge(reference);
                                    self.trace_bridge_ms += structural_overlap.structuralPhaseMillis(bridge_start);
                                    break :blk result;
                                } else false;
                            if (current == start and self.trace_empty_reentry_calls < 64) {
                                self.trace_empty_reentry_calls += 1;
                                const current_block = self.analysis.program.blocks[current.index()];
                                structural_overlap.traceStructural("structural_phase empty_reentry_candidate current={} start={} context_start={} stop={?} context_stop={?} loop_exit={?} context_loop_exit={?} continue_target={?} context_continue_target={?} parameters={} current_arguments={} context_arguments={} canonical={} terminator={s} exact={} zero_argument_loop={} transparent_empty={} transparent_owned_stop={} authenticated={} internal_distinct_numeric={} same_entry_numeric={} same_entry_parameterized={} same_scc_parameterized={} identity_parameterized={} incoming_source={?} incoming_target={?}\n", .{
                                    current.index(),
                                    start.index(),
                                    context.start.index(),
                                    if (stop) |value| value.index() else null,
                                    if (context.stop) |value| value.index() else null,
                                    if (loop_exit) |value| value.index() else null,
                                    if (context.loop_exit) |value| value.index() else null,
                                    if (continue_target) |value| value.index() else null,
                                    if (context.continue_target) |value| value.index() else null,
                                    current_block.parameters.len,
                                    if (current_arguments) |values| values.len else 0,
                                    if (context.parameter_arguments) |values| values.len else 0,
                                    node_split.parametersAreCanonical(self.analysis.program.values, current_block),
                                    @tagName(current_block.terminator),
                                    exact_context,
                                    zero_argument_loop_context,
                                    transparent_empty_context,
                                    transparent_empty_owned_stop_context,
                                    authenticated_continuation,
                                    authenticated_internal_distinct_numeric_reentry,
                                    authenticated_same_entry_numeric_reentry,
                                    authenticated_same_entry_parameterized_reentry,
                                    authenticated_same_scc_parameterized_reentry,
                                    identity_parameterized_continuation,
                                    if (current_incoming) |reference| reference.source.index() else null,
                                    if (current_incoming) |reference| reference.target.index() else null,
                                });
                            }
                            if (exact_context or zero_argument_loop_context or transparent_empty_context or
                                transparent_empty_owned_stop_context or
                                authenticated_continuation or authenticated_same_entry_numeric_reentry or
                                authenticated_same_entry_parameterized_reentry or
                                authenticated_same_context_distinct_parameterized_reentry or
                                authenticated_same_entry_nested_iteration_reentry or
                                authenticated_same_scc_parameterized_reentry or
                                authenticated_internal_distinct_numeric_reentry or
                                identity_parameterized_continuation)
                            {
                                const projected = try finishRegion(
                                    self.allocator,
                                    region,
                                    &nodes,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                );
                                projected.escape_projection = .{ .target = current, .edge = null };
                                return projected;
                            }
                        }
                    }
                    if (nodes.items.len != 0) {
                        if (self.visited_contexts[local_index]) |context| {
                            if (context.start != start and
                                context.stop == stop and
                                context.loop_exit == loop_exit and
                                context.continue_target == continue_target and
                                try self.parameterProjectionMatches(current, context.parameter_arguments, current_arguments) and
                                blk: {
                                    self.trace_bridge_calls += 1;
                                    const bridge_start = structural_overlap.structuralPhaseNow();
                                    const result = try self.hasStableNodeSplitBridgeFromNode(
                                        nodes.items[nodes.items.len - 1],
                                        current,
                                    );
                                    self.trace_bridge_ms += structural_overlap.structuralPhaseMillis(bridge_start);
                                    break :blk result;
                                })
                            {
                                const transfer = finalContinueProjection(
                                    self.analysis.program,
                                    nodes.items[nodes.items.len - 1],
                                    current,
                                ) orelse return error.UnsupportedShape;
                                const projected = try finishRegion(
                                    self.allocator,
                                    region,
                                    &nodes,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                );
                                projected.escape_projection = .{
                                    .target = current,
                                    .edge = switch (transfer) {
                                        .edge => |edge| edge,
                                        .transferred => null,
                                    },
                                };
                                return projected;
                            }
                        }
                    }
                    if (nodes.items.len != 0) {
                        const may_project_empty_terminal = if (self.visited_contexts[local_index]) |context|
                            // A same-entry revisit is still an ownership
                            // collision. The shortcut is only for a shared
                            // terminal reached through an already-owned
                            // prefix from another region.
                            context.start != current
                        else
                            true;
                        if (may_project_empty_terminal) if (self.emptyReturnTerminalProjection(
                            current,
                            current_arguments,
                            nodes.items[nodes.items.len - 1],
                        )) |projection| {
                            const projected = try finishRegion(
                                self.allocator,
                                region,
                                &nodes,
                                stop,
                                loop_exit,
                                continue_target,
                            );
                            projected.terminal_projection = projection;
                            return projected;
                        };
                    }
                    if (nodes.items.len != 0) {
                        if (self.visited_contexts[local_index]) |context| {
                            if (current_arguments) |arguments| if (current_incoming) |incoming| {
                                if (try self.authenticatedEffectfulPrefixReplay(
                                    current,
                                    start,
                                    stop,
                                    context,
                                    arguments,
                                    incoming,
                                )) |replay| {
                                    defer self.allocator.free(replay.nodes);
                                    try nodes.appendSlice(self.allocator, replay.nodes);
                                    current = replay.next;
                                    current_arguments = replay.arguments;
                                    current_incoming = .{
                                        .source = replay.source,
                                        .kind = .jump,
                                        .target = replay.next,
                                    };
                                    structural_overlap.traceStructural("structural_phase parameterized_effectful_prefix_replay current={} next={} nodes={} incoming_source={} incoming_target={}\n", .{
                                        current.index(),
                                        replay.next.index(),
                                        replay.nodes.len,
                                        replay.source.index(),
                                        replay.next.index(),
                                    });
                                    continue;
                                }
                            };
                        }
                    }
                    if (nodes.items.len != 0) {
                        if (self.visited_contexts[local_index]) |context| {
                            if (current_arguments) |arguments| if (current_incoming) |incoming| {
                                if (try self.authenticatedEffectfulZeroParameterPrefixReplay(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    context,
                                    arguments,
                                    incoming,
                                )) |replay| {
                                    defer self.allocator.free(replay.nodes);
                                    try nodes.appendSlice(self.allocator, replay.nodes);
                                    current = replay.next;
                                    current_arguments = replay.arguments;
                                    current_incoming = .{
                                        .source = replay.source,
                                        .kind = .jump,
                                        .target = replay.next,
                                    };
                                    continue;
                                }
                            };
                        }
                    }
                    if (nodes.items.len == 0) {
                        if (self.visited_contexts[local_index]) |context| {
                            if (current_arguments) |arguments| if (current_incoming) |incoming| {
                                if (try self.authenticatedSameEntryParameterizedPrefixReplay(
                                    current,
                                    start,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                    context,
                                    arguments,
                                    incoming,
                                )) |replay| {
                                    defer self.allocator.free(replay.nodes);
                                    try nodes.appendSlice(self.allocator, replay.nodes);
                                    current = replay.next;
                                    current_arguments = replay.arguments;
                                    current_incoming = .{
                                        .source = replay.source,
                                        .kind = .jump,
                                        .target = replay.next,
                                    };
                                    structural_overlap.traceStructural("structural_phase same_entry_parameterized_prefix_replay current={} next={} nodes={} incoming_source={} incoming_target={}\n", .{
                                        current.index(),
                                        replay.next.index(),
                                        replay.nodes.len,
                                        replay.source.index(),
                                        replay.next.index(),
                                    });
                                    continue;
                                }
                            };
                        }
                    }
                    if (nodes.items.len == 0) {
                        if (try self.authenticatedEffectfulTerminalReplay(
                            current,
                            start,
                            stop,
                            current_arguments,
                            current_incoming,
                        )) |replay| {
                            defer self.allocator.free(replay.nodes);
                            try nodes.appendSlice(self.allocator, replay.nodes);
                            const projected = try finishRegion(
                                self.allocator,
                                region,
                                &nodes,
                                stop,
                                loop_exit,
                                continue_target,
                            );
                            if (replay.terminal) |terminal| projected.terminal_projection = terminal;
                            return projected;
                        }
                    }
                }
                if (stage_trace.enabled) std.debug.print("COLLISION on block {d}! already_owned by outer region\n", .{current.index()});
                try self.noteCollisionNode(
                    current,
                    if (nodes.items.len == 0) null else nodes.items[nodes.items.len - 1],
                    current_incoming,
                    .already_owned,
                    .{
                        .start = start,
                        .stop = stop,
                        .loop_exit = loop_exit,
                        .continue_target = continue_target,
                        .parameter_arguments = current_arguments,
                    },
                );
                return error.UnsupportedShape;
            }
            if (!suppress_loop_detection) {
                if (stop) |stop_id| {
                    if (self.canProjectTerminal(current, stop_id, allowed)) {
                        const projected = try finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                        projected.terminal_projection = .{ .terminal = current, .edge = null };
                        return projected;
                    }
                }
            }
            try self.markVisited(local_index);
            try self.setVisitedContext(local_index, .{
                .start = start,
                .stop = stop,
                .loop_exit = loop_exit,
                .continue_target = continue_target,
                .parameter_arguments = current_arguments,
                .entry_reference = current_incoming,
            });

            const block = self.analysis.program.blocks[current.index()];
            switch (block.terminator) {
                .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {
                    try nodes.append(self.allocator, .{ .block = current });
                    return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                },
                .jump => |edge| {
                    if (!suppress_loop_detection and self.loop_headers[local_index]) {
                        const latch_probe_start = structural_overlap.structuralPhaseNow();
                        const latch_candidate = try self.buildLatchLoop(current, allowed, escape_targets, continue_targets, loop_exit, current_arguments, current_incoming);
                        const latch_probe_ms = structural_overlap.structuralPhaseMillis(latch_probe_start);
                        self.trace_loop_probe_calls += 1;
                        self.trace_loop_probe_ms += latch_probe_ms;
                        self.trace_build_latch_ms += latch_probe_ms;
                        if (latch_candidate) |loop| {
                            nodes.append(self.allocator, .{ .latch_loop = loop }) catch |err| {
                                destroyLatchLoop(self.allocator, loop);
                                return err;
                            };
                            if (isEscapeTarget(escape_targets, loop.exit)) {
                                return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                            }
                            current = loop.exit;
                            current_arguments = null;
                            current_incoming = null;
                            continue;
                        }
                        const infinite_probe_start = structural_overlap.structuralPhaseNow();
                        const infinite_candidate = try self.buildInfiniteLoop(current, allowed, stop, escape_targets, continue_targets, loop_exit, current_arguments, current_incoming);
                        const infinite_probe_ms = structural_overlap.structuralPhaseMillis(infinite_probe_start);
                        self.trace_loop_probe_calls += 1;
                        self.trace_loop_probe_ms += infinite_probe_ms;
                        self.trace_build_infinite_ms += infinite_probe_ms;
                        if (infinite_candidate) |loop| {
                            nodes.append(self.allocator, .{ .infinite_loop = loop }) catch |err| {
                                destroyInfiniteLoop(self.allocator, loop);
                                return err;
                            };
                            if (loop.exit) |exit| {
                                if (isEscapeTarget(escape_targets, exit)) {
                                    return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                                }
                                current = exit;
                                current_arguments = null;
                                current_incoming = null;
                                continue;
                            }
                            return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                        }
                    }
                    try nodes.append(self.allocator, .{ .block = current });
                    if (stop) |stop_id| {
                        if (self.canProjectTerminal(edge.target, stop_id, allowed)) {
                            const projected = try finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                            projected.terminal_projection = .{ .terminal = edge.target, .edge = edge };
                            return projected;
                        }
                    }
                    const incoming_reference: ir.CfgEdgeRef = .{
                        .source = current,
                        .kind = .jump,
                        .target = edge.target,
                    };
                    current = edge.target;
                    current_arguments = edge.arguments;
                    current_incoming = incoming_reference;
                },
                .branch => |branch| {
                    if (!suppress_loop_detection and self.loop_headers[local_index]) {
                        const loop_probe_start = structural_overlap.structuralPhaseNow();
                        const loop_candidate = try self.buildLoop(current, branch, allowed, escape_targets, continue_targets, loop_exit);
                        const loop_probe_ms = structural_overlap.structuralPhaseMillis(loop_probe_start);
                        self.trace_loop_probe_calls += 1;
                        self.trace_loop_probe_ms += loop_probe_ms;
                        self.trace_build_loop_ms += loop_probe_ms;
                        if (loop_candidate) |loop| {
                            nodes.append(self.allocator, .{ .loop = loop }) catch |err| {
                                destroyRegion(self.allocator, loop.body_region);
                                return err;
                            };
                            const exit_target = loop.exit_edge.target;
                            if ((stop != null and exit_target == stop.?) or
                                (loop_exit != null and exit_target == loop_exit.?) or
                                isEscapeTarget(escape_targets, exit_target))
                            {
                                return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                            }
                            current = exit_target;
                            current_arguments = loop.exit_edge.arguments;
                            current_incoming = .{
                                .source = loop.header,
                                .kind = if (loop.continue_on_true) .branch_else else .branch_then,
                                .target = exit_target,
                            };
                            continue;
                        }
                        const latch_probe_start = structural_overlap.structuralPhaseNow();
                        const latch_candidate = try self.buildLatchLoop(current, allowed, escape_targets, continue_targets, loop_exit, current_arguments, current_incoming);
                        const latch_probe_ms = structural_overlap.structuralPhaseMillis(latch_probe_start);
                        self.trace_loop_probe_calls += 1;
                        self.trace_loop_probe_ms += latch_probe_ms;
                        self.trace_build_latch_ms += latch_probe_ms;
                        if (latch_candidate) |loop| {
                            nodes.append(self.allocator, .{ .latch_loop = loop }) catch |err| {
                                destroyLatchLoop(self.allocator, loop);
                                return err;
                            };
                            if (isEscapeTarget(escape_targets, loop.exit)) {
                                return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                            }
                            current = loop.exit;
                            current_arguments = null;
                            current_incoming = null;
                            continue;
                        }
                        const infinite_probe_start = structural_overlap.structuralPhaseNow();
                        const infinite_candidate = try self.buildInfiniteLoop(current, allowed, stop, escape_targets, continue_targets, loop_exit, current_arguments, current_incoming);
                        const infinite_probe_ms = structural_overlap.structuralPhaseMillis(infinite_probe_start);
                        self.trace_loop_probe_calls += 1;
                        self.trace_loop_probe_ms += infinite_probe_ms;
                        self.trace_build_infinite_ms += infinite_probe_ms;
                        if (infinite_candidate) |loop| {
                            nodes.append(self.allocator, .{ .infinite_loop = loop }) catch |err| {
                                destroyInfiniteLoop(self.allocator, loop);
                                return err;
                            };
                            if (loop.exit) |exit| {
                                if (isEscapeTarget(escape_targets, exit)) {
                                    return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                                }
                                current = exit;
                                current_arguments = null;
                                current_incoming = null;
                                continue;
                            }
                            return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                        }
                    }
                    if (continue_target != null) {
                        const stop_id = stop orelse return error.UnsupportedShape;
                        if (loop_exit) |exit_id| {
                            if (makeLoopControl(current, branch, stop_id, exit_id)) |control| {
                                try nodes.append(self.allocator, .{ .loop_control = control });
                                return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                            }
                        }
                        const terminal_control_start = structural_overlap.structuralPhaseNow();
                        const terminal_control = try self.makeLoopTerminalControl(current, branch, stop_id, allowed);
                        if (region_step < 256) {
                            structural_overlap.traceStructural("structural_phase region_loop_control function={} step={} block={} phase=terminal_control result={} ms={}\\n", .{
                                self.analysis.function.id.index(),
                                region_step,
                                current.index(),
                                terminal_control != null,
                                structural_overlap.structuralPhaseMillis(terminal_control_start),
                            });
                        }
                        if (terminal_control) |control| {
                            try nodes.append(self.allocator, .{ .loop_terminal = control });
                            return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                        }
                        if (allowed) |membership| {
                            const rejoining_start = structural_overlap.structuralPhaseNow();
                            const rejoining = try self.buildLoopRejoiningBranch(
                                current,
                                branch,
                                membership,
                                stop_id,
                                continue_target.?,
                                loop_exit,
                                escape_targets,
                                continue_targets,
                            );
                            if (region_step < 256) {
                                structural_overlap.traceStructural("structural_phase region_loop_control function={} step={} block={} phase=rejoining result={} ms={}\\n", .{
                                    self.analysis.function.id.index(),
                                    region_step,
                                    current.index(),
                                    rejoining != null,
                                    structural_overlap.structuralPhaseMillis(rejoining_start),
                                });
                            }
                            if (rejoining) |rejoining_branch| {
                                const join = rejoining_branch.join.?;
                                const join_index = self.analysis.blockIndex(join) orelse return error.UnsupportedShape;
                                nodes.append(self.allocator, .{ .branch = rejoining_branch }) catch |err| {
                                    destroyBranch(self.allocator, rejoining_branch);
                                    return err;
                                };
                                if (membership[join_index]) {
                                    current = join;
                                    current_arguments = null;
                                    current_incoming = null;
                                    continue;
                                }
                                const projected = try finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                                if (isEscapeTarget(continue_targets, join)) {
                                    projected.continue_projection = .{ .target = join, .edge = null };
                                } else {
                                    projected.escape_projection = .{ .target = join, .edge = null };
                                }
                                return projected;
                            }
                        }
                        const boundary_control_start = structural_overlap.structuralPhaseNow();
                        const boundary_control = try self.makeLoopBoundaryControl(
                            current,
                            branch,
                            stop_id,
                            continue_target.?,
                            loop_exit,
                            escape_targets,
                            continue_targets,
                            allowed,
                        );
                        if (region_step < 256) {
                            structural_overlap.traceStructural("structural_phase region_loop_control function={} step={} block={} phase=boundary_control result={} ms={}\\n", .{
                                self.analysis.function.id.index(),
                                region_step,
                                current.index(),
                                boundary_control != null,
                                structural_overlap.structuralPhaseMillis(boundary_control_start),
                            });
                        }
                        if (boundary_control) |control| {
                            nodes.append(self.allocator, .{ .loop_boundary = control }) catch |err| {
                                destroyLoopBoundaryControl(self.allocator, control);
                                return err;
                            };
                            return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                        }
                    }

                    var convergence_boundaries: std.ArrayList(ir.BlockId) = .empty;
                    defer convergence_boundaries.deinit(self.allocator);
                    if (continue_target) |boundary| {
                        try appendBoundaryTarget(self.allocator, &convergence_boundaries, boundary);
                        if (loop_exit) |exit| try appendBoundaryTarget(self.allocator, &convergence_boundaries, exit);
                        try self.appendBoundaryTargets(&convergence_boundaries, escape_targets);
                        try self.appendBoundaryTargets(&convergence_boundaries, continue_targets);
                        if (allowed) |membership| {
                            try self.appendOutsideBoundaryEntries(&convergence_boundaries, membership);
                        }
                    }
                    if (region_step < 256) {
                        structural_overlap.traceStructural("structural_phase region_branch_convergence_begin function={} step={} block={} then={} else={} boundaries={}\n", .{
                            self.analysis.function.id.index(),
                            region_step,
                            current.index(),
                            branch.then_edge.target.index(),
                            branch.else_edge.target.index(),
                            convergence_boundaries.items.len,
                        });
                    }
                    const join_start = structural_overlap.structuralPhaseNow();
                    const bounded_join = if (convergence_boundaries.items.len != 0)
                        try self.analysis.immediateStructuralConvergenceBeforeAny(
                            self.allocator,
                            current,
                            convergence_boundaries.items,
                            allowed,
                        )
                    else
                        null;
                    self.trace_join_calls += 1;
                    var join = bounded_join;
                    if (join == null) {
                        join = (try self.analysis.immediateConvergence(self.allocator, current, allowed)) orelse
                            (try self.structuralIterationConvergence(current, allowed)) orelse
                            self.analysis.immediatePostDominator(current) orelse if (stop) |stop_id|
                            try self.analysis.immediatePostDominatorWithin(self.allocator, current, stop_id, allowed)
                        else
                            null;
                    }
                    self.trace_join_ms += structural_overlap.structuralPhaseMillis(join_start);
                    if (region_step < 256) {
                        structural_overlap.traceStructural("structural_phase region_branch_convergence_done function={} step={} block={} join={?}\n", .{
                            self.analysis.function.id.index(),
                            region_step,
                            current.index(),
                            join,
                        });
                    }
                    if (convergence_boundaries.items.len != 0) {
                        const direct_candidates = [_]struct { target: ir.BlockId, other: ir.BlockId }{
                            .{ .target = branch.then_edge.target, .other = branch.else_edge.target },
                            .{ .target = branch.else_edge.target, .other = branch.then_edge.target },
                        };
                        for (direct_candidates) |candidate| {
                            var is_boundary = false;
                            for (convergence_boundaries.items) |boundary| {
                                if (candidate.target == boundary) {
                                    is_boundary = true;
                                    break;
                                }
                            }
                            if (is_boundary) continue;
                            if (try self.analysis.allPathsReachTargetOrBoundariesAlloc(
                                self.allocator,
                                candidate.other,
                                candidate.target,
                                convergence_boundaries.items,
                                allowed,
                            )) {
                                join = candidate.target;
                                break;
                            }
                        }
                    }
                    if (stop) |stop_id| {
                        if (branch.then_edge.target == stop_id or branch.else_edge.target == stop_id) {
                            join = stop_id;
                        } else if (join) |join_id| {
                            if (join_id != stop_id and
                                !try self.analysis.canReachAvoiding(branch.then_edge.target, join_id, stop_id) and
                                !try self.analysis.canReachAvoiding(branch.else_edge.target, join_id, stop_id))
                            {
                                join = stop_id;
                            }
                        }
                    }
                    if (join) |candidate| {
                        // Nested arms can legitimately supply more than two
                        // predecessors. Dominance and unvisited ownership
                        // distinguish that join from an external shared suffix.
                        const owns_terminal = if (self.analysis.blockIndex(candidate)) |index|
                            !self.visited[index] and self.analysis.dominates(current, candidate)
                        else
                            false;
                        if (isTerminal(self.analysis.program.blocks[candidate.index()].terminator) and
                            self.analysis.predecessorCount(candidate) > 2 and
                            branch.then_edge.target != candidate and
                            branch.else_edge.target != candidate and
                            !owns_terminal)
                        {
                            join = null;
                        }
                    }
                    if (join) |candidate| {
                        if (self.active_shared_exits) |shared| {
                            if (sharedOwnsBlock(shared, candidate)) join = loop_exit;
                        }
                    }
                    if (join == null) join = try self.directSharedTerminalJoin(current, branch, allowed);
                    var then_reentry: loop_continue_shape.Reentry = .{};
                    defer then_reentry.deinit(self.allocator);
                    var else_reentry: loop_continue_shape.Reentry = .{};
                    defer else_reentry.deinit(self.allocator);
                    const reentry_target = if (continue_target != null and !suppress_loop_detection)
                        continue_target
                    else
                        stop;
                    if (reentry_target) |continue_id| {
                        then_reentry = try loop_continue_shape.classifyArmAlloc(
                            self.allocator,
                            self.analysis,
                            self.active_shared_reentries,
                            current,
                            .branch_then,
                            branch.then_edge,
                            continue_id,
                            allowed,
                        );
                        else_reentry = try loop_continue_shape.classifyArmAlloc(
                            self.allocator,
                            self.analysis,
                            self.active_shared_reentries,
                            current,
                            .branch_else,
                            branch.else_edge,
                            continue_id,
                            allowed,
                        );
                    }
                    const directly_reenters_loop = then_reentry.reenters or else_reentry.reenters;
                    var then_history_cut: ?forwarding_history_cut.Cut = null;
                    var else_history_cut: ?forwarding_history_cut.Cut = null;
                    if (!directly_reenters_loop and stop != null and
                        (continue_target == null or stop.? != continue_target.?))
                    {
                        then_history_cut = try forwarding_history_cut.findAlloc(
                            self.allocator,
                            self.analysis.program,
                            .{ .source = current, .kind = .branch_then, .target = branch.then_edge.target },
                            stop.?,
                        );
                        else_history_cut = try forwarding_history_cut.findAlloc(
                            self.allocator,
                            self.analysis.program,
                            .{ .source = current, .kind = .branch_else, .target = branch.else_edge.target },
                            stop.?,
                        );
                        if (then_history_cut != null or else_history_cut != null) join = stop;
                    }
                    const restores_local_stop = then_history_cut != null or else_history_cut != null;
                    const then_edge = if (then_history_cut) |cut| cut.edge else branch.then_edge;
                    const else_edge = if (else_history_cut) |cut| cut.edge else branch.else_edge;
                    const shared_control_join: ?ir.BlockId = if (!directly_reenters_loop and !restores_local_stop and
                        allowed != null and join != null)
                        try shared_control_shape.selectConvergenceAlloc(
                            self.allocator,
                            self.analysis,
                            current,
                            join.?,
                            convergence_boundaries.items,
                            allowed.?,
                        )
                    else
                        null;
                    if (stop != null and !restores_local_stop and shared_control_join == null and (directly_reenters_loop or
                        (join == null or join.? == stop.? or
                            (continue_target != null and join.? == continue_target.?) or
                            (loop_exit != null and join.? == loop_exit.?))))
                    {
                        const then_structured_edge = try then_reentry.structuredEdge(branch.then_edge);
                        const else_structured_edge = try else_reentry.structuredEdge(branch.else_edge);
                        const then_entry_reference = directEdgeReference(
                            self.analysis.program,
                            .{ .block = current },
                            then_structured_edge.target,
                        );
                        const else_entry_reference = directEdgeReference(
                            self.analysis.program,
                            .{ .block = current },
                            else_structured_edge.target,
                        );
                        const then_region = try self.buildRegionImplWithEntryArgumentsAndEdge(
                            then_structured_edge.target,
                            stop,
                            allowed,
                            loop_exit,
                            escape_targets,
                            continue_targets,
                            false,
                            continue_target,
                            then_structured_edge.arguments,
                            then_entry_reference,
                        );
                        const else_region = self.buildRegionImplWithEntryArgumentsAndEdge(
                            else_structured_edge.target,
                            stop,
                            allowed,
                            loop_exit,
                            escape_targets,
                            continue_targets,
                            false,
                            continue_target,
                            else_structured_edge.arguments,
                            else_entry_reference,
                        ) catch |err| {
                            destroyRegion(self.allocator, then_region);
                            return err;
                        };
                        self.consumeEdgeOverride(branch.then_edge, then_reentry.edge_override) catch |err| {
                            destroyRegion(self.allocator, then_region);
                            destroyRegion(self.allocator, else_region);
                            return err;
                        };
                        self.consumeEdgeOverride(branch.else_edge, else_reentry.edge_override) catch |err| {
                            destroyRegion(self.allocator, then_region);
                            destroyRegion(self.allocator, else_region);
                            return err;
                        };
                        const structured_branch: Branch = .{
                            .block = current,
                            .then_region = then_region,
                            .else_region = else_region,
                            .join = null,
                            .then_edge_override = if (then_reentry.takeEdgeOverride()) |path| .{ .forwarding = path } else null,
                            .else_edge_override = if (else_reentry.takeEdgeOverride()) |path| .{ .forwarding = path } else null,
                            .then_shared_reentry = then_reentry.shared_reentry,
                            .else_shared_reentry = else_reentry.shared_reentry,
                        };
                        nodes.append(self.allocator, .{ .branch = structured_branch }) catch |err| {
                            destroyBranch(self.allocator, structured_branch);
                            return err;
                        };
                        return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                    }
                    if (shared_control_join) |shared_join| {
                        const membership = allowed.?;
                        const final_join = join.?;
                        const shared_is_boundary = (stop != null and shared_join == stop.?) or
                            (loop_exit != null and shared_join == loop_exit.?) or
                            (continue_target != null and shared_join == continue_target.?);
                        const shared_index = self.analysis.blockIndex(shared_join) orelse return error.UnsupportedShape;
                        if (!shared_is_boundary and !self.visited[shared_index]) {
                            const final_escape: EscapeTarget = .{ .block = final_join, .parent = escape_targets };
                            const then_region = self.buildRegionImplWithEntryArgumentsAndEdge(
                                then_edge.target,
                                shared_join,
                                allowed,
                                loop_exit,
                                &final_escape,
                                continue_targets,
                                false,
                                continue_target,
                                then_edge.arguments,
                                directEdgeReference(self.analysis.program, .{ .block = current }, then_edge.target),
                            ) catch |err| {
                                self.noteCollisionEdge(.{ .source = current, .kind = .branch_then, .target = then_edge.target });
                                return err;
                            };
                            const else_region = self.buildRegionImplWithEntryArgumentsAndEdge(
                                else_edge.target,
                                shared_join,
                                allowed,
                                loop_exit,
                                &final_escape,
                                continue_targets,
                                false,
                                continue_target,
                                else_edge.arguments,
                                directEdgeReference(self.analysis.program, .{ .block = current }, else_edge.target),
                            ) catch |err| {
                                self.noteCollisionEdge(.{ .source = current, .kind = .branch_else, .target = else_edge.target });
                                destroyRegion(self.allocator, then_region);
                                return err;
                            };
                            const shared_branch: Branch = .{
                                .block = current,
                                .then_region = then_region,
                                .else_region = else_region,
                                .join = shared_join,
                                .then_edge_override = if (then_history_cut) |cut| .{ .history_cut = cut } else null,
                                .else_edge_override = if (else_history_cut) |cut| .{ .history_cut = cut } else null,
                            };
                            nodes.append(self.allocator, .{ .branch = shared_branch }) catch |err| {
                                destroyBranch(self.allocator, shared_branch);
                                return err;
                            };
                            if (membership[shared_index]) {
                                current = shared_join;
                                current_arguments = null;
                                current_incoming = null;
                                continue;
                            }
                            const projected = try finishRegion(
                                self.allocator,
                                region,
                                &nodes,
                                stop,
                                loop_exit,
                                continue_target,
                            );
                            if (isEscapeTarget(continue_targets, shared_join)) {
                                projected.continue_projection = .{ .target = shared_join, .edge = null };
                            } else {
                                projected.escape_projection = .{ .target = shared_join, .edge = null };
                            }
                            return projected;
                        }
                    }
                    var branch_escape: EscapeTarget = undefined;
                    const branch_escape_targets = if (join) |join_id| targets: {
                        branch_escape = .{ .block = join_id, .parent = escape_targets };
                        break :targets &branch_escape;
                    } else escape_targets;
                    const then_region = self.buildRegionImplWithEntryArgumentsAndEdge(
                        then_edge.target,
                        join,
                        allowed,
                        loop_exit,
                        branch_escape_targets,
                        continue_targets,
                        false,
                        continue_target,
                        then_edge.arguments,
                        directEdgeReference(self.analysis.program, .{ .block = current }, then_edge.target),
                    ) catch |err| {
                        self.noteCollisionEdge(.{ .source = current, .kind = .branch_then, .target = then_edge.target });
                        return err;
                    };
                    const else_region = self.buildRegionImplWithEntryArgumentsAndEdge(
                        else_edge.target,
                        join,
                        allowed,
                        loop_exit,
                        branch_escape_targets,
                        continue_targets,
                        false,
                        continue_target,
                        else_edge.arguments,
                        directEdgeReference(self.analysis.program, .{ .block = current }, else_edge.target),
                    ) catch |err| {
                        self.noteCollisionEdge(.{ .source = current, .kind = .branch_else, .target = else_edge.target });
                        destroyRegion(self.allocator, then_region);
                        return err;
                    };
                    if (join == null and
                        (regionHasTerminalJoinEscapedAcrossArms(
                            self.analysis.program,
                            then_region,
                            else_region,
                        ) or
                            regionHasTerminalJoinEscapedAcrossArms(
                                self.analysis.program,
                                else_region,
                                then_region,
                            )))
                    {
                        destroyRegion(self.allocator, then_region);
                        destroyRegion(self.allocator, else_region);
                        return error.UnsupportedShape;
                    }
                    const then_reaches_join = if (join) |join_id|
                        regionFallsThroughTo(self.analysis.program, then_region, join_id) or
                            regionOwnsEscape(then_region)
                    else
                        false;
                    const else_reaches_join = if (join) |join_id|
                        regionFallsThroughTo(self.analysis.program, else_region, join_id) or
                            regionOwnsEscape(else_region)
                    else
                        false;
                    nodes.append(self.allocator, .{ .branch = .{
                        .block = current,
                        .then_region = then_region,
                        .else_region = else_region,
                        .join = if (then_reaches_join or else_reaches_join) join else null,
                        .then_edge_override = if (then_history_cut) |cut| .{ .history_cut = cut } else null,
                        .else_edge_override = if (else_history_cut) |cut| .{ .history_cut = cut } else null,
                    } }) catch |err| {
                        destroyRegion(self.allocator, then_region);
                        destroyRegion(self.allocator, else_region);
                        return err;
                    };

                    if (join) |join_id| {
                        if (!then_reaches_join and !else_reaches_join) {
                            return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                        }
                        if (allowed) |membership| {
                            const join_index = self.analysis.blockIndex(join_id) orelse return error.UnsupportedShape;
                            if (!membership[join_index]) {
                                const projected = try finishRegion(
                                    self.allocator,
                                    region,
                                    &nodes,
                                    stop,
                                    loop_exit,
                                    continue_target,
                                );
                                if (isEscapeTarget(continue_targets, join_id)) {
                                    projected.continue_projection = .{ .target = join_id, .edge = null };
                                } else {
                                    projected.escape_projection = .{ .target = join_id, .edge = null };
                                }
                                return projected;
                            }
                        }
                        current = join_id;
                        current_arguments = null;
                        current_incoming = null;
                    } else {
                        return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
                    }
                },
            }
        }
        return finishRegion(self.allocator, region, &nodes, stop, loop_exit, continue_target);
    }

    fn forwardingContinueProjectionAlloc(
        self: *const Builder,
        final_node: Node,
        shared_entry: ir.BlockId,
        continue_target: ir.BlockId,
        stop: ?ir.BlockId,
        allowed: ?[]const bool,
    ) BuildError!?control_flow.ForwardingPath {
        const source = switch (final_node) {
            .block => |block_id| block_id,
            else => return null,
        };
        if (source.index() >= self.analysis.program.blocks.len) return error.UnsupportedShape;
        const raw = switch (self.analysis.program.blocks[source.index()].terminator) {
            .jump => |edge| edge,
            else => return null,
        };
        if (raw.target != shared_entry) return error.UnsupportedShape;

        var path = try control_flow.replayForwardingPathTo(
            self.allocator,
            self.analysis.program,
            raw,
            continue_target,
        ) orelse return null;
        var owns_path = true;
        defer if (owns_path) path.deinit(self.allocator);
        if (path.blocks.len == 0 or path.blocks[0] != shared_entry or path.edge.target != continue_target) {
            return error.UnsupportedShape;
        }
        for (path.blocks) |block_id| {
            if (stop != null and block_id == stop.?) return null;
            const block_index = self.analysis.blockIndex(block_id) orelse return error.UnsupportedShape;
            if (allowed) |membership| {
                if (block_index >= membership.len or !membership[block_index]) return null;
            }
            if (!self.analysis.isReachable(block_id) or !self.visited[block_index]) return null;
        }
        owns_path = false;
        return path;
    }

    fn canProjectTerminal(
        self: *const Builder,
        terminal_id: ir.BlockId,
        stop_id: ir.BlockId,
        allowed: ?[]const bool,
    ) bool {
        if (terminal_id == stop_id or terminal_id.index() >= self.analysis.program.blocks.len) return false;
        const terminal_index = self.analysis.blockIndex(terminal_id) orelse return false;
        if (allowed) |membership| {
            if (terminal_index >= membership.len or !membership[terminal_index]) return false;
        }
        if (self.visited[terminal_index]) return false;
        const terminal = self.analysis.program.blocks[terminal_id.index()];
        return isTerminal(terminal.terminator) and
            self.analysis.predecessorCount(terminal_id) > 1 and
            self.analysis.postDominates(terminal_id, stop_id);
    }

    fn directSharedTerminalJoin(
        self: *const Builder,
        branch_block: ir.BlockId,
        branch: ir.Branch,
        allowed: ?[]const bool,
    ) std.mem.Allocator.Error!?ir.BlockId {
        const edges = [_]ir.Edge{ branch.then_edge, branch.else_edge };
        for (edges, 0..) |edge, edge_index| {
            const candidate_index = self.analysis.blockIndex(edge.target) orelse continue;
            if (allowed) |membership| {
                if (candidate_index >= membership.len or !membership[candidate_index]) continue;
            }
            const candidate = self.analysis.program.blocks[edge.target.index()];
            if (!isTerminal(candidate.terminator) or self.visited[candidate_index] or
                !self.analysis.dominates(branch_block, candidate.id)) continue;

            // A direct shared-terminal claim transfers ownership of the
            // terminal to this branch. Every reachable predecessor must
            // therefore remain under the branch's dominance boundary. An
            // external predecessor would make the terminal a shared suffix
            // owned by another region, not this branch's join.
            var owns_all_predecessors = true;
            var predecessor_index: usize = 0;
            while (self.analysis.predecessorAt(candidate.id, predecessor_index)) |predecessor| : (predecessor_index += 1) {
                if (!self.analysis.dominates(branch_block, predecessor)) {
                    owns_all_predecessors = false;
                    break;
                }
            }
            if (!owns_all_predecessors) continue;

            const other = edges[1 - edge_index].target;
            if (try self.analysis.canReachAvoiding(other, candidate.id, branch_block)) return candidate.id;
        }
        return null;
    }

    fn ownedTransparentStopEdge(
        self: *const Builder,
        start: ir.BlockId,
        stop: ir.BlockId,
        allowed: ?[]const bool,
    ) ?ir.Edge {
        var current = start;
        var traversed: usize = 0;
        while (current != stop) : (traversed += 1) {
            if (traversed >= self.analysis.function.blocks.len) return null;
            const local_index = self.analysis.blockIndex(current) orelse return null;
            if (allowed) |membership| {
                if (local_index >= membership.len or !membership[local_index]) return null;
            }
            if (!self.visited[local_index]) return null;

            const block = self.analysis.program.blocks[current.index()];
            if (block.parameters.len != 0 or block.instructions.len != 0) return null;
            const edge = switch (block.terminator) {
                .jump => |value| value,
                else => return null,
            };
            if (edge.target == stop) {
                const stop_block = self.analysis.program.blocks[stop.index()];
                if (edge.arguments.len != stop_block.parameters.len) return null;
                return edge;
            }
            if (edge.arguments.len != 0) return null;
            current = edge.target;
        }
        return null;
    }

    fn buildLoop(
        self: *Builder,
        header: ir.BlockId,
        branch: ir.Branch,
        enclosing_allowed: ?[]const bool,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        enclosing_loop_exit: ?ir.BlockId,
    ) BuildError!?Loop {
        const checkpoint = self.beginMutation();
        errdefer self.rollbackMutation(checkpoint);
        const result = try self.buildLoopCore(
            header,
            branch,
            enclosing_allowed,
            escape_targets,
            continue_targets,
            enclosing_loop_exit,
        );
        if (result == null) {
            self.rollbackMutation(checkpoint);
        } else {
            self.finishMutation(checkpoint);
        }
        return result;
    }

    fn buildLoopCore(
        self: *Builder,
        header: ir.BlockId,
        branch: ir.Branch,
        enclosing_allowed: ?[]const bool,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        enclosing_loop_exit: ?ir.BlockId,
    ) BuildError!?Loop {
        var membership = (try self.collectNaturalLoop(header, enclosing_allowed)) orelse return null;
        defer membership.deinit();

        const then_index = self.analysis.blockIndex(branch.then_edge.target) orelse return error.UnsupportedShape;
        const else_index = self.analysis.blockIndex(branch.else_edge.target) orelse return error.UnsupportedShape;
        const then_is_body = membership.bits[then_index];
        const else_is_body = membership.bits[else_index];
        if (then_is_body == else_is_body) return null;
        const exit_shape = try natural_loop.classifyExit(self.analysis, membership.bits);
        switch (exit_shape) {
            .multiple => if (!try self.loopSecondaryExitsAreOwned(
                membership.bits,
                if (then_is_body) branch.else_edge.target else branch.then_edge.target,
                escape_targets,
                continue_targets,
                enclosing_loop_exit,
            )) return null,
            .closed, .unique => {},
        }

        const body_edge = if (then_is_body) branch.then_edge else branch.else_edge;
        const exit_edge = if (then_is_body) branch.else_edge else branch.then_edge;
        if (try self.outsideTerminalPath(enclosing_allowed, exit_edge.target) and
            (enclosing_loop_exit == null or exit_edge.target != enclosing_loop_exit.?)) return null;
        const body_reference: ir.CfgEdgeRef = .{
            .source = header,
            .kind = if (then_is_body) .branch_then else .branch_else,
            .target = body_edge.target,
        };
        const body_region = try self.buildLoopRegion(
            body_edge.target,
            header,
            membership.bits,
            exit_edge.target,
            escape_targets,
            continue_targets,
            body_edge.arguments,
            body_reference,
        );
        errdefer destroyRegion(self.allocator, body_region);

        for (membership.bits, 0..) |is_member, local_index| {
            if (is_member and local_index != membership.header_index and !self.visited[local_index]) return error.UnsupportedShape;
        }
        return .{
            .header = header,
            .body_region = body_region,
            .body_edge = body_edge,
            .exit_edge = exit_edge,
            .exit_is_escape = isEscapeTarget(escape_targets, exit_edge.target) or
                (enclosing_loop_exit != null and exit_edge.target == enclosing_loop_exit.?),
            .continue_on_true = then_is_body,
        };
    }

    fn outsideTerminalPath(
        self: *const Builder,
        membership: ?[]const bool,
        target: ir.BlockId,
    ) BuildError!bool {
        const allowed = membership orelse return false;
        const target_index = self.analysis.blockIndex(target) orelse return error.UnsupportedShape;
        if (allowed[target_index]) return false;
        return self.outsidePathMustTerminate(allowed, target);
    }

    // A node split can leave an empty clone just outside the active region.
    // It is safe to own only the clone itself when its authenticated edge
    // forwards directly to a boundary already owned by this structure.
    fn authenticatedTransparentOutsideProjection(
        self: *Builder,
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        entry_arguments: ?[]const ir.ValueId,
        entry_reference: ?ir.CfgEdgeRef,
        membership: []const bool,
    ) BuildError!?ir.Edge {
        const block_index = self.analysis.blockIndex(start) orelse return null;
        if (block_index >= membership.len or membership[block_index]) return null;
        if (!try self.parameterProjectionMatches(start, null, entry_arguments)) return null;
        if (self.visited[block_index]) return null;

        const block = self.analysis.program.blocks[start.index()];
        if (block.id != start or block.parameters.len != 0 or block.instructions.len != 0) return null;
        const edge = switch (block.terminator) {
            .jump => |value| value,
            else => return null,
        };
        if (edge.target == start or edge.target.index() >= self.analysis.program.blocks.len) return null;
        const target_block = self.analysis.program.blocks[edge.target.index()];
        if (edge.arguments.len != target_block.parameters.len) return null;

        if ((stop == null or edge.target != stop.?) and
            !isEscapeTarget(escape_targets, edge.target) and
            !isEscapeTarget(continue_targets, edge.target) and
            (loop_exit == null or edge.target != loop_exit.?))
        {
            return null;
        }

        const reference = entry_reference orelse try self.uniqueIncomingReference(start) orelse return null;
        if (reference.target != start) return null;
        const incoming = cfg_edge.value(self.analysis.program, reference) orelse return null;
        if (incoming.arguments.len != block.parameters.len or incoming.arguments.len != 0) return null;
        if (entry_arguments) |arguments| {
            if (!std.mem.eql(ir.ValueId, incoming.arguments, arguments)) return null;
        }
        if (!try self.hasAuthenticatedContinuationBridge(reference)) return null;
        return edge;
    }

    const TerminalOutsideResult = union(enum) {
        none,
        appended,
        projected: TerminalProjection,
    };

    fn appendTerminalOutsideRegion(
        self: *Builder,
        nodes: *std.ArrayList(Node),
        start: ir.BlockId,
        stop: ?ir.BlockId,
        loop_exit: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        entry_arguments: ?[]const ir.ValueId,
        entry_reference: ?ir.CfgEdgeRef,
        membership: []const bool,
    ) BuildError!TerminalOutsideResult {
        if (!try self.outsidePathMustTerminate(membership, start)) return .none;
        if (membership.len != self.analysis.function.blocks.len) return error.UnsupportedShape;
        const authenticated_entry = entry_reference orelse try self.uniqueIncomingReference(start) orelse return .none;

        const terminal_membership = try self.allocator.alloc(bool, membership.len);
        defer self.allocator.free(terminal_membership);
        @memset(terminal_membership, false);

        var shared_terminal: ?ir.BlockId = null;

        const pending = try self.allocator.alloc(ir.BlockId, membership.len);
        defer self.allocator.free(pending);
        const start_index = self.analysis.blockIndex(start) orelse return error.UnsupportedShape;
        if (self.visited[start_index]) return .none;
        terminal_membership[start_index] = true;
        pending[0] = start;
        var pending_index: usize = 0;
        var pending_len: usize = 1;
        while (pending_index < pending_len) : (pending_index += 1) {
            const current = pending[pending_index];
            for (0..self.analysis.successorCount(current)) |successor_index| {
                const successor = self.analysis.successorAt(current, successor_index) orelse return error.UnsupportedShape;
                const successor_local = self.analysis.blockIndex(successor) orelse return error.UnsupportedShape;
                if (membership[successor_local] or
                    successor == stop or
                    successor == loop_exit or
                    isEscapeTarget(escape_targets, successor) or
                    isEscapeTarget(continue_targets, successor))
                {
                    return .none;
                }
                if (self.visited[successor_local]) {
                    const successor_block = self.analysis.program.blocks[successor.index()];
                    const authenticated = try self.hasAuthenticatedContinuationBridge(authenticated_entry);
                    if (!isTerminal(successor_block.terminator) or
                        !authenticated) return .none;
                    if (shared_terminal) |existing| {
                        if (existing != successor) return .none;
                    } else {
                        shared_terminal = successor;
                    }
                    continue;
                }
                if (terminal_membership[successor_local]) continue;
                terminal_membership[successor_local] = true;
                pending[pending_len] = successor;
                pending_len += 1;
            }
        }

        if (shared_terminal) |terminal| {
            const terminal_index = self.analysis.blockIndex(terminal) orelse return error.UnsupportedShape;
            for (terminal_membership, 0..) |is_member, local_index| {
                if (!is_member) continue;
                const candidate = self.analysis.function.blocks[local_index];
                if (candidate == terminal) continue;
                if (isTerminal(self.analysis.program.blocks[candidate.index()].terminator)) return .none;
            }
            terminal_membership[terminal_index] = false;
            const terminal_region = try self.buildRegionImplWithEntryArgumentsAndEdge(
                start,
                terminal,
                terminal_membership,
                null,
                null,
                null,
                false,
                null,
                entry_arguments,
                authenticated_entry,
            );
            errdefer destroyRegion(self.allocator, terminal_region);
            if (terminal_region.stop != terminal or
                terminal_region.nodes.len == 0 or
                terminal_region.terminal_projection != null or
                terminal_region.continue_projection != null or
                terminal_region.escape_projection != null or
                terminal_region.stop_forwarding != null)
            {
                return .none;
            }
            const edge = switch (finalContinueProjection(
                self.analysis.program,
                terminal_region.nodes[terminal_region.nodes.len - 1],
                terminal,
            ) orelse return .appended) {
                .edge => |value| value,
                .transferred => null,
            };
            try nodes.appendSlice(self.allocator, terminal_region.nodes);
            self.allocator.free(terminal_region.nodes);
            self.allocator.destroy(terminal_region);
            return .{ .projected = .{ .terminal = terminal, .edge = edge } };
        }

        const terminal_region = try self.buildRegionImplWithEntryArgumentsAndEdge(
            start,
            null,
            terminal_membership,
            null,
            null,
            null,
            false,
            null,
            entry_arguments,
            entry_reference,
        );
        errdefer destroyRegion(self.allocator, terminal_region);
        if (terminal_region.nodes.len == 0 or
            terminal_region.stop != null or
            terminal_region.loop_exit != null or
            terminal_region.continue_projection != null or
            terminal_region.escape_projection != null or
            terminal_region.terminal_projection != null)
        {
            return error.UnsupportedShape;
        }
        try nodes.appendSlice(self.allocator, terminal_region.nodes);
        self.allocator.free(terminal_region.nodes);
        self.allocator.destroy(terminal_region);
        return .appended;
    }

    fn uniqueIncomingReference(self: *const Builder, target: ir.BlockId) BuildError!?ir.CfgEdgeRef {
        if (target.index() >= self.analysis.program.blocks.len or
            self.analysis.predecessorCount(target) != 1)
        {
            return null;
        }
        const predecessor = self.analysis.predecessorAt(target, 0) orelse return null;
        if (!self.analysis.isReachable(predecessor)) return null;
        return directEdgeReference(self.analysis.program, .{ .block = predecessor }, target);
    }

    fn loopSecondaryExitsAreOwned(
        self: *const Builder,
        membership: []const bool,
        primary_exit: ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        enclosing_loop_exit: ?ir.BlockId,
    ) BuildError!bool {
        if (membership.len != self.analysis.function.blocks.len) return error.UnsupportedShape;
        for (membership, 0..) |is_member, local_index| {
            if (!is_member) continue;
            const block_id = self.analysis.function.blocks[local_index];
            const terminator = self.analysis.program.blocks[block_id.index()].terminator;
            switch (terminator) {
                .jump => |edge| if (!try self.loopExitIsOwned(
                    membership,
                    edge.target,
                    primary_exit,
                    escape_targets,
                    continue_targets,
                    enclosing_loop_exit,
                )) return false,
                .branch => |candidate| {
                    if (!try self.loopExitIsOwned(
                        membership,
                        candidate.then_edge.target,
                        primary_exit,
                        escape_targets,
                        continue_targets,
                        enclosing_loop_exit,
                    )) return false;
                    if (!try self.loopExitIsOwned(
                        membership,
                        candidate.else_edge.target,
                        primary_exit,
                        escape_targets,
                        continue_targets,
                        enclosing_loop_exit,
                    )) return false;
                },
                .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
            }
        }
        return true;
    }

    fn loopExitIsOwned(
        self: *const Builder,
        membership: []const bool,
        target: ir.BlockId,
        primary_exit: ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        enclosing_loop_exit: ?ir.BlockId,
    ) BuildError!bool {
        const target_index = self.analysis.blockIndex(target) orelse return error.UnsupportedShape;
        if (membership[target_index] or target == primary_exit or
            isEscapeTarget(escape_targets, target) or isEscapeTarget(continue_targets, target) or
            (enclosing_loop_exit != null and target == enclosing_loop_exit.?)) return true;
        return self.outsidePathMustTerminateOrReach(membership, target, primary_exit);
    }

    fn outsidePathMustTerminate(
        self: *const Builder,
        membership: []const bool,
        start: ir.BlockId,
    ) BuildError!bool {
        const mutable_self = @constCast(self);
        const call_index = mutable_self.trace_outside_termination_calls;
        mutable_self.trace_outside_termination_calls += 1;
        const trace_call = call_index < 64;
        if (trace_call) {
            structural_overlap.traceStructural("structural_phase outside_termination_begin function={} call={} start={} membership={}\n", .{
                self.analysis.function.id.index(),
                call_index,
                start.index(),
                membership.len,
            });
        }
        const trace_start = structural_overlap.structuralPhaseNow();
        const result = natural_loop.outsidePathMustTerminateAlloc(self.allocator, self.analysis, membership, start);
        if (trace_call) {
            structural_overlap.traceStructural("structural_phase outside_termination_done function={} call={} start={} result={} ms={}\n", .{
                self.analysis.function.id.index(),
                call_index,
                start.index(),
                result catch false,
                structural_overlap.structuralPhaseMillis(trace_start),
            });
        }
        return result;
    }

    fn outsidePathMustTerminateOrReach(
        self: *const Builder,
        membership: []const bool,
        start: ir.BlockId,
        sink: ir.BlockId,
    ) BuildError!bool {
        const mutable_self = @constCast(self);
        const call_index = mutable_self.trace_outside_termination_calls;
        mutable_self.trace_outside_termination_calls += 1;
        const trace_call = call_index < 64;
        if (trace_call) {
            structural_overlap.traceStructural("structural_phase outside_termination_begin function={} call={} start={} membership={}\n", .{
                self.analysis.function.id.index(),
                call_index,
                start.index(),
                membership.len,
            });
        }
        const trace_start = structural_overlap.structuralPhaseNow();
        const result = natural_loop.outsidePathMustTerminateOrReachAlloc(self.allocator, self.analysis, membership, start, sink);
        if (trace_call) {
            structural_overlap.traceStructural("structural_phase outside_termination_done function={} call={} start={} result={} ms={}\n", .{
                self.analysis.function.id.index(),
                call_index,
                start.index(),
                result catch false,
                structural_overlap.structuralPhaseMillis(trace_start),
            });
        }
        return result;
    }

    fn buildLoopRejoiningBranch(
        self: *Builder,
        block: ir.BlockId,
        branch: ir.Branch,
        membership: []const bool,
        local_stop: ir.BlockId,
        loop_continue: ir.BlockId,
        loop_exit: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
    ) BuildError!?Branch {
        const checkpoint = self.beginMutation();
        errdefer self.rollbackMutation(checkpoint);
        const result = try self.buildLoopRejoiningBranchCore(
            block,
            branch,
            membership,
            local_stop,
            loop_continue,
            loop_exit,
            escape_targets,
            continue_targets,
        );
        if (result == null) {
            self.rollbackMutation(checkpoint);
        } else {
            self.finishMutation(checkpoint);
        }
        return result;
    }

    fn buildLoopRejoiningBranchCore(
        self: *Builder,
        block: ir.BlockId,
        branch: ir.Branch,
        membership: []const bool,
        local_stop: ir.BlockId,
        loop_continue: ir.BlockId,
        loop_exit: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
    ) BuildError!?Branch {
        const then_index = self.analysis.blockIndex(branch.then_edge.target) orelse return error.UnsupportedShape;
        const else_index = self.analysis.blockIndex(branch.else_edge.target) orelse return error.UnsupportedShape;
        if (loop_exit) |exit| {
            if (branch.then_edge.target == exit or branch.else_edge.target == exit) return null;
        }
        const then_is_member = membership[then_index];
        const else_is_member = membership[else_index];
        if (then_is_member == else_is_member) return null;

        const trace_rejoining = self.trace_region_step_calls < 256;
        if (trace_rejoining) {
            structural_overlap.traceStructural("structural_phase rejoining_phase function={} block={} then={} else={} phase=begin then_member={} else_member={}\\n", .{
                self.analysis.function.id.index(),
                block.index(),
                branch.then_edge.target.index(),
                branch.else_edge.target.index(),
                then_is_member,
                else_is_member,
            });
        }
        const final_join_start = structural_overlap.structuralPhaseNow();
        const direct_join = try self.analysis.immediateStructuralConvergenceBetween(
            self.allocator,
            branch.then_edge.target,
            branch.else_edge.target,
            null,
        );
        const postdom_join = if (direct_join == null) self.analysis.immediatePostDominator(block) else null;
        const final_join = direct_join orelse postdom_join orelse {
            if (trace_rejoining) {
                structural_overlap.traceStructural("structural_phase rejoining_phase function={} block={} phase=final_join result=null ms={}\\n", .{
                    self.analysis.function.id.index(),
                    block.index(),
                    structural_overlap.structuralPhaseMillis(final_join_start),
                });
            }
            return null;
        };
        if (trace_rejoining) {
            structural_overlap.traceStructural("structural_phase rejoining_phase function={} block={} phase=final_join result={} ms={}\\n", .{
                self.analysis.function.id.index(),
                block.index(),
                final_join.index(),
                structural_overlap.structuralPhaseMillis(final_join_start),
            });
        }
        var convergence_boundaries: std.ArrayList(ir.BlockId) = .empty;
        defer convergence_boundaries.deinit(self.allocator);
        try appendBoundaryTarget(self.allocator, &convergence_boundaries, local_stop);
        try appendBoundaryTarget(self.allocator, &convergence_boundaries, loop_continue);
        if (loop_exit) |exit| try appendBoundaryTarget(self.allocator, &convergence_boundaries, exit);
        try self.appendBoundaryTargets(&convergence_boundaries, escape_targets);
        try self.appendBoundaryTargets(&convergence_boundaries, continue_targets);
        const select_join_start = structural_overlap.structuralPhaseNow();
        const selected_join = try shared_control_shape.selectConvergenceAlloc(
            self.allocator,
            self.analysis,
            block,
            final_join,
            convergence_boundaries.items,
            membership,
        );
        const join = selected_join orelse final_join;
        if (trace_rejoining) {
            structural_overlap.traceStructural("structural_phase rejoining_phase function={} block={} phase=select_join result={} selected={} ms={}\\n", .{
                self.analysis.function.id.index(),
                block.index(),
                join.index(),
                selected_join != null,
                structural_overlap.structuralPhaseMillis(select_join_start),
            });
        }
        const reach_start = structural_overlap.structuralPhaseNow();
        const then_reaches_join = try self.analysis.canReachAvoiding(branch.then_edge.target, join, local_stop);
        const else_reaches_join = try self.analysis.canReachAvoiding(branch.else_edge.target, join, local_stop);
        if (trace_rejoining) {
            structural_overlap.traceStructural("structural_phase rejoining_phase function={} block={} phase=reach_join then={} else={} ms={}\\n", .{
                self.analysis.function.id.index(),
                block.index(),
                then_reaches_join,
                else_reaches_join,
                structural_overlap.structuralPhaseMillis(reach_start),
            });
        }
        if (join != local_stop and !then_reaches_join and !else_reaches_join) {
            return null;
        }
        const outside_target = if (then_is_member) branch.else_edge.target else branch.then_edge.target;
        if (join == outside_target) return null;
        const join_index = self.analysis.blockIndex(join) orelse return error.UnsupportedShape;
        if (self.visited[join_index] or join == local_stop or join == loop_continue or
            (loop_exit != null and join == loop_exit.?))
        {
            return null;
        }
        const outside = try self.allocator.alloc(bool, membership.len);
        defer self.allocator.free(outside);
        for (membership, 0..) |is_member, local_index| {
            outside[local_index] = !is_member and self.analysis.isReachable(self.analysis.function.blocks[local_index]);
        }

        const join_is_continue = isEscapeTarget(continue_targets, join);
        const final_join_escape: EscapeTarget = .{ .block = final_join, .parent = escape_targets };
        const outer_escape_targets = if (join == final_join) escape_targets else &final_join_escape;
        const join_escape: EscapeTarget = .{ .block = join, .parent = outer_escape_targets };
        const join_continue: EscapeTarget = .{ .block = join, .parent = continue_targets };
        const arm_escape_targets = if (join_is_continue) escape_targets else &join_escape;
        const arm_continue_targets = if (join_is_continue) &join_continue else continue_targets;
        const loop_exit_escape: EscapeTarget = .{ .block = loop_exit orelse join, .parent = arm_escape_targets };
        const bounded_escape_targets = if (loop_exit != null) &loop_exit_escape else arm_escape_targets;
        const then_allowed = if (then_is_member) membership else outside;
        const else_allowed = if (else_is_member) membership else outside;
        const then_region_start = structural_overlap.structuralPhaseNow();
        const then_region = self.buildRegionImplWithEntryArgumentsAndEdge(
            branch.then_edge.target,
            join,
            then_allowed,
            loop_exit,
            bounded_escape_targets,
            arm_continue_targets,
            false,
            loop_continue,
            branch.then_edge.arguments,
            .{ .source = block, .kind = .branch_then, .target = branch.then_edge.target },
        ) catch |err| {
            if (trace_rejoining) {
                structural_overlap.traceStructural("structural_phase rejoining_phase function={} block={} phase=then_region result=error ms={}\\n", .{
                    self.analysis.function.id.index(),
                    block.index(),
                    structural_overlap.structuralPhaseMillis(then_region_start),
                });
            }
            self.noteCollisionEdge(.{
                .source = block,
                .kind = .branch_then,
                .target = branch.then_edge.target,
            });
            return err;
        };
        if (trace_rejoining) {
            structural_overlap.traceStructural("structural_phase rejoining_phase function={} block={} phase=then_region result=ok ms={}\\n", .{
                self.analysis.function.id.index(),
                block.index(),
                structural_overlap.structuralPhaseMillis(then_region_start),
            });
        }
        const else_region_start = structural_overlap.structuralPhaseNow();
        const else_region = self.buildRegionImplWithEntryArgumentsAndEdge(
            branch.else_edge.target,
            join,
            else_allowed,
            loop_exit,
            bounded_escape_targets,
            arm_continue_targets,
            false,
            loop_continue,
            branch.else_edge.arguments,
            .{ .source = block, .kind = .branch_else, .target = branch.else_edge.target },
        ) catch |err| {
            if (trace_rejoining) {
                structural_overlap.traceStructural("structural_phase rejoining_phase function={} block={} phase=else_region result=error ms={}\\n", .{
                    self.analysis.function.id.index(),
                    block.index(),
                    structural_overlap.structuralPhaseMillis(else_region_start),
                });
            }
            self.noteCollisionEdge(.{
                .source = block,
                .kind = .branch_else,
                .target = branch.else_edge.target,
            });
            destroyRegion(self.allocator, then_region);
            return err;
        };
        if (trace_rejoining) {
            structural_overlap.traceStructural("structural_phase rejoining_phase function={} block={} phase=else_region result=ok ms={}\\n", .{
                self.analysis.function.id.index(),
                block.index(),
                structural_overlap.structuralPhaseMillis(else_region_start),
            });
        }
        return .{
            .block = block,
            .then_region = then_region,
            .else_region = else_region,
            .join = join,
        };
    }

    fn buildLatchLoop(
        self: *Builder,
        header: ir.BlockId,
        enclosing_allowed: ?[]const bool,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        enclosing_loop_exit: ?ir.BlockId,
        entry_arguments: ?[]const ir.ValueId,
        entry_reference: ?ir.CfgEdgeRef,
    ) BuildError!?LatchLoop {
        const checkpoint = self.beginMutation();
        errdefer self.rollbackMutation(checkpoint);
        const result = try self.buildLatchLoopCore(
            header,
            enclosing_allowed,
            escape_targets,
            continue_targets,
            enclosing_loop_exit,
            entry_arguments,
            entry_reference,
        );
        if (result == null) {
            self.rollbackMutation(checkpoint);
        } else {
            self.finishMutation(checkpoint);
        }
        return result;
    }

    fn buildLatchLoopCore(
        self: *Builder,
        header: ir.BlockId,
        enclosing_allowed: ?[]const bool,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        enclosing_loop_exit: ?ir.BlockId,
        entry_arguments: ?[]const ir.ValueId,
        entry_reference: ?ir.CfgEdgeRef,
    ) BuildError!?LatchLoop {
        var membership = (try self.collectNaturalLoop(header, enclosing_allowed)) orelse return null;
        defer membership.deinit();
        const shape = (try natural_loop.classifyPostTested(self.analysis, header, membership.bits)) orelse return null;
        const exit = try self.promoteLatchLoopExit(membership.bits, shape.exit);
        var shared_reentries: ?*loop_continue_shape.SharedPaths = null;
        var owns_shared_reentries = true;
        defer if (owns_shared_reentries) {
            if (shared_reentries) |paths| paths.deinit(self.allocator);
        };
        var shared_exits: ?*loop_exit_shape.SharedPaths = null;
        var owns_shared_exits = true;
        defer if (owns_shared_exits) {
            if (shared_exits) |paths| paths.deinit(self.allocator);
        };
        var exit_latches = try natural_loop.collectExitLatches(
            self.allocator,
            self.analysis,
            header,
            membership.bits,
            exit,
        );
        defer exit_latches.deinit();
        if (exit_latches.count != shape.latch_count) return null;

        shared_exits = loop_exit_shape.auditSharedAlloc(
            self.allocator,
            self.analysis,
            header,
            membership.bits,
            exit_latches.bits,
            exit,
        ) catch |err| switch (err) {
            error.UnsupportedShape => null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        if (shared_exits) |paths| try self.consumeSharedExits(paths, membership.bits);
        if (shape.has_non_latch_backedge) {
            shared_reentries = loop_continue_shape.auditAlloc(
                self.allocator,
                self.analysis,
                header,
                membership.bits,
                exit_latches.bits,
            ) catch |err| switch (err) {
                error.UnsupportedShape => null,
                error.OutOfMemory => return error.OutOfMemory,
            };
            if (shared_reentries) |paths| try self.consumeSharedReentries(paths, membership.bits);
        }

        try self.reopenLoopHeader(membership.header_index);
        const previous_shared_reentries = self.active_shared_reentries;
        self.active_shared_reentries = shared_reentries;
        defer self.active_shared_reentries = previous_shared_reentries;
        const previous_shared_exits = self.active_shared_exits;
        self.active_shared_exits = shared_exits;
        defer self.active_shared_exits = previous_shared_exits;
        const needs_latch_split = shape.single_latch != null and
            !shape.has_non_latch_backedge and
            self.analysis.immediatePostDominator(header) == exit;
        const body_region = if (needs_latch_split) body: {
            const latch = shape.single_latch.?;
            const prefix = try self.buildRegionIncludingStart(
                header,
                latch,
                membership.bits,
                exit,
                escape_targets,
                continue_targets,
                header,
                entry_arguments,
                entry_reference,
            );
            const suffix = self.buildRegionIncludingStart(
                latch,
                header,
                membership.bits,
                exit,
                escape_targets,
                continue_targets,
                header,
                null,
                null,
            ) catch |err| {
                destroyRegion(self.allocator, prefix);
                return err;
            };
            self.closePrefixAt(prefix, latch) catch |err| {
                destroyRegion(self.allocator, prefix);
                destroyRegion(self.allocator, suffix);
                return err;
            };
            break :body self.mergeSequentialRegions(prefix, suffix, header, exit) catch |err| {
                destroyRegion(self.allocator, prefix);
                destroyRegion(self.allocator, suffix);
                return err;
            };
        } else try self.buildRegionIncludingStart(
            header,
            header,
            membership.bits,
            exit,
            escape_targets,
            continue_targets,
            header,
            entry_arguments,
            entry_reference,
        );
        errdefer destroyRegion(self.allocator, body_region);

        for (membership.bits, 0..) |is_member, local_index| {
            if (is_member and !self.visited[local_index]) return error.UnsupportedShape;
        }

        owns_shared_reentries = false;
        owns_shared_exits = false;
        return .{
            .header = header,
            .body_region = body_region,
            .exit = exit,
            .exit_is_escape = isEscapeTarget(escape_targets, exit) or
                (enclosing_loop_exit != null and exit == enclosing_loop_exit.?),
            .latch_count = shape.latch_count,
            .shared_reentries = shared_reentries,
            .shared_exits = shared_exits,
        };
    }

    fn promoteLatchLoopExit(
        self: *const Builder,
        membership: []const bool,
        immediate_exit: ir.BlockId,
    ) BuildError!ir.BlockId {
        if (membership.len != self.analysis.function.blocks.len) return error.UnsupportedShape;
        const outside = try self.allocator.alloc(bool, membership.len);
        defer self.allocator.free(outside);
        for (membership, 0..) |is_member, index| outside[index] = !is_member;

        var promoted: ?ir.BlockId = null;
        for (self.analysis.function.blocks, 0..) |source, source_index| {
            if (!membership[source_index]) continue;
            for (0..self.analysis.successorCount(source)) |successor_index| {
                const target = self.analysis.successorAt(source, successor_index) orelse return error.UnsupportedShape;
                const target_index = self.analysis.blockIndex(target) orelse return error.UnsupportedShape;
                if (membership[target_index] or try self.analysis.canReach(target, immediate_exit)) continue;
                if (isTerminal(self.analysis.program.blocks[target.index()].terminator)) continue;

                const resolved_convergence = (try self.analysis.immediateStructuralConvergenceBetween(
                    self.allocator,
                    immediate_exit,
                    target,
                    outside,
                )) orelse return immediate_exit;
                const convergence_index = self.analysis.blockIndex(resolved_convergence) orelse return error.UnsupportedShape;
                if (membership[convergence_index] or
                    !try self.analysis.canReach(immediate_exit, resolved_convergence) or
                    !try self.analysis.canReach(target, resolved_convergence)) return immediate_exit;
                if (promoted) |existing| {
                    if (existing != resolved_convergence) return immediate_exit;
                } else {
                    promoted = resolved_convergence;
                }
            }
        }
        return promoted orelse immediate_exit;
    }

    fn closePrefixAt(_: *Builder, prefix: *Region, latch: ir.BlockId) BuildError!void {
        if (prefix.nodes.len == 0) return error.UnsupportedShape;
        const node = &prefix.nodes[prefix.nodes.len - 1];
        if (node.* != .branch) return error.UnsupportedShape;
        const branch = &node.branch;
        if (branch.join != null or branch.then_region.stop != latch or branch.else_region.stop != latch) {
            return error.UnsupportedShape;
        }
        branch.join = latch;
    }

    fn mergeSequentialRegions(
        self: *Builder,
        prefix: *Region,
        suffix: *Region,
        stop: ir.BlockId,
        loop_exit: ir.BlockId,
    ) BuildError!*Region {
        const region = try self.allocator.create(Region);
        errdefer self.allocator.destroy(region);
        const nodes = try self.allocator.alloc(Node, prefix.nodes.len + suffix.nodes.len);
        @memcpy(nodes[0..prefix.nodes.len], prefix.nodes);
        @memcpy(nodes[prefix.nodes.len..], suffix.nodes);

        self.allocator.free(prefix.nodes);
        self.allocator.destroy(prefix);
        self.allocator.free(suffix.nodes);
        self.allocator.destroy(suffix);
        region.* = .{
            .nodes = nodes,
            .stop = stop,
            .loop_exit = loop_exit,
            .continue_target = stop,
        };
        return region;
    }

    fn recordInfiniteSubphase(_: *Builder, calls: *usize, elapsed: *i64, start: i96) void {
        calls.* += 1;
        elapsed.* += structural_overlap.structuralPhaseMillis(start);
    }

    fn classifyInfiniteExitAtBoundary(
        self: *Builder,
        membership: []const bool,
        boundary: ?ir.BlockId,
    ) BuildError!natural_loop.ExitShape {
        const start = structural_overlap.structuralPhaseNow();
        const result = natural_loop.classifyExitAtBoundary(self.analysis, membership, boundary);
        self.recordInfiniteSubphase(&self.trace_infinite_classify_calls, &self.trace_infinite_classify_ms, start);
        return result;
    }

    fn selectInfiniteContinuation(
        self: *Builder,
        membership: []const bool,
    ) BuildError!?ir.BlockId {
        const start = structural_overlap.structuralPhaseNow();
        const result = natural_loop.selectContinuingExitConvergenceAlloc(
            self.allocator,
            self.analysis,
            membership,
        );
        self.recordInfiniteSubphase(
            &self.trace_infinite_continuation_calls,
            &self.trace_infinite_continuation_ms,
            start,
        );
        return result;
    }

    fn resolveInfiniteMultipleExit(
        self: *Builder,
        membership: []const bool,
        continuation: ir.BlockId,
    ) BuildError!?ir.BlockId {
        const start = structural_overlap.structuralPhaseNow();
        const result = self.resolveMultipleLoopExit(membership, continuation);
        self.recordInfiniteSubphase(&self.trace_infinite_resolve_calls, &self.trace_infinite_resolve_ms, start);
        return result;
    }

    fn selectInfiniteSharedEntries(
        self: *Builder,
        membership: []const bool,
        canonical_exit: ir.BlockId,
    ) BuildError![]ir.BlockId {
        const start = structural_overlap.structuralPhaseNow();
        const result = loop_side_exit.selectSharedRegionEntriesAllocWithReplayContext(
            self.allocator,
            self.analysis,
            membership,
            canonical_exit,
            self.replay_context,
        ) catch |err| {
            structural_overlap.traceStructural(
                "structural_phase shared_entry_call function={} canonical_exit={} error={s}\n",
                .{ self.analysis.function.id.index(), canonical_exit.index(), @errorName(err) },
            );
            return err;
        };
        structural_overlap.traceStructural(
            "structural_phase shared_entry_call function={} canonical_exit={} selected_count={}\n",
            .{ self.analysis.function.id.index(), canonical_exit.index(), result.len },
        );
        self.recordInfiniteSubphase(
            &self.trace_infinite_shared_entry_calls,
            &self.trace_infinite_shared_entry_ms,
            start,
        );
        return result;
    }

    // A loop body cannot own an already-structured effectful or parameterized
    // block outside its authenticated boundary. Detect that handoff before
    // recursively building the body; transparent empty forwarding remains
    // available to the normal projection logic below.
    fn infiniteLoopHasOwnedOutsideTarget(
        self: *const Builder,
        membership: []const bool,
        continuation: ?ir.BlockId,
        exit: ?ir.BlockId,
        shared_side_entries: []const ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        enclosing_loop_exit: ?ir.BlockId,
    ) BuildError!bool {
        for (membership, 0..) |is_member, local_index| {
            if (!is_member) continue;
            const block = self.analysis.function.blocks[local_index];
            for (0..self.analysis.successorCount(block)) |successor_index| {
                const target = self.analysis.successorAt(block, successor_index) orelse
                    return error.UnsupportedShape;
                const target_index = self.analysis.blockIndex(target) orelse
                    return error.UnsupportedShape;
                if (membership[target_index]) continue;
                if (continuation != null and target == continuation.?) continue;
                if (exit != null and target == exit.?) continue;
                if (containsBlockId(shared_side_entries, target)) continue;
                if (enclosing_loop_exit != null and target == enclosing_loop_exit.?) continue;
                if (isEscapeTarget(escape_targets, target) or isEscapeTarget(continue_targets, target)) continue;
                if (!self.visited[target_index]) continue;
                const target_block = self.analysis.program.blocks[target.index()];
                if (target_block.parameters.len != 0 or target_block.instructions.len != 0) return true;
            }
        }
        return false;
    }

    fn buildInfiniteLoop(
        self: *Builder,
        header: ir.BlockId,
        enclosing_allowed: ?[]const bool,
        continuation: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        enclosing_loop_exit: ?ir.BlockId,
        entry_arguments: ?[]const ir.ValueId,
        entry_reference: ?ir.CfgEdgeRef,
    ) BuildError!?InfiniteLoop {
        const checkpoint = self.beginMutation();
        errdefer self.rollbackMutation(checkpoint);
        const result = try self.buildInfiniteLoopCore(
            header,
            enclosing_allowed,
            continuation,
            escape_targets,
            continue_targets,
            enclosing_loop_exit,
            entry_arguments,
            entry_reference,
        );
        if (result == null) {
            self.rollbackMutation(checkpoint);
        } else {
            self.finishMutation(checkpoint);
        }
        return result;
    }

    fn buildInfiniteLoopCore(
        self: *Builder,
        header: ir.BlockId,
        enclosing_allowed: ?[]const bool,
        continuation: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        enclosing_loop_exit: ?ir.BlockId,
        entry_arguments: ?[]const ir.ValueId,
        entry_reference: ?ir.CfgEdgeRef,
    ) BuildError!?InfiniteLoop {
        const probe_index = self.trace_infinite_probe_calls;
        self.trace_infinite_probe_calls += 1;
        var membership = (try self.collectNaturalLoop(header, enclosing_allowed)) orelse return null;
        defer membership.deinit();
        if (probe_index < 32 or probe_index % 128 == 0) {
            structural_overlap.traceStructural("structural_phase infinite_probe function={} probe={} header={} members={} visited={} continuation={?} enclosing_exit={?}\n", .{
                self.analysis.function.id.index(),
                probe_index,
                header.index(),
                std.mem.countScalar(bool, membership.bits, true),
                self.visited_count,
                continuation,
                enclosing_loop_exit,
            });
        }
        if (enclosing_loop_exit != null and probe_index >= 32 and probe_index % 128 != 0) {
            structural_overlap.traceStructural("structural_phase infinite_probe_context function={} probe={} header={} members={} continuation={?} enclosing_exit={?}\n", .{
                self.analysis.function.id.index(),
                probe_index,
                header.index(),
                std.mem.countScalar(bool, membership.bits, true),
                continuation,
                enclosing_loop_exit,
            });
        }
        var structural_continuation = continuation orelse try self.authenticatedInactiveBranchTarget(header);
        if (structural_continuation == null) {
            if (probe_index < 32 or probe_index % 128 == 0) {
                structural_overlap.traceStructural("structural_phase infinite_probe_phase function={} probe={} header={} phase=select_continuation\n", .{
                    self.analysis.function.id.index(),
                    probe_index,
                    header.index(),
                });
            }
            switch (try self.classifyInfiniteExitAtBoundary(membership.bits, null)) {
                .multiple => structural_continuation = try self.selectInfiniteContinuation(membership.bits),
                .closed, .unique => {},
            }
        }
        var exit: ?ir.BlockId = switch (try self.classifyInfiniteExitAtBoundary(membership.bits, structural_continuation)) {
            .closed => null,
            .unique => |target| target,
            .multiple => multiple: {
                if (structural_continuation) |target| {
                    if (try self.resolveInfiniteMultipleExit(membership.bits, target)) |selected| {
                        break :multiple selected;
                    }
                }
                const fallback = try self.selectInfiniteContinuation(membership.bits) orelse return null;
                if (structural_continuation == null or fallback != structural_continuation.?) {
                    if (try self.resolveInfiniteMultipleExit(membership.bits, fallback)) |selected| {
                        break :multiple selected;
                    }
                }
                return null;
            },
        };
        const exit_index = if (exit) |target| self.analysis.blockIndex(target) orelse return error.UnsupportedShape else null;
        const exit_is_enclosing_continuation = if (exit) |target|
            (continuation != null and target == continuation.?) or isEscapeTarget(continue_targets, target) or
                (enclosing_loop_exit != null and target == enclosing_loop_exit.?)
        else
            false;
        if (exit_index) |index| if (self.visited[index] and !exit_is_enclosing_continuation) return null;

        var shared_side_entries: []ir.BlockId = &.{};
        var owns_shared_side_entries = false;
        defer if (owns_shared_side_entries) self.allocator.free(shared_side_entries);
        if (exit) |canonical_exit| {
            shared_side_entries = try self.selectInfiniteSharedEntries(membership.bits, canonical_exit);
            owns_shared_side_entries = true;
            for (shared_side_entries) |entry| {
                const entry_index = self.analysis.blockIndex(entry) orelse return error.UnsupportedShape;
                if (self.visited[entry_index]) {
                    self.allocator.free(shared_side_entries);
                    shared_side_entries = &.{};
                    owns_shared_side_entries = false;
                    break;
                }
            }
        }
        if (try self.infiniteLoopHasOwnedOutsideTarget(
            membership.bits,
            continuation,
            exit,
            shared_side_entries,
            escape_targets,
            continue_targets,
            enclosing_loop_exit,
        )) return null;
        // A nested loop must pass its enclosing loop exit through the parent
        // region.  Otherwise a child side-exit can claim the parent's
        // effectful exit block, leaving the parent with a stale `.exit`
        // boundary after ownership accounting observes that block as visited.
        var enclosing_escape: EscapeTarget = undefined;
        const parent_escape_targets = if (enclosing_loop_exit) |parent_exit| targets: {
            break :targets prependEscapeTarget(&enclosing_escape, parent_exit, escape_targets);
        } else escape_targets;
        var shared_escapes: []EscapeTarget = &.{};
        defer if (shared_escapes.len != 0) self.allocator.free(shared_escapes);
        const body_escape_targets = if (shared_side_entries.len != 0) targets: {
            shared_escapes = try self.allocator.alloc(EscapeTarget, shared_side_entries.len);
            for (shared_escapes, 0..) |*target, index| {
                target.* = .{
                    .block = shared_side_entries[index],
                    .parent = if (index + 1 < shared_escapes.len)
                        &shared_escapes[index + 1]
                    else
                        parent_escape_targets,
                };
            }
            break :targets &shared_escapes[0];
        } else parent_escape_targets;

        if (probe_index < 32 or probe_index % 128 == 0) {
            structural_overlap.traceStructural("structural_phase infinite_probe_phase function={} probe={} header={} phase=body continuation={?} exit={?} shared_entries={}\n", .{
                self.analysis.function.id.index(),
                probe_index,
                header.index(),
                structural_continuation,
                exit,
                shared_side_entries.len,
            });
        }
        try self.reopenLoopHeader(membership.header_index);
        const body_region_start = structural_overlap.structuralPhaseNow();
        const body_region_result = self.buildRegionIncludingStart(
            header,
            header,
            membership.bits,
            exit,
            body_escape_targets,
            continue_targets,
            header,
            entry_arguments,
            entry_reference,
        );
        self.recordInfiniteSubphase(
            &self.trace_infinite_body_calls,
            &self.trace_infinite_body_ms,
            body_region_start,
        );
        const body_region = body_region_result catch |err| {
            structural_overlap.traceStructural("structural_phase infinite_body_failed header={} depth={} visited={} exit={?} continuation={?} shared_entries={} error={s}\n", .{
                header.index(),
                self.trace_region_depth,
                self.visited_count,
                exit,
                continuation,
                shared_side_entries.len,
                @errorName(err),
            });
            return err;
        };
        errdefer destroyRegion(self.allocator, body_region);
        for (membership.bits, 0..) |is_member, local_index| {
            if (is_member and !self.visited[local_index]) {
                structural_overlap.traceStructural("structural_phase infinite_body_unvisited header={} member={} members={} visited={} exit={?} continuation={?} shared_entries={}\n", .{
                    header.index(),
                    self.analysis.function.blocks[local_index].index(),
                    std.mem.countScalar(bool, membership.bits, true),
                    self.visited_count,
                    exit,
                    continuation,
                    shared_side_entries.len,
                });
                self.noteUnvisitedLoopMember(membership.bits, local_index);
                return error.UnsupportedShape;
            }
        }
        if (shared_side_entries.len == 0) {
            if (exit) |canonical_exit| {
                const free_targets = try regionFreeTargetsAlloc(self.allocator, body_region);
                defer self.allocator.free(free_targets);
                var selected = std.ArrayList(ir.BlockId).empty;
                defer selected.deinit(self.allocator);
                for (free_targets) |target| {
                    const target_index = self.analysis.blockIndex(target) orelse return error.UnsupportedShape;
                    if (membership.bits[target_index] or self.visited[target_index] or target == canonical_exit or
                        !try natural_loop.canReachOutsideLoopAlloc(
                            self.allocator,
                            self.analysis,
                            membership.bits,
                            target,
                            canonical_exit,
                        ))
                    {
                        continue;
                    }
                    try selected.append(self.allocator, target);
                }
                if (selected.items.len != 0) {
                    shared_side_entries = try selected.toOwnedSlice(self.allocator);
                    owns_shared_side_entries = true;
                }
            }
        }
        var shared_side_exit: ?SharedSideExit = null;
        errdefer if (shared_side_exit) |side_exit| destroySharedSideExit(self.allocator, side_exit);
        if (shared_side_entries.len != 0) {
            const canonical_exit = exit orelse return error.UnsupportedShape;
            const outside = try self.allocator.alloc(bool, membership.bits.len);
            defer self.allocator.free(outside);
            for (membership.bits, 0..) |is_member, index| {
                outside[index] = !is_member and self.analysis.isReachable(self.analysis.function.blocks[index]);
            }
            shared_side_exit = try self.buildSharedSideExit(
                shared_side_entries,
                canonical_exit,
                outside,
                escape_targets,
                continue_targets,
            );
        }
        if (exit_index) |index| {
            if (self.visited[index] and !exit_is_enclosing_continuation) {
                body_region.loop_exit = null;
                exit = null;
            }
        }
        return .{
            .header = header,
            .body_region = body_region,
            .exit = exit,
            .exit_is_escape = if (exit) |target|
                isEscapeTarget(escape_targets, target) or
                    (enclosing_loop_exit != null and target == enclosing_loop_exit.?)
            else
                false,
            .shared_side_exit = shared_side_exit,
        };
    }

    fn buildSharedSideExit(
        self: *Builder,
        entries: []const ir.BlockId,
        canonical_exit: ir.BlockId,
        outside: []const bool,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
    ) BuildError!?SharedSideExit {
        if (entries.len == 0) return null;
        var owned = try self.allocator.alloc(SharedSideEntry, entries.len);
        var built_count: usize = 0;
        var transferred = false;
        defer if (!transferred) {
            for (owned[0..built_count]) |side| destroyRegion(self.allocator, side.region);
            self.allocator.free(owned);
        };

        for (entries, 0..) |entry, index| {
            var shadowed_escape_targets = try shadowEscapeTargetsAlloc(
                self.allocator,
                escape_targets,
                entry,
            );
            defer shadowed_escape_targets.deinit(self.allocator);
            var filtered_escape_targets = try self.filterTerminalEscapeTargetsAlloc(
                shadowed_escape_targets.targets,
            );
            defer filtered_escape_targets.deinit(self.allocator);
            const side_escape: EscapeTarget = .{
                .block = canonical_exit,
                .parent = filtered_escape_targets.targets,
            };
            const side_region = try self.buildRegionImplWithEntryArguments(
                entry,
                canonical_exit,
                outside,
                null,
                &side_escape,
                continue_targets,
                false,
                null,
                null,
            );
            owned[index] = .{ .entry = entry, .region = side_region };
            built_count += 1;
        }

        const result = ownSharedSideRegions(self.allocator, owned) catch |err| {
            transferred = true;
            return err;
        };
        transferred = true;
        return result;
    }

    fn resolveMultipleLoopExit(
        self: *const Builder,
        membership: []const bool,
        continuation: ir.BlockId,
    ) BuildError!?ir.BlockId {
        if (try natural_loop.selectExitReaching(self.analysis, membership, continuation)) |selected| return selected;
        if (try natural_loop.allContinuingExitsReach(
            self.allocator,
            self.analysis,
            membership,
            continuation,
        )) return continuation;
        return null;
    }

    fn authenticatedInactiveBranchTarget(self: *const Builder, header: ir.BlockId) BuildError!?ir.BlockId {
        if (header.index() >= self.analysis.program.blocks.len) return null;
        const live = switch (self.analysis.program.blocks[header.index()].terminator) {
            .jump => |edge| edge,
            else => return null,
        };
        var selected: ?ir.BlockId = null;
        for (self.analysis.program.obligations) |obligation| {
            const subject = switch (obligation.subject) {
                .control_branch => |value| value,
                else => continue,
            };
            if (subject.block != header) continue;
            const replay = control_flow.replayControlBranchObligation(self.analysis.program, obligation) orelse continue;
            if (replay.subject.block != header or
                replay.selected.target != live.target or
                !std.mem.eql(ir.ValueId, replay.selected.arguments, live.arguments))
            {
                continue;
            }
            var inactive = if (replay.truth) replay.subject.branch.else_edge else replay.subject.branch.then_edge;
            var owns_inactive = false;
            defer if (owns_inactive and inactive.arguments.len != 0) self.allocator.free(inactive.arguments);
            var remaining = self.analysis.function.blocks.len + 1;
            while (remaining != 0 and !self.analysis.isReachable(inactive.target)) : (remaining -= 1) {
                if (self.analysis.blockIndex(inactive.target) == null) break;
                const forwarded = try control_flow.replayForwardingJump(
                    self.allocator,
                    self.analysis.program,
                    inactive,
                ) orelse break;
                if (owns_inactive and inactive.arguments.len != 0) self.allocator.free(inactive.arguments);
                inactive = forwarded;
                owns_inactive = true;
            }
            if (!self.analysis.isReachable(inactive.target)) continue;
            if (selected) |existing| {
                if (existing != inactive.target) return null;
            } else {
                selected = inactive.target;
            }
        }
        return selected;
    }

    fn structuralIterationConvergence(
        self: *const Builder,
        block: ir.BlockId,
        allowed: ?[]const bool,
    ) BuildError!?ir.BlockId {
        const immediate = try self.analysis.immediateStructuralConvergence(self.allocator, block, allowed);
        if (immediate) |candidate| {
            if (structural_overlap.isIterationTransitionHeader(self.analysis.program, candidate) or
                try self.authenticatedInactiveBranchTarget(candidate) != null) return candidate;
        }

        if (try structural_overlap.selectIterationConvergence(
            self.allocator,
            self.analysis,
            block,
            allowed,
        )) |selection| return selection.join;
        return null;
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

    fn collectNaturalLoop(self: *Builder, header: ir.BlockId, enclosing_allowed: ?[]const bool) BuildError!?natural_loop.Membership {
        const header_index = self.analysis.blockIndex(header) orelse return error.UnsupportedShape;
        if (header_index >= self.loop_headers.len or !self.loop_headers[header_index]) return null;
        if (self.loop_memberships) |cache| {
            const bits = if (cache[header_index]) |cached| cached else blk: {
                var collected = (try natural_loop.collect(self.allocator, self.analysis, header)) orelse return null;
                errdefer collected.deinit();
                const cached = try self.allocator.dupe(bool, collected.bits);
                collected.deinit();
                try self.installLoopMembership(header_index, cached);
                break :blk cached;
            };
            const cached_validation = self.cachedLoopValidation(header_index, enclosing_allowed);
            if (cached_validation == .invalid) return error.UnsupportedShape;
            if (cached_validation == .uncomputed) {
                try self.validateNaturalLoopMembership(header_index, bits, enclosing_allowed);
            }
            return .{
                .allocator = self.allocator,
                .bits = bits,
                .header_index = header_index,
                .owns_bits = false,
            };
        }

        var membership = (try natural_loop.collect(self.allocator, self.analysis, header)) orelse return null;
        errdefer membership.deinit();
        try self.validateNaturalLoopMembership(header_index, membership.bits, enclosing_allowed);
        return membership;
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

    fn consumeSharedReentries(
        self: *Builder,
        shared: *const loop_continue_shape.SharedPaths,
        membership: []const bool,
    ) BuildError!void {
        if (shared.blocks.len == 0 or shared.entries.len < 2) return error.UnsupportedShape;
        for (shared.blocks) |block_id| {
            const block_index = self.analysis.blockIndex(block_id) orelse return error.UnsupportedShape;
            if (!membership[block_index] or !self.analysis.isReachable(block_id) or self.visited[block_index]) {
                return error.UnsupportedShape;
            }
            try self.markVisited(block_index);
        }
    }

    fn consumeSharedExits(
        self: *Builder,
        shared: *const loop_exit_shape.SharedPaths,
        membership: []const bool,
    ) BuildError!void {
        if (shared.blocks.len == 0 or shared.entries.len < 2) return error.UnsupportedShape;
        for (shared.blocks) |block_id| {
            const block_index = self.analysis.blockIndex(block_id) orelse return error.UnsupportedShape;
            if (membership[block_index] or !self.analysis.isReachable(block_id) or self.visited[block_index]) {
                return error.UnsupportedShape;
            }
            try self.markVisited(block_index);
        }
    }

    fn consumeEdgeOverride(self: *Builder, raw: ir.Edge, edge_override: ?control_flow.ForwardingPath) BuildError!void {
        const path = edge_override orelse return;
        if (path.blocks.len == 0 or path.blocks[0] != raw.target) return error.UnsupportedShape;
        for (path.blocks) |block_id| {
            const block_index = self.analysis.blockIndex(block_id) orelse return error.UnsupportedShape;
            if (!self.analysis.isReachable(block_id) or self.visited[block_index]) return error.UnsupportedShape;
            try self.markVisited(block_index);
        }
    }

    fn makeLoopTerminalControl(
        self: *Builder,
        block: ir.BlockId,
        branch: ir.Branch,
        continue_target: ir.BlockId,
        allowed: ?[]const bool,
    ) BuildError!?LoopTerminalControl {
        const continue_on_true = if (branch.then_edge.target == continue_target)
            true
        else if (branch.else_edge.target == continue_target)
            false
        else
            return null;
        const continue_edge = if (continue_on_true) branch.then_edge else branch.else_edge;
        const terminal_edge = if (continue_on_true) branch.else_edge else branch.then_edge;
        const terminal_index = self.analysis.blockIndex(terminal_edge.target) orelse return error.UnsupportedShape;
        if (allowed) |membership| if (membership[terminal_index]) return null;
        const terminal = self.analysis.program.blocks[terminal_edge.target.index()];
        if (!isTerminal(terminal.terminator)) return null;
        if (!self.analysis.isReachable(terminal.id) or self.visited[terminal_index]) return error.UnsupportedShape;
        try self.markVisited(terminal_index);
        return .{
            .block = block,
            .continue_edge = continue_edge,
            .terminal_edge = terminal_edge,
            .terminal_block = terminal.id,
            .continue_on_true = continue_on_true,
        };
    }

    fn makeLoopBoundaryControl(
        self: *Builder,
        block: ir.BlockId,
        branch: ir.Branch,
        local_stop: ir.BlockId,
        loop_continue: ir.BlockId,
        exit_target: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        allowed: ?[]const bool,
    ) BuildError!?LoopBoundaryControl {
        const membership = allowed orelse return null;
        const then_index = self.analysis.blockIndex(branch.then_edge.target) orelse return error.UnsupportedShape;
        const else_index = self.analysis.blockIndex(branch.else_edge.target) orelse return error.UnsupportedShape;
        const then_is_body = membership[then_index];
        const else_is_body = membership[else_index];
        if (then_is_body == else_is_body) return null;
        const body_on_true = then_is_body;
        const body_edge = if (body_on_true) branch.then_edge else branch.else_edge;
        const boundary_edge = if (body_on_true) branch.else_edge else branch.then_edge;
        const body_reference: ir.CfgEdgeRef = .{
            .source = block,
            .kind = if (body_on_true) .branch_then else .branch_else,
            .target = body_edge.target,
        };
        const continue_target = if (local_stop != loop_continue and
            try self.analysis.canReachAvoiding(body_edge.target, local_stop, loop_continue))
            local_stop
        else
            loop_continue;
        const boundary_kind: ir.CfgEdgeKind = if (body_on_true) .branch_else else .branch_then;
        const shared_exit = if (self.active_shared_exits) |shared|
            shared.entryRef(.{ .source = block, .kind = boundary_kind, .target = boundary_edge.target })
        else
            null;

        const boundary: LoopBoundary = if (shared_exit) |entry|
            .{ .shared_exit = entry }
        else if (isEscapeTarget(escape_targets, boundary_edge.target))
            .{ .escape = boundary_edge }
        else if (exit_target != null and boundary_edge.target == exit_target.?)
            .{ .exit = boundary_edge }
        else blk: {
            const terminal_index = self.analysis.blockIndex(boundary_edge.target) orelse return error.UnsupportedShape;
            const terminal = self.analysis.program.blocks[boundary_edge.target.index()];
            if (isTerminal(terminal.terminator)) {
                if (!self.analysis.isReachable(terminal.id) or self.visited[terminal_index]) return error.UnsupportedShape;
                try self.markVisited(terminal_index);
                break :blk .{ .terminal = .{ .edge = boundary_edge, .block = terminal.id } };
            }
            const outside = try self.allocator.alloc(bool, membership.len);
            defer self.allocator.free(outside);
            for (membership, 0..) |is_member, local_index| {
                outside[local_index] = !is_member and self.analysis.isReachable(self.analysis.function.blocks[local_index]);
            }
            var filtered_escape_targets = try self.filterTerminalEscapeTargetsAlloc(escape_targets);
            defer filtered_escape_targets.deinit(self.allocator);
            if (try self.forwardedEscapeTarget(
                boundary_edge.target,
                continue_target,
                exit_target,
                filtered_escape_targets.targets,
                continue_targets,
                membership,
            )) |target| {
                const side_region = self.buildRegionImplWithEntryArgumentsAndEdge(
                    boundary_edge.target,
                    target,
                    outside,
                    null,
                    filtered_escape_targets.targets,
                    continue_targets,
                    false,
                    null,
                    boundary_edge.arguments,
                    .{ .source = block, .kind = boundary_kind, .target = boundary_edge.target },
                ) catch |err| {
                    self.noteCollisionEdge(.{ .source = block, .kind = boundary_kind, .target = boundary_edge.target });
                    return err;
                };
                break :blk .{ .side_escape = .{
                    .entry_edge = boundary_edge,
                    .region = side_region,
                    .target = target,
                } };
            }

            const continuation = exit_target orelse return null;
            const side_escape: EscapeTarget = .{ .block = continuation, .parent = filtered_escape_targets.targets };
            const side_region = self.buildRegionImplWithEntryArgumentsAndEdge(
                boundary_edge.target,
                continuation,
                outside,
                null,
                &side_escape,
                continue_targets,
                false,
                null,
                boundary_edge.arguments,
                .{ .source = block, .kind = boundary_kind, .target = boundary_edge.target },
            ) catch |err| {
                self.noteCollisionEdge(.{ .source = block, .kind = boundary_kind, .target = boundary_edge.target });
                return err;
            };
            break :blk .{ .side_exit = .{ .entry_edge = boundary_edge, .region = side_region } };
        };
        errdefer destroyLoopBoundary(self.allocator, boundary);

        const body_region = try self.buildLoopRegion(
            body_edge.target,
            continue_target,
            membership,
            exit_target,
            escape_targets,
            continue_targets,
            body_edge.arguments,
            body_reference,
        );
        errdefer destroyRegion(self.allocator, body_region);
        return .{
            .block = block,
            .body_edge = body_edge,
            .body_region = body_region,
            .boundary = boundary,
            .body_on_true = body_on_true,
        };
    }

    fn forwardedEscapeTarget(
        self: *const Builder,
        start: ir.BlockId,
        current_continue: ir.BlockId,
        current_exit: ?ir.BlockId,
        escape_targets: ?*const EscapeTarget,
        continue_targets: ?*const EscapeTarget,
        membership: []const bool,
    ) BuildError!?ir.BlockId {
        const start_index = self.analysis.blockIndex(start) orelse return error.UnsupportedShape;
        if (membership.len != self.analysis.function.blocks.len or
            membership[start_index] or
            !self.analysis.isReachable(start)) return null;

        // Both target chains ask the same outside-loop reachability question.
        // Build one forward closure, preserving the existing escape-chain
        // ordering when selecting the first authenticated target.
        const reachable = try self.allocator.alloc(bool, membership.len);
        defer self.allocator.free(reachable);
        const pending = try self.allocator.alloc(ir.BlockId, membership.len);
        defer self.allocator.free(pending);
        @memset(reachable, false);
        reachable[start_index] = true;
        pending[0] = start;
        var pending_index: usize = 0;
        var pending_len: usize = 1;
        while (pending_index < pending_len) : (pending_index += 1) {
            const current = pending[pending_index];
            for (0..self.analysis.successorCount(current)) |successor_index| {
                const successor = self.analysis.successorAt(current, successor_index) orelse
                    return error.UnsupportedShape;
                const successor_local = self.analysis.blockIndex(successor) orelse return error.UnsupportedShape;
                if ((current_exit != null and successor == current_exit.?) or
                    membership[successor_local] or
                    reachable[successor_local]) continue;
                reachable[successor_local] = true;
                pending[pending_len] = successor;
                pending_len += 1;
            }
        }

        var current = escape_targets;
        while (current) |candidate| : (current = candidate.parent) {
            if (candidate.block == current_continue) continue;
            if (current_exit != null and candidate.block == current_exit.?) continue;
            const candidate_index = self.analysis.blockIndex(candidate.block) orelse return error.UnsupportedShape;
            if (isTerminal(self.analysis.program.blocks[candidate.block.index()].terminator)) continue;
            if (reachable[candidate_index]) return candidate.block;
        }
        current = continue_targets;
        while (current) |candidate| : (current = candidate.parent) {
            if (candidate.block == current_continue) continue;
            if (current_exit != null and candidate.block == current_exit.?) continue;
            const candidate_index = self.analysis.blockIndex(candidate.block) orelse return error.UnsupportedShape;
            if (isTerminal(self.analysis.program.blocks[candidate.block.index()].terminator)) continue;
            if (reachable[candidate_index]) return candidate.block;
        }
        return null;
    }

    fn appendBoundaryTargets(
        self: *const Builder,
        boundaries: *std.ArrayList(ir.BlockId),
        targets: ?*const EscapeTarget,
    ) std.mem.Allocator.Error!void {
        var current = targets;
        while (current) |target| : (current = target.parent) {
            try appendBoundaryTarget(self.allocator, boundaries, target.block);
        }
    }

    fn appendOutsideBoundaryEntries(
        self: *const Builder,
        boundaries: *std.ArrayList(ir.BlockId),
        membership: []const bool,
    ) BuildError!void {
        if (membership.len != self.analysis.function.blocks.len) return error.UnsupportedShape;
        const semantic_boundary_count = boundaries.items.len;
        for (self.analysis.function.blocks, 0..) |source, source_index| {
            if (!membership[source_index]) continue;
            for (0..self.analysis.successorCount(source)) |successor_index| {
                const target = self.analysis.successorAt(source, successor_index) orelse return error.UnsupportedShape;
                const target_index = self.analysis.blockIndex(target) orelse return error.UnsupportedShape;
                if (membership[target_index]) continue;
                for (boundaries.items[0..semantic_boundary_count]) |boundary| {
                    const boundary_index = self.analysis.blockIndex(boundary) orelse return error.UnsupportedShape;
                    if (membership[boundary_index]) continue;
                    if (target == boundary or try natural_loop.canReachOutsideLoopAlloc(
                        self.allocator,
                        self.analysis,
                        membership,
                        target,
                        boundary,
                    )) {
                        try appendBoundaryTarget(self.allocator, boundaries, target);
                        break;
                    }
                }
            }
        }
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

test "same visit context reuses an owned continuation" {
    const function_id = ir.FunctionId.fromIndex(0);
    const start = ir.BlockId.fromIndex(0);
    const middle = ir.BlockId.fromIndex(1);
    const stop = ir.BlockId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = start, .function = function_id, .terminator = .{ .jump = .{ .target = middle } } },
        .{ .id = middle, .function = function_id, .terminator = .{ .jump = .{ .target = stop } } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ start, middle, stop },
        .entry_block = start,
    };
    const program: ir.Program = .{
        .program_id = "same-context-continuation",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ true, false, false };
    var contexts = [_]?Builder.VisitContext{ .{
        .start = start,
        .stop = stop,
        .loop_exit = null,
        .continue_target = null,
    }, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const reused = try builder.buildRegionImpl(start, stop, null, null, null, null, false, null);
    defer destroyRegion(std.testing.allocator, reused);
    try std.testing.expectEqual(@as(usize, 0), reused.nodes.len);
    try std.testing.expect(reused.escape_projection != null);
    try std.testing.expectEqual(start, reused.escape_projection.?.target);
    try std.testing.expect(reused.escape_projection.?.edge == null);

    contexts[0].?.stop = null;
    var rejected_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    try std.testing.expectError(
        error.UnsupportedShape,
        rejected_builder.buildRegionImpl(start, stop, null, null, null, null, false, null),
    );
}

test "same-start different-stop reuse rejects an effectful continuation" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const first_source = ir.BlockId.fromIndex(1);
    const second_source = ir.BlockId.fromIndex(2);
    const start = ir.BlockId.fromIndex(3);
    const first_stop = ir.BlockId.fromIndex(4);
    const second_stop = ir.BlockId.fromIndex(5);
    const original = ir.BlockId.fromIndex(6);
    const condition = ir.ValueId.fromIndex(0);
    const table = ir.ValueId.fromIndex(1);
    const key = ir.ValueId.fromIndex(2);
    const read = ir.ValueId.fromIndex(3);
    const constant_id = ir.InstructionId.fromIndex(0);
    const read_id = ir.InstructionId.fromIndex(1);
    const write_id = ir.InstructionId.fromIndex(2);
    const place = ir.PlaceId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first_source },
            .else_edge = .{ .target = second_source },
        } } },
        .{ .id = first_source, .function = function_id, .terminator = .{ .jump = .{ .target = start } } },
        .{ .id = second_source, .function = function_id, .terminator = .{ .jump = .{ .target = start } } },
        .{ .id = start, .function = function_id, .instructions = &.{ constant_id, read_id, write_id }, .terminator = .{ .jump = .{ .target = first_stop } } },
        .{ .id = first_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = second_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ condition, table },
        .blocks = &.{ entry, first_source, second_source, start, first_stop, second_stop, original },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = table, .function = function_id, .type = .{ .kind = .table }, .origin = .{ .parameter = 1 } },
        .{ .id = key, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = constant_id, .index = 0 } } },
        .{ .id = read, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } } },
    };
    const places = [_]ir.Place{.{
        .id = place,
        .function = function_id,
        .type = .dynamic,
        .origin = .{ .local = 0 },
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = constant_id, .block = start, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{key}, .effects = .pure },
        .{ .id = read_id, .block = start, .operation = .{ .table_get = .{ .table = table, .key = key, .mode = .semantic } }, .results = &.{read}, .effects = .semantic_table_read },
        .{ .id = write_id, .block = start, .operation = .{ .place_write = .{ .place = place, .value = read } }, .results = &.{}, .effects = .place_write },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = first_source,
            .kind = .jump,
            .from = .{ .target = original },
            .to = .{ .target = start },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = second_source,
            .kind = .jump,
            .from = .{ .target = original },
            .to = .{ .target = start },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
    };
    const program: ir.Program = .{
        .program_id = "same-start-different-stop-effectful-continuation",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, false, false, true, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, .{
        .start = start,
        .stop = first_stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &.{},
    }, null, null, null };
    var collision: ?Collision = null;
    defer if (collision) |*value| value.deinit(std.testing.allocator);
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
        .collision = &collision,
    };

    try std.testing.expectError(
        error.UnsupportedShape,
        builder.buildRegionImpl(start, second_stop, null, null, null, null, false, null),
    );
    try std.testing.expect(collision != null);
    const recorded = collision.?;
    try std.testing.expectEqual(start, recorded.block);
    try std.testing.expectEqual(first_stop, recorded.owner_context.?.stop.?);
    try std.testing.expectEqual(second_stop, recorded.incoming_context.?.stop.?);
    try std.testing.expectEqual(@as(usize, 2), recorded.incoming_group.len);
    for (recorded.incoming_group) |reference| {
        try std.testing.expectEqual(start, reference.target);
        try std.testing.expectEqual(@as(usize, 0), cfg_edge.value(&program, reference).?.arguments.len);
    }
}

test "authenticated effectful terminal replay preserves an owned bridge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const first_source = ir.BlockId.fromIndex(1);
    const second_source = ir.BlockId.fromIndex(2);
    const start = ir.BlockId.fromIndex(3);
    const first_stop = ir.BlockId.fromIndex(4);
    const second_stop = ir.BlockId.fromIndex(5);
    const original = ir.BlockId.fromIndex(6);
    const condition = ir.ValueId.fromIndex(0);
    const result = ir.ValueId.fromIndex(1);
    const original_result = ir.ValueId.fromIndex(2);
    const constant_id = ir.InstructionId.fromIndex(0);
    const original_constant_id = ir.InstructionId.fromIndex(1);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first_source },
            .else_edge = .{ .target = second_source },
        } } },
        .{ .id = first_source, .function = function_id, .terminator = .{ .jump = .{ .target = start } } },
        .{ .id = second_source, .function = function_id, .terminator = .{ .jump = .{ .target = start } } },
        .{ .id = start, .function = function_id, .instructions = &.{constant_id}, .terminator = .{ .jump = .{ .target = first_stop } } },
        .{ .id = first_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = second_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original, .function = function_id, .instructions = &.{original_constant_id}, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, first_source, second_source, start, first_stop, second_stop, original },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = constant_id, .index = 0 } } },
        .{ .id = original_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = original_constant_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = constant_id, .block = start, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{result}, .effects = .pure },
        .{ .id = original_constant_id, .block = original, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{original_result}, .effects = .pure },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = first_source,
            .kind = .jump,
            .from = .{ .target = original },
            .to = .{ .target = start },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = second_source,
            .kind = .jump,
            .from = .{ .target = original },
            .to = .{ .target = start },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
    };
    const program: ir.Program = .{
        .program_id = "authenticated-effectful-terminal-replay",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, false, false, true, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, .{
        .start = start,
        .stop = first_stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &.{},
    }, null, null, null };
    var collision: ?Collision = null;
    defer if (collision) |*value| value.deinit(std.testing.allocator);
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
        .collision = &collision,
    };
    const replayed = try builder.buildRegionImplWithEntryArgumentsAndEdge(
        start,
        second_stop,
        null,
        null,
        null,
        null,
        false,
        null,
        &.{},
        .{ .source = second_source, .kind = .jump, .target = start },
    );
    defer destroyRegion(std.testing.allocator, replayed);
    try std.testing.expectEqual(@as(usize, 1), replayed.nodes.len);
    try std.testing.expectEqual(start, replayed.nodes[0].block);
    try std.testing.expectEqual(second_stop, replayed.stop.?);
    try std.testing.expectEqual(first_stop, replayed.terminal_projection.?.terminal);
    try std.testing.expect(replayed.terminal_projection.?.edge != null);
    try std.testing.expect(collision == null);
}

const TerminalContinuationReplayWitness = enum {
    valid,
    missing_bridge,
    pure_suffix,
    wrong_return_origin,
    matching_stop,
    parameterized_suffix,
};

fn terminalContinuationReplayWitness(witness: TerminalContinuationReplayWitness) !bool {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner_source = ir.BlockId.fromIndex(1);
    const incoming_source = ir.BlockId.fromIndex(2);
    const current = ir.BlockId.fromIndex(3);
    const terminal = ir.BlockId.fromIndex(4);
    const owner_stop = ir.BlockId.fromIndex(5);
    const incoming_stop = ir.BlockId.fromIndex(6);
    const original = ir.BlockId.fromIndex(7);
    const condition = ir.ValueId.fromIndex(0);
    const current_result = ir.ValueId.fromIndex(1);
    const original_result = ir.ValueId.fromIndex(2);
    const current_parameter = ir.ValueId.fromIndex(3);
    const current_get = ir.InstructionId.fromIndex(0);
    const current_write = ir.InstructionId.fromIndex(1);
    const original_get = ir.InstructionId.fromIndex(2);
    const original_write = ir.InstructionId.fromIndex(3);
    const place = ir.PlaceId.fromIndex(0);
    const block_ids = [_]ir.BlockId{
        entry,
        owner_source,
        incoming_source,
        current,
        terminal,
        owner_stop,
        incoming_stop,
        original,
    };
    const function_parameters = [_]ir.ValueId{condition};
    var current_parameters = [_]ir.ValueId{current_parameter};
    const current_parameter_slice: []const ir.ValueId = if (witness == .parameterized_suffix)
        current_parameters[0..]
    else
        &.{};
    const current_return = [_]ir.ValueId{current_result};
    const wrong_return = [_]ir.ValueId{original_result};
    const terminal_return: []const ir.ValueId = if (witness == .wrong_return_origin)
        wrong_return[0..]
    else
        current_return[0..];
    const suffix_effects: ir.EffectSummary = if (witness == .pure_suffix)
        .pure
    else
        .table_constructor;
    const suffix_write_effects: ir.EffectSummary = if (witness == .pure_suffix)
        .pure
    else
        .place_write;
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = owner_source },
            .else_edge = .{ .target = incoming_source },
        } } },
        .{ .id = owner_source, .function = function_id, .terminator = .{ .jump = .{ .target = owner_stop } } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{ .target = current } } },
        .{ .id = current, .function = function_id, .parameters = current_parameter_slice, .instructions = &.{ current_get, current_write }, .terminator = .{ .return_values = terminal_return } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = incoming_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original, .function = function_id, .instructions = &.{ original_get, original_write }, .terminator = .{ .return_values = wrong_return[0..] } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = function_parameters[0..],
        .local_places = &.{place},
        .blocks = block_ids[0..],
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = current_result, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = current_get, .index = 0 } } },
        .{ .id = original_result, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = original_get, .index = 0 } } },
        .{ .id = current_parameter, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = current, .index = 0 } } },
    };
    const places = [_]ir.Place{.{
        .id = place,
        .function = function_id,
        .type = .dynamic,
        .origin = .{ .local = 0 },
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = current_get, .block = current, .operation = .{ .make_table = {} }, .results = &.{current_result}, .effects = suffix_effects },
        .{ .id = current_write, .block = current, .operation = .{ .place_write = .{ .place = place, .value = current_result } }, .results = &.{}, .effects = suffix_write_effects },
        .{ .id = original_get, .block = original, .operation = .{ .make_table = {} }, .results = &.{original_result}, .effects = suffix_effects },
        .{ .id = original_write, .block = original, .operation = .{ .place_write = .{ .place = place, .value = original_result } }, .results = &.{}, .effects = suffix_write_effects },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = incoming_source,
        .kind = .jump,
        .from = .{ .target = original },
        .to = .{ .target = current },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const edge_rewrites: []const ir.CfgEdgeRewrite = if (witness == .missing_bridge)
        &.{}
    else
        rewrites[0..];
    const functions = [_]ir.Function{function};
    const program: ir.Program = .{
        .program_id = "terminal-continuation-replay-witness",
        .entry_function = function_id,
        .functions = functions[0..],
        .blocks = blocks[0..],
        .instructions = instructions[0..],
        .values = values[0..],
        .places = places[0..],
        .edge_rewrites = edge_rewrites,
    };
    var analysis = try cfg.Analysis.init(allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(allocator, &analysis);
    defer allocator.free(loop_headers);

    var visited = [_]bool{ false, false, false, true, false, false, false, false };
    const owner_context_stop = if (witness == .matching_stop) incoming_stop else owner_stop;
    var contexts = [_]?Builder.VisitContext{ null, null, null, .{
        .start = owner_source,
        .stop = owner_context_stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &.{},
    }, null, null, null, null };
    var builder: Builder = .{
        .allocator = allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const witness_reference = ir.CfgEdgeRef{ .source = incoming_source, .kind = .jump, .target = current };
    const replay = try builder.authenticatedEffectfulTerminalContinuationReplay(
        current,
        incoming_source,
        incoming_stop,
        null,
        null,
        &.{},
        witness_reference,
        .{ .block = incoming_source },
    );
    if (replay) |value| {
        allocator.free(value.nodes);
        return true;
    }
    return false;
}

test "effectful terminal continuation replay requires complete authenticated witness" {
    try std.testing.expect(try terminalContinuationReplayWitness(.valid));
    try std.testing.expect(!(try terminalContinuationReplayWitness(.missing_bridge)));
    try std.testing.expect(!(try terminalContinuationReplayWitness(.pure_suffix)));
    try std.testing.expect(!(try terminalContinuationReplayWitness(.wrong_return_origin)));
    try std.testing.expect(!(try terminalContinuationReplayWitness(.matching_stop)));
    try std.testing.expect(!(try terminalContinuationReplayWitness(.parameterized_suffix)));
}

test "mixed-lineage entry collision keeps only the supplied edge" {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const incoming_source = ir.BlockId.fromIndex(1);
    const cloned_source = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const owner_stop = ir.BlockId.fromIndex(4);
    const incoming_stop = ir.BlockId.fromIndex(5);
    const original = ir.BlockId.fromIndex(6);
    const condition = ir.ValueId.fromIndex(0);

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = incoming_source },
            .else_edge = .{ .target = cloned_source },
        } } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = cloned_source, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = incoming_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, incoming_source, cloned_source, target, owner_stop, incoming_stop, original },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = incoming_source,
        .kind = .jump,
        .from = .{ .target = original },
        .to = .{ .target = target },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const program = ir.Program{
        .program_id = "mixed-lineage-entry-collision",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = cfg.Analysis.init(allocator, &program, function) catch |err| switch (err) {
        error.InvalidCfg => return error.TestUnexpectedResult,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(allocator, &analysis);
    defer allocator.free(loop_headers);
    const entry_reference: ir.CfgEdgeRef = .{
        .source = incoming_source,
        .kind = .jump,
        .target = target,
    };

    var visited = [_]bool{ false, false, false, true, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, .{
        .start = target,
        .stop = owner_stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &.{},
    }, null, null, null };
    var collision: ?Collision = null;
    defer if (collision) |*value| value.deinit(allocator);
    var builder: Builder = .{
        .allocator = allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
        .collision = &collision,
    };
    try std.testing.expect(try builder.hasAuthenticatedContinuationBridge(entry_reference));
    try std.testing.expectError(
        error.UnsupportedShape,
        builder.buildRegionImplWithEntryArgumentsAndEdge(
            target,
            incoming_stop,
            null,
            null,
            null,
            null,
            false,
            null,
            &.{},
            entry_reference,
        ),
    );
    const recorded = collision orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(target, recorded.block);
    try std.testing.expectEqual(entry_reference.source, recorded.incoming.?.source);
    try std.testing.expectEqual(entry_reference.kind, recorded.incoming.?.kind);
    try std.testing.expectEqual(entry_reference.target, recorded.incoming.?.target);
    try std.testing.expectEqual(@as(usize, 0), recorded.incoming_group.len);

    var unauthenticated_visited = [_]bool{ false, false, false, true, false, false, false };
    var unauthenticated_contexts = contexts;
    var unauthenticated_collision: ?Collision = null;
    defer if (unauthenticated_collision) |*value| value.deinit(allocator);
    var unauthenticated_builder: Builder = .{
        .allocator = allocator,
        .analysis = &analysis,
        .visited = &unauthenticated_visited,
        .visited_contexts = &unauthenticated_contexts,
        .loop_headers = loop_headers,
        .collision = &unauthenticated_collision,
    };
    const unauthenticated_reference: ir.CfgEdgeRef = .{
        .source = cloned_source,
        .kind = .jump,
        .target = target,
    };
    try std.testing.expect(!try unauthenticated_builder.hasAuthenticatedContinuationBridge(unauthenticated_reference));
    try std.testing.expectError(
        error.UnsupportedShape,
        unauthenticated_builder.buildRegionImplWithEntryArgumentsAndEdge(
            target,
            incoming_stop,
            null,
            null,
            null,
            null,
            false,
            null,
            &.{},
            unauthenticated_reference,
        ),
    );
    const unauthenticated_recorded = unauthenticated_collision orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(unauthenticated_reference.source, unauthenticated_recorded.incoming.?.source);
    try std.testing.expectEqual(unauthenticated_reference.kind, unauthenticated_recorded.incoming.?.kind);
    try std.testing.expectEqual(unauthenticated_reference.target, unauthenticated_recorded.incoming.?.target);
    try std.testing.expectEqual(@as(usize, 0), unauthenticated_recorded.incoming_group.len);

    var no_edge_visited = [_]bool{ false, false, false, true, false, false, false };
    var no_edge_contexts = contexts;
    var no_edge_collision: ?Collision = null;
    defer if (no_edge_collision) |*value| value.deinit(allocator);
    var no_edge_builder: Builder = .{
        .allocator = allocator,
        .analysis = &analysis,
        .visited = &no_edge_visited,
        .visited_contexts = &no_edge_contexts,
        .loop_headers = loop_headers,
        .collision = &no_edge_collision,
    };
    try std.testing.expectError(
        error.UnsupportedShape,
        no_edge_builder.buildRegionImplWithEntryArgumentsAndEdge(
            target,
            incoming_stop,
            null,
            null,
            null,
            null,
            false,
            null,
            &.{},
            null,
        ),
    );
    const no_edge_recorded = no_edge_collision orelse return error.TestUnexpectedResult;
    try std.testing.expect(no_edge_recorded.incoming == null);
    try std.testing.expectEqual(@as(usize, 0), no_edge_recorded.incoming_group.len);
}

test "transparent empty continuation reuses a different stop" {
    const function_id = ir.FunctionId.fromIndex(0);
    const start = ir.BlockId.fromIndex(0);
    const first_stop = ir.BlockId.fromIndex(1);
    const second_stop = ir.BlockId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = start, .function = function_id, .terminator = .{ .jump = .{ .target = first_stop } } },
        .{ .id = first_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = second_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ start, first_stop, second_stop },
        .entry_block = start,
    };
    const program: ir.Program = .{
        .program_id = "transparent-empty-continuation",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ true, false, false };
    var contexts = [_]?Builder.VisitContext{ .{
        .start = start,
        .stop = first_stop,
        .loop_exit = null,
        .continue_target = null,
    }, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const reused = try builder.buildRegionImpl(start, second_stop, null, null, null, null, false, null);
    defer destroyRegion(std.testing.allocator, reused);
    try std.testing.expectEqual(@as(usize, 0), reused.nodes.len);
    try std.testing.expect(reused.escape_projection != null);
    try std.testing.expectEqual(start, reused.escape_projection.?.target);

    var loop_visited = [_]bool{ true, false, false };
    var loop_contexts = contexts;
    var loop_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &loop_visited,
        .visited_contexts = &loop_contexts,
        .loop_headers = loop_headers,
    };
    const loop_reused = try loop_builder.buildRegionImpl(
        start,
        second_stop,
        null,
        second_stop,
        null,
        null,
        false,
        null,
    );
    defer destroyRegion(std.testing.allocator, loop_reused);
    try std.testing.expectEqual(@as(usize, 0), loop_reused.nodes.len);
    try std.testing.expect(loop_reused.escape_projection != null);
    try std.testing.expectEqual(start, loop_reused.escape_projection.?.target);
    var wrong_stop_context = loop_contexts[0].?;
    wrong_stop_context.stop = second_stop;
    try std.testing.expect(!loop_builder.transparentEmptyOwnedStopContextMatches(
        start,
        start,
        second_stop,
        wrong_stop_context,
        true,
    ));

    var branch_blocks = blocks;
    branch_blocks[start.index()].terminator = .{ .branch = .{
        .condition = ir.ValueId.fromIndex(0),
        .then_edge = .{ .target = first_stop },
        .else_edge = .{ .target = second_stop },
    } };
    const branch_values = [_]ir.Value{.{
        .id = ir.ValueId.fromIndex(0),
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    var branch_program = program;
    branch_program.blocks = &branch_blocks;
    branch_program.values = &branch_values;
    var branch_analysis = try cfg.Analysis.init(std.testing.allocator, &branch_program, function);
    defer branch_analysis.deinit();
    const branch_loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &branch_analysis);
    defer std.testing.allocator.free(branch_loop_headers);
    var branch_visited = [_]bool{ true, false, false };
    var branch_contexts = [_]?Builder.VisitContext{ .{
        .start = start,
        .stop = first_stop,
        .loop_exit = null,
        .continue_target = null,
    }, null, null };
    var rejected_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &branch_analysis,
        .visited = &branch_visited,
        .visited_contexts = &branch_contexts,
        .loop_headers = branch_loop_headers,
    };
    try std.testing.expectError(
        error.UnsupportedShape,
        rejected_builder.buildRegionImpl(start, second_stop, null, null, null, null, false, null),
    );
}

test "transparent empty owned stop crosses loop context with canonical tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const start = ir.BlockId.fromIndex(1);
    const owner_stop = ir.BlockId.fromIndex(2);
    const current_stop = ir.BlockId.fromIndex(3);
    const loop_exit = ir.BlockId.fromIndex(4);
    const continue_target = ir.BlockId.fromIndex(5);
    const incoming_value = ir.ValueId.fromIndex(0);
    const owner_value = ir.ValueId.fromIndex(1);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = start } } },
        .{ .id = start, .function = function_id, .terminator = .{ .jump = .{
            .target = owner_stop,
            .arguments = &.{incoming_value},
        } } },
        .{ .id = owner_stop, .function = function_id, .parameters = &.{owner_value}, .terminator = .{ .return_values = &.{owner_value} } },
        .{ .id = current_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = loop_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = continue_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{incoming_value},
        .blocks = &.{ entry, start, owner_stop, current_stop, loop_exit, continue_target },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = incoming_value, .function = function_id, .type = .number, .origin = .{ .parameter = 0 } },
        .{ .id = owner_value, .function = function_id, .type = .number, .origin = .{ .block_parameter = .{ .block = owner_stop, .index = 0 } } },
    };
    const program: ir.Program = .{
        .program_id = "transparent-empty-owned-stop-loop-context",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, true, false, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, .{
        .start = start,
        .stop = owner_stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &.{},
    }, null, null, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const reused = try builder.buildRegionImplWithEntryArguments(
        start,
        current_stop,
        null,
        loop_exit,
        null,
        null,
        false,
        continue_target,
        null,
    );
    defer destroyRegion(std.testing.allocator, reused);
    try std.testing.expectEqual(@as(usize, 0), reused.nodes.len);
    try std.testing.expect(reused.escape_projection != null);
    try std.testing.expectEqual(start, reused.escape_projection.?.target);

    var post_prefix_visited = [_]bool{ false, true, false, false, false, false };
    var post_prefix_contexts = contexts;
    var post_prefix_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &post_prefix_visited,
        .visited_contexts = &post_prefix_contexts,
        .loop_headers = loop_headers,
    };
    const post_prefix = try post_prefix_builder.buildRegionImplWithEntryArguments(
        entry,
        current_stop,
        null,
        loop_exit,
        null,
        null,
        false,
        continue_target,
        null,
    );
    defer destroyRegion(std.testing.allocator, post_prefix);
    try std.testing.expectEqual(@as(usize, 1), post_prefix.nodes.len);
    try std.testing.expectEqual(entry, post_prefix.nodes[0].blockId());
    try std.testing.expect(post_prefix.escape_projection != null);
    try std.testing.expectEqual(start, post_prefix.escape_projection.?.target);
}

test "transparent empty visited continuation reuses an owned predecessor edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const start = ir.BlockId.fromIndex(1);
    const first_stop = ir.BlockId.fromIndex(2);
    const second_stop = ir.BlockId.fromIndex(3);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = start } } },
        .{ .id = start, .function = function_id, .terminator = .{ .jump = .{ .target = first_stop } } },
        .{ .id = first_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = second_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, start, first_stop, second_stop },
        .entry_block = entry,
    };
    const program: ir.Program = .{
        .program_id = "transparent-empty-visited-continuation",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, true, false, false };
    var contexts = [_]?Builder.VisitContext{ null, .{
        .start = start,
        .stop = first_stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &.{},
    }, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const reused = try builder.buildRegionImpl(entry, second_stop, null, null, null, null, false, null);
    defer destroyRegion(std.testing.allocator, reused);
    try std.testing.expectEqual(@as(usize, 1), reused.nodes.len);
    try std.testing.expectEqual(entry, reused.nodes[0].blockId());
    try std.testing.expectEqual(start, reused.escape_projection.?.target);

    var branch_blocks = blocks;
    branch_blocks[start.index()].terminator = .{ .branch = .{
        .condition = ir.ValueId.fromIndex(0),
        .then_edge = .{ .target = first_stop },
        .else_edge = .{ .target = second_stop },
    } };
    const branch_values = [_]ir.Value{.{
        .id = ir.ValueId.fromIndex(0),
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    var branch_program = program;
    branch_program.blocks = &branch_blocks;
    branch_program.values = &branch_values;
    var branch_analysis = try cfg.Analysis.init(std.testing.allocator, &branch_program, function);
    defer branch_analysis.deinit();
    const branch_loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &branch_analysis);
    defer std.testing.allocator.free(branch_loop_headers);
    var branch_visited = [_]bool{ false, true, false, false };
    var branch_contexts = [_]?Builder.VisitContext{ null, .{
        .start = start,
        .stop = first_stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &.{},
    }, null, null };
    var rejected_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &branch_analysis,
        .visited = &branch_visited,
        .visited_contexts = &branch_contexts,
        .loop_headers = branch_loop_headers,
    };
    try std.testing.expectError(
        error.UnsupportedShape,
        rejected_builder.buildRegionImpl(entry, second_stop, null, null, null, null, false, null),
    );
}

test "visited empty return terminal projects through an owned prefix" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const prefix = ir.BlockId.fromIndex(1);
    const terminal = ir.BlockId.fromIndex(2);
    const owner_stop = ir.BlockId.fromIndex(3);
    const incoming_stop = ir.BlockId.fromIndex(4);
    const result = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = prefix } } },
        .{ .id = prefix, .function = function_id, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = incoming_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{result},
        .blocks = &.{ entry, prefix, terminal, owner_stop, incoming_stop },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = result,
        .function = function_id,
        .type = .dynamic,
        .origin = .{ .parameter = 0 },
    }};
    const program: ir.Program = .{
        .program_id = "visited-empty-return-terminal",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, false, true, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, .{
        .start = prefix,
        .stop = owner_stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &.{},
    }, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const projected = try builder.buildRegionImpl(entry, incoming_stop, null, null, null, null, false, null);
    defer destroyRegion(std.testing.allocator, projected);
    try std.testing.expectEqual(@as(usize, 2), projected.nodes.len);
    try std.testing.expectEqual(entry, projected.nodes[0].blockId());
    try std.testing.expectEqual(prefix, projected.nodes[1].blockId());
    try std.testing.expect(projected.terminal_projection != null);
    try std.testing.expectEqual(terminal, projected.terminal_projection.?.terminal);
    try std.testing.expect(projected.terminal_projection.?.edge != null);
    try std.testing.expectEqual(terminal, projected.terminal_projection.?.edge.?.target);

    var nonempty_blocks = blocks;
    nonempty_blocks[terminal.index()].terminator = .{ .return_values = &.{result} };
    var nonempty_program = program;
    nonempty_program.program_id = "visited-valued-return-terminal";
    nonempty_program.blocks = &nonempty_blocks;
    var nonempty_analysis = try cfg.Analysis.init(std.testing.allocator, &nonempty_program, function);
    defer nonempty_analysis.deinit();
    const nonempty_loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &nonempty_analysis);
    defer std.testing.allocator.free(nonempty_loop_headers);
    var nonempty_visited = [_]bool{ false, false, true, false, false };
    var nonempty_contexts = contexts;
    var nonempty_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &nonempty_analysis,
        .visited = &nonempty_visited,
        .visited_contexts = &nonempty_contexts,
        .loop_headers = nonempty_loop_headers,
    };
    try std.testing.expectError(
        error.UnsupportedShape,
        nonempty_builder.buildRegionImpl(entry, incoming_stop, null, null, null, null, false, null),
    );
}

test "empty loop continuation reuses a different stop context" {
    const function_id = ir.FunctionId.fromIndex(0);
    const start = ir.BlockId.fromIndex(0);
    const continue_block = ir.BlockId.fromIndex(1);
    const loop_exit = ir.BlockId.fromIndex(2);
    const first_stop = ir.BlockId.fromIndex(3);
    const second_stop = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = start, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = continue_block },
            .else_edge = .{ .target = loop_exit },
        } } },
        .{ .id = continue_block, .function = function_id, .terminator = .{ .jump = .{ .target = start } } },
        .{ .id = loop_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = first_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = second_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ start, continue_block, loop_exit, first_stop, second_stop },
        .entry_block = start,
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program: ir.Program = .{
        .program_id = "empty-loop-continuation-context",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ true, false, false, false, false };
    var contexts = [_]?Builder.VisitContext{ .{
        .start = start,
        .stop = first_stop,
        .loop_exit = loop_exit,
        .continue_target = continue_block,
        .parameter_arguments = &.{},
    }, null, null, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const reused = try builder.buildRegionImpl(
        start,
        second_stop,
        null,
        loop_exit,
        null,
        null,
        false,
        continue_block,
    );
    defer destroyRegion(std.testing.allocator, reused);
    try std.testing.expectEqual(@as(usize, 0), reused.nodes.len);
    try std.testing.expect(reused.escape_projection != null);
    try std.testing.expectEqual(start, reused.escape_projection.?.target);

    contexts[0].?.parameter_arguments = &.{condition};
    var rejected_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    try std.testing.expectError(
        error.UnsupportedShape,
        rejected_builder.buildRegionImpl(
            start,
            second_stop,
            null,
            loop_exit,
            null,
            null,
            false,
            continue_block,
        ),
    );
}

test "parameterized continuation reuse requires the same incoming tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const start = ir.BlockId.fromIndex(0);
    const stop = ir.BlockId.fromIndex(1);
    const parameter = ir.ValueId.fromIndex(0);
    const first_argument = ir.ValueId.fromIndex(1);
    const second_argument = ir.ValueId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{
            .id = start,
            .function = function_id,
            .parameters = &.{parameter},
            .terminator = .{ .jump = .{ .target = stop } },
        },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ start, stop },
        .entry_block = start,
    };
    const values = [_]ir.Value{
        .{ .id = parameter, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = first_argument, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = second_argument, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } },
    };
    const program: ir.Program = .{
        .program_id = "parameterized-continuation-projection",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ true, false };
    var contexts = [_]?Builder.VisitContext{ .{
        .start = start,
        .stop = stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &.{first_argument},
    }, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };

    const reused = try builder.buildRegionImplWithEntryArguments(
        start,
        stop,
        null,
        null,
        null,
        null,
        false,
        null,
        &.{first_argument},
    );
    defer destroyRegion(std.testing.allocator, reused);
    try std.testing.expectEqual(@as(usize, 0), reused.nodes.len);
    try std.testing.expect(reused.escape_projection != null);
    try std.testing.expectEqual(start, reused.escape_projection.?.target);

    var rejected_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    try std.testing.expectError(
        error.UnsupportedShape,
        rejected_builder.buildRegionImplWithEntryArguments(
            start,
            stop,
            null,
            null,
            null,
            null,
            false,
            null,
            &.{second_argument},
        ),
    );
}

test "numeric iteration reentry accepts an authenticated forwarding prefix" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner_start = ir.BlockId.fromIndex(1);
    const owner_stop = ir.BlockId.fromIndex(2);
    const prefix = ir.BlockId.fromIndex(3);
    const header = ir.BlockId.fromIndex(4);
    const body = ir.BlockId.fromIndex(5);
    const loop_exit = ir.BlockId.fromIndex(6);
    const continue_target = ir.BlockId.fromIndex(7);
    const incoming_stop = ir.BlockId.fromIndex(8);
    const header_control = ir.ValueId.fromIndex(0);
    const header_limit = ir.ValueId.fromIndex(1);
    const header_step = ir.ValueId.fromIndex(2);
    const header_initial = ir.ValueId.fromIndex(3);
    const has_value = ir.ValueId.fromIndex(4);
    const next_limit = ir.ValueId.fromIndex(5);
    const next_step = ir.ValueId.fromIndex(6);
    const next_control = ir.ValueId.fromIndex(7);
    const entry_condition = ir.ValueId.fromIndex(8);
    const wrong_argument = ir.ValueId.fromIndex(9);
    const transition_id = ir.InstructionId.fromIndex(0);
    const tuple = [_]ir.ValueId{ header_control, header_limit, header_step, header_initial };
    var wrong_tuple = tuple;
    wrong_tuple[0] = wrong_argument;

    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = entry_condition,
            .then_edge = .{ .target = owner_start },
            .else_edge = .{ .target = prefix },
        } } },
        .{ .id = owner_start, .function = function_id, .terminator = .{ .jump = .{ .target = owner_stop } } },
        .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = prefix, .function = function_id, .terminator = .{ .jump = .{
            .target = header,
            .arguments = &tuple,
        } } },
        .{ .id = header, .function = function_id, .parameters = &.{
            header_control,
            header_limit,
            header_step,
            header_initial,
        }, .instructions = &.{transition_id}, .terminator = .{ .branch = .{
            .condition = has_value,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = loop_exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = incoming_stop } } },
        .{ .id = loop_exit, .function = function_id, .terminator = .{ .jump = .{ .target = continue_target } } },
        .{ .id = continue_target, .function = function_id, .terminator = .{ .jump = .{ .target = incoming_stop } } },
        .{ .id = incoming_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{entry_condition},
        .blocks = &.{ entry, owner_start, owner_stop, prefix, header, body, loop_exit, continue_target, incoming_stop },
        .entry_block = entry,
    };
    const functions = [_]ir.Function{function};
    const values = [_]ir.Value{
        .{ .id = header_control, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
        .{ .id = header_limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 1 } } },
        .{ .id = header_step, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 2 } } },
        .{ .id = header_initial, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 3 } } },
        .{ .id = has_value, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 0 } } },
        .{ .id = next_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 1 } } },
        .{ .id = next_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 3 } } },
        .{ .id = entry_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = wrong_argument, .function = function_id, .origin = .{ .parameter = 1 } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = transition_id,
        .block = header,
        .operation = .{ .numeric_for_next = .{
            .control = header_control,
            .limit = header_limit,
            .step = header_step,
            .initial = header_initial,
        } },
        .results = &.{ has_value, next_limit, next_step, next_control },
        .effects = .numeric_for_next,
    }};
    const program: ir.Program = .{
        .program_id = "numeric-forwarding-prefix-reentry",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, false, false, false, true, false, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, null, .{
        .start = owner_start,
        .stop = owner_stop,
        .loop_exit = loop_exit,
        .continue_target = continue_target,
        .parameter_arguments = &tuple,
    }, null, null, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const reused = try builder.buildRegionImplWithEntryArguments(
        prefix,
        incoming_stop,
        null,
        loop_exit,
        null,
        null,
        false,
        continue_target,
        &tuple,
    );
    defer destroyRegion(std.testing.allocator, reused);
    try std.testing.expectEqual(@as(usize, 1), reused.nodes.len);
    try std.testing.expectEqual(prefix, reused.nodes[0].blockId());
    try std.testing.expect(reused.escape_projection != null);
    try std.testing.expectEqual(header, reused.escape_projection.?.target);

    blocks[prefix.index()].terminator = .{ .jump = .{
        .target = header,
        .arguments = &wrong_tuple,
    } };
    var rejected_visited = [_]bool{ false, false, false, false, true, false, false, false, false };
    var rejected_contexts = [_]?Builder.VisitContext{ null, null, null, null, .{
        .start = owner_start,
        .stop = owner_stop,
        .loop_exit = loop_exit,
        .continue_target = continue_target,
        .parameter_arguments = &tuple,
    }, null, null, null, null };
    var rejected_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &rejected_visited,
        .visited_contexts = &rejected_contexts,
        .loop_headers = loop_headers,
    };
    try std.testing.expectError(
        error.UnsupportedShape,
        rejected_builder.buildRegionImplWithEntryArguments(
            prefix,
            incoming_stop,
            null,
            loop_exit,
            null,
            null,
            false,
            continue_target,
            &wrong_tuple,
        ),
    );
}

test "nested loop boundary owns an outside terminal path" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const prefix = ir.BlockId.fromIndex(3);
    const branch = ir.BlockId.fromIndex(4);
    const reentry = ir.BlockId.fromIndex(5);
    const continue_path = ir.BlockId.fromIndex(6);
    const terminal_path = ir.BlockId.fromIndex(7);
    const terminal_relay = ir.BlockId.fromIndex(8);
    const exit = ir.BlockId.fromIndex(9);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = prefix } } },
        .{ .id = prefix, .function = function_id, .terminator = .{ .jump = .{ .target = branch } } },
        .{ .id = branch, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = reentry },
            .else_edge = .{ .target = terminal_path },
        } } },
        .{ .id = reentry, .function = function_id, .terminator = .{ .jump = .{ .target = continue_path } } },
        .{ .id = continue_path, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = terminal_path, .function = function_id, .terminator = .{ .jump = .{ .target = terminal_relay } } },
        .{ .id = terminal_relay, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, header, body, prefix, branch, reentry, continue_path, terminal_path, terminal_relay, exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program: ir.Program = .{
        .program_id = "nested-loop-outside-terminal",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expect(plan.root.nodes.len != 0);
}

test "terminal-only outside suffix is admitted without weakening boundaries" {
    const function_id = ir.FunctionId.fromIndex(0);
    const start = ir.BlockId.fromIndex(0);
    const suffix = ir.BlockId.fromIndex(1);
    const relay = ir.BlockId.fromIndex(2);
    const terminal = ir.BlockId.fromIndex(3);
    var blocks = [_]ir.Block{
        .{ .id = start, .function = function_id, .terminator = .{ .jump = .{ .target = suffix } } },
        .{ .id = suffix, .function = function_id, .terminator = .{ .jump = .{ .target = relay } } },
        .{ .id = relay, .function = function_id, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ start, suffix, relay, terminal },
        .entry_block = start,
    };
    const functions = [_]ir.Function{function};
    const program: ir.Program = .{
        .program_id = "terminal-only-outside-suffix",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    const membership = [_]bool{ true, false, false, false };

    {
        var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
        defer analysis.deinit();
        const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
        defer std.testing.allocator.free(loop_headers);
        var visited = [_]bool{ false, false, false, false };
        var contexts = [_]?Builder.VisitContext{ null, null, null, null };
        var builder: Builder = .{
            .allocator = std.testing.allocator,
            .analysis = &analysis,
            .visited = &visited,
            .visited_contexts = &contexts,
            .loop_headers = loop_headers,
        };
        const region = try builder.buildRegionImpl(start, null, &membership, null, null, null, false, null);
        defer destroyRegion(std.testing.allocator, region);
        try std.testing.expectEqual(@as(usize, 4), region.nodes.len);
        try std.testing.expectEqual(terminal, region.nodes[3].blockId());
    }

    blocks[relay.index()].terminator = .{ .jump = .{ .target = start } };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);
    var visited = [_]bool{ false, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    try std.testing.expect(!try builder.outsidePathMustTerminate(&membership, suffix));
}

test "authenticated outside suffix may reuse an owned shared terminal" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const direct = ir.BlockId.fromIndex(1);
    const header = ir.BlockId.fromIndex(2);
    const body = ir.BlockId.fromIndex(3);
    const latch = ir.BlockId.fromIndex(4);
    const forwarding = ir.BlockId.fromIndex(5);
    const terminal_path = ir.BlockId.fromIndex(6);
    const terminal = ir.BlockId.fromIndex(7);
    const exit = ir.BlockId.fromIndex(8);
    const condition = ir.ValueId.fromIndex(0);
    const body_condition = ir.ValueId.fromIndex(1);
    const exit_condition = ir.ValueId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = direct },
            .else_edge = .{ .target = header },
        } } },
        .{ .id = direct, .function = function_id, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = exit_condition,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = body_condition,
            .then_edge = .{ .target = latch },
            .else_edge = .{ .target = forwarding },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = forwarding, .function = function_id, .terminator = .{ .jump = .{ .target = terminal_path } } },
        .{ .id = terminal_path, .function = function_id, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ condition, body_condition, exit_condition },
        .blocks = &.{ entry, direct, header, body, latch, forwarding, terminal_path, terminal, exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = body_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = exit_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 2 } },
    };
    const program: ir.Program = .{
        .program_id = "owned-shared-terminal-outside-suffix",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expect(plan.root.nodes.len != 0);
}

test "nonterminal loop exit projects before an outside cyclic suffix" {
    const function_id = ir.FunctionId.fromIndex(0);
    const start = ir.BlockId.fromIndex(0);
    const loop_exit = ir.BlockId.fromIndex(1);
    const cycle = ir.BlockId.fromIndex(2);
    const stop = ir.BlockId.fromIndex(3);
    const blocks = [_]ir.Block{
        .{ .id = start, .function = function_id, .terminator = .{ .jump = .{ .target = loop_exit } } },
        .{ .id = loop_exit, .function = function_id, .terminator = .{ .jump = .{ .target = cycle } } },
        .{ .id = cycle, .function = function_id, .terminator = .{ .jump = .{ .target = loop_exit } } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ start, loop_exit, cycle, stop },
        .entry_block = start,
    };
    const program: ir.Program = .{
        .program_id = "nonterminal-loop-exit-projection",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    const membership = [_]bool{ true, false, false, false };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);
    var visited = [_]bool{ false, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };

    const region = try builder.buildRegionImpl(
        start,
        stop,
        &membership,
        loop_exit,
        null,
        null,
        false,
        null,
    );
    defer destroyRegion(std.testing.allocator, region);
    try std.testing.expectEqual(@as(usize, 1), region.nodes.len);
    try std.testing.expect(region.escape_projection != null);
    try std.testing.expectEqual(loop_exit, region.escape_projection.?.target);
    try std.testing.expect(region.escape_projection.?.edge != null);
}

test "stable node split bridge reuses a different owner context" {
    const function_id = ir.FunctionId.fromIndex(0);
    const prefix = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const stop = ir.BlockId.fromIndex(2);
    const original = ir.BlockId.fromIndex(3);
    var blocks = [_]ir.Block{
        .{ .id = prefix, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ prefix, target, stop, original },
        .entry_block = prefix,
    };
    var rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = prefix,
        .kind = .jump,
        .from = .{ .target = original },
        .to = .{ .target = target },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const program: ir.Program = .{
        .program_id = "stable-bridge-continuation",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, true, false, false };
    var contexts = [_]?Builder.VisitContext{ null, .{
        .start = target,
        .stop = stop,
        .loop_exit = null,
        .continue_target = null,
    }, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const reused = try builder.buildRegionImpl(prefix, stop, null, null, null, null, false, null);
    defer destroyRegion(std.testing.allocator, reused);
    try std.testing.expectEqual(@as(usize, 1), reused.nodes.len);
    try std.testing.expectEqual(prefix, reused.nodes[0].blockId());
    try std.testing.expect(reused.escape_projection != null);
    try std.testing.expectEqual(target, reused.escape_projection.?.target);

    var membership_visited = [_]bool{ false, true, false, false };
    var membership_contexts = contexts;
    var membership_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &membership_visited,
        .visited_contexts = &membership_contexts,
        .loop_headers = loop_headers,
    };
    const membership = [_]bool{ true, false, false, false };
    const outside_projection = try membership_builder.buildRegionImpl(
        prefix,
        stop,
        &membership,
        null,
        null,
        null,
        false,
        null,
    );
    defer destroyRegion(std.testing.allocator, outside_projection);
    try std.testing.expectEqual(@as(usize, 1), outside_projection.nodes.len);
    try std.testing.expect(outside_projection.escape_projection != null);
    try std.testing.expectEqual(target, outside_projection.escape_projection.?.target);

    contexts[1].?.start = target;
    rewrites[0].rule = .forwarding_jump;
    visited[0] = false;
    var rejected_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    try std.testing.expectError(
        error.UnsupportedShape,
        rejected_builder.buildRegionImpl(prefix, stop, null, null, null, null, false, null),
    );
}

test "authenticated empty outside clone projects to loop exit" {
    const function_id = ir.FunctionId.fromIndex(0);
    const prefix = ir.BlockId.fromIndex(0);
    const clone = ir.BlockId.fromIndex(1);
    const loop_exit = ir.BlockId.fromIndex(2);
    const original = ir.BlockId.fromIndex(3);
    const blocks = [_]ir.Block{
        .{ .id = prefix, .function = function_id, .terminator = .{ .jump = .{ .target = clone } } },
        .{ .id = clone, .function = function_id, .terminator = .{ .jump = .{ .target = loop_exit } } },
        .{ .id = loop_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original, .function = function_id, .terminator = .{ .jump = .{ .target = loop_exit } } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ prefix, clone, loop_exit, original },
        .entry_block = prefix,
    };
    var rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = prefix,
        .kind = .jump,
        .from = .{ .target = original },
        .to = .{ .target = clone },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    var program = ir.Program{
        .program_id = "authenticated-empty-outside-clone",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);
    var visited = [_]bool{ false, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, null };
    const membership = [_]bool{ false, false, false, false };
    const entry_reference: ir.CfgEdgeRef = .{ .source = prefix, .kind = .jump, .target = clone };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const region = try builder.buildRegionImplWithEntryArgumentsAndEdge(
        clone,
        null,
        &membership,
        loop_exit,
        null,
        null,
        false,
        null,
        null,
        entry_reference,
    );
    defer destroyRegion(std.testing.allocator, region);
    try std.testing.expectEqual(@as(usize, 1), region.nodes.len);
    try std.testing.expectEqual(clone, region.nodes[0].blockId());
    try std.testing.expect(region.escape_projection != null);
    try std.testing.expectEqual(loop_exit, region.escape_projection.?.target);
    try std.testing.expect(region.escape_projection.?.edge != null);

    rewrites[0].rule = .forwarding_jump;
    program.edge_rewrites = &rewrites;
    var rejected_analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer rejected_analysis.deinit();
    var rejected_visited = [_]bool{ false, false, false, false };
    var rejected_contexts = [_]?Builder.VisitContext{ null, null, null, null };
    var rejected_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &rejected_analysis,
        .visited = &rejected_visited,
        .visited_contexts = &rejected_contexts,
        .loop_headers = loop_headers,
    };
    try std.testing.expectError(
        error.UnsupportedShape,
        rejected_builder.buildRegionImplWithEntryArgumentsAndEdge(
            clone,
            null,
            &membership,
            loop_exit,
            null,
            null,
            false,
            null,
            null,
            entry_reference,
        ),
    );
}

test "empty authenticated continuation reuses its canonical entry edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const prefix = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const stop = ir.BlockId.fromIndex(2);
    const original = ir.BlockId.fromIndex(3);
    const blocks = [_]ir.Block{
        .{ .id = prefix, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ prefix, target, stop, original },
        .entry_block = prefix,
    };
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = prefix,
        .kind = .jump,
        .from = .{ .target = original },
        .to = .{ .target = target },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const program: ir.Program = .{
        .program_id = "empty-authenticated-continuation-entry",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, true, false, false };
    var contexts = [_]?Builder.VisitContext{ null, .{
        .start = original,
        .stop = stop,
        .loop_exit = null,
        .continue_target = null,
    }, null, null };
    const entry_reference: ir.CfgEdgeRef = .{ .source = prefix, .kind = .jump, .target = target };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const reused = try builder.buildRegionImplWithEntryArgumentsAndEdge(
        target,
        stop,
        null,
        null,
        null,
        null,
        false,
        null,
        null,
        entry_reference,
    );
    defer destroyRegion(std.testing.allocator, reused);
    try std.testing.expectEqual(@as(usize, 0), reused.nodes.len);
    try std.testing.expect(reused.escape_projection != null);
    try std.testing.expectEqual(target, reused.escape_projection.?.target);

    var rejected_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    try std.testing.expectError(
        error.UnsupportedShape,
        rejected_builder.buildRegionImplWithEntryArgumentsAndEdge(
            target,
            stop,
            null,
            null,
            null,
            null,
            false,
            null,
            null,
            null,
        ),
    );
}

test "empty parameterized continuation recovers one authenticated joined edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const prefix = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const owner_stop = ir.BlockId.fromIndex(2);
    const incoming_stop = ir.BlockId.fromIndex(3);
    const owner_continue = ir.BlockId.fromIndex(4);
    const incoming_continue = ir.BlockId.fromIndex(5);
    const original = ir.BlockId.fromIndex(6);
    const argument = ir.ValueId.fromIndex(0);
    const other_argument = ir.ValueId.fromIndex(1);
    const target_parameter = ir.ValueId.fromIndex(2);
    const original_parameter = ir.ValueId.fromIndex(3);
    const arguments = [_]ir.ValueId{argument};

    var blocks = [_]ir.Block{
        .{ .id = prefix, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &arguments,
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{target_parameter}, .terminator = .{ .jump = .{ .target = owner_stop } } },
        .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = incoming_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = owner_continue, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = incoming_continue, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original, .function = function_id, .parameters = &.{original_parameter}, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ argument, other_argument },
        .blocks = &.{ prefix, target, owner_stop, incoming_stop, owner_continue, incoming_continue, original },
        .entry_block = prefix,
    };
    const values = [_]ir.Value{
        .{ .id = argument, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = other_argument, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = target_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = original_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = original, .index = 0 } } },
    };
    var rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = prefix,
        .kind = .jump,
        .from = .{ .target = original, .arguments = &arguments },
        .to = .{ .target = target, .arguments = &arguments },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    var program = ir.Program{
        .program_id = "empty-parameterized-joined-continuation",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, true, false, false, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, .{
        .start = target,
        .stop = owner_stop,
        .loop_exit = null,
        .continue_target = owner_continue,
        .parameter_arguments = &arguments,
    }, null, null, null, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const incoming_reference: ir.CfgEdgeRef = .{ .source = prefix, .kind = .jump, .target = target };
    try std.testing.expect(try builder.hasAuthenticatedContinuationBridge(incoming_reference));
    try std.testing.expect(try builder.hasAuthenticatedUniqueIncomingParameterizedBridge(
        target,
        &arguments,
        &arguments,
    ));

    const reused = try builder.buildRegionImplWithEntryArguments(
        target,
        incoming_stop,
        null,
        null,
        null,
        null,
        false,
        incoming_continue,
        &arguments,
    );
    defer destroyRegion(std.testing.allocator, reused);
    try std.testing.expectEqual(@as(usize, 0), reused.nodes.len);
    try std.testing.expect(reused.escape_projection != null);
    try std.testing.expectEqual(target, reused.escape_projection.?.target);

    blocks[prefix.index()].terminator = .{ .jump = .{
        .target = target,
        .arguments = &[_]ir.ValueId{other_argument},
    } };
    program.blocks = &blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer tampered_analysis.deinit();
    var tampered_visited = [_]bool{ false, true, false, false, false, false, false };
    var tampered_contexts = [_]?Builder.VisitContext{ null, .{
        .start = target,
        .stop = owner_stop,
        .loop_exit = null,
        .continue_target = owner_continue,
        .parameter_arguments = &arguments,
    }, null, null, null, null, null };
    var tampered_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &tampered_analysis,
        .visited = &tampered_visited,
        .visited_contexts = &tampered_contexts,
        .loop_headers = loop_headers,
    };
    try std.testing.expect(!try tampered_builder.hasAuthenticatedUniqueIncomingParameterizedBridge(
        target,
        &arguments,
        &arguments,
    ));
    try std.testing.expectError(
        error.UnsupportedShape,
        tampered_builder.buildRegionImplWithEntryArguments(
            target,
            incoming_stop,
            null,
            null,
            null,
            null,
            false,
            incoming_continue,
            &arguments,
        ),
    );
}

test "transferred parameterized join recovers only one authenticated edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(0);
    const predecessor = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const owner_stop = ir.BlockId.fromIndex(3);
    const target_stop = ir.BlockId.fromIndex(4);
    const original = ir.BlockId.fromIndex(5);
    const condition = ir.ValueId.fromIndex(0);
    const first_argument = ir.ValueId.fromIndex(1);
    const second_argument = ir.ValueId.fromIndex(2);
    const first_parameter = ir.ValueId.fromIndex(3);
    const second_parameter = ir.ValueId.fromIndex(4);
    const original_first_parameter = ir.ValueId.fromIndex(5);
    const original_second_parameter = ir.ValueId.fromIndex(6);
    const arguments = [_]ir.ValueId{ first_argument, second_argument };

    var blocks = [_]ir.Block{
        .{ .id = owner, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = predecessor },
            .else_edge = .{ .target = owner_stop },
        } } },
        .{ .id = predecessor, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &arguments,
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{ first_parameter, second_parameter }, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = target_stop },
            .else_edge = .{ .target = owner_stop },
        } } },
        .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = target_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original, .function = function_id, .parameters = &.{ original_first_parameter, original_second_parameter }, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = target_stop },
            .else_edge = .{ .target = owner_stop },
        } } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ condition, first_argument, second_argument },
        .blocks = &.{ owner, predecessor, target, owner_stop, target_stop, original },
        .entry_block = owner,
    };
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = first_argument, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = second_argument, .function = function_id, .origin = .{ .parameter = 2 } },
        .{ .id = first_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = second_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 1 } } },
        .{ .id = original_first_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = original, .index = 0 } } },
        .{ .id = original_second_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = original, .index = 1 } } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = predecessor,
        .kind = .jump,
        .from = .{ .target = original, .arguments = &arguments },
        .to = .{ .target = target, .arguments = &arguments },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    var program = ir.Program{
        .program_id = "transferred-parameterized-join",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var nested_nodes = [_]Node{.{ .block = predecessor }};
    var nested_region = Region{ .nodes = &nested_nodes, .stop = target, .loop_exit = null };
    var empty_nodes = [_]Node{};
    var empty_region = Region{ .nodes = &empty_nodes, .stop = owner_stop, .loop_exit = null };
    const node: Node = .{ .branch = .{
        .block = owner,
        .then_region = &nested_region,
        .else_region = &empty_region,
        .join = target,
    } };
    var visited = [_]bool{ false, false, true, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, .{
        .start = target,
        .stop = owner_stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &arguments,
    }, null, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };

    const incoming_reference = ir.CfgEdgeRef{ .source = predecessor, .kind = .jump, .target = target };
    try std.testing.expect(try builder.hasAuthenticatedContinuationBridge(incoming_reference));
    const projected = (try builder.visitedEntryContinuationProjection(
        node,
        target,
        null,
        null,
    )).?;
    try std.testing.expectEqualSlices(ir.ValueId, &arguments, projected.arguments.?);
    try std.testing.expect(projected.projection == .transferred);

    const alternate = ir.BlockId.fromIndex(6);
    const alternate_parameter_first = ir.ValueId.fromIndex(7);
    const alternate_parameter_second = ir.ValueId.fromIndex(8);
    var ambiguous_blocks = blocks ++ [_]ir.Block{.{
        .id = alternate,
        .function = function_id,
        .parameters = &.{ alternate_parameter_first, alternate_parameter_second },
        .terminator = .{ .jump = .{ .target = target, .arguments = &arguments } },
    }};
    ambiguous_blocks[owner.index()].terminator = .{ .branch = .{
        .condition = condition,
        .then_edge = .{ .target = predecessor },
        .else_edge = .{ .target = alternate },
    } };
    var ambiguous_function = function;
    ambiguous_function.blocks = &.{ owner, predecessor, target, owner_stop, target_stop, original, alternate };
    var ambiguous_program = program;
    ambiguous_program.blocks = &ambiguous_blocks;
    ambiguous_program.functions = &.{ambiguous_function};
    var ambiguous_analysis = try cfg.Analysis.init(std.testing.allocator, &ambiguous_program, ambiguous_function);
    defer ambiguous_analysis.deinit();
    var ambiguous_builder = builder;
    ambiguous_builder.analysis = &ambiguous_analysis;
    var ambiguous_nodes = [_]Node{ .{ .block = predecessor }, .{ .block = alternate } };
    var ambiguous_nested_region = Region{ .nodes = &ambiguous_nodes, .stop = target, .loop_exit = null };
    var ambiguous_node = node;
    ambiguous_node.branch.then_region = &ambiguous_nested_region;
    try std.testing.expect((try ambiguous_builder.visitedEntryContinuationProjection(
        ambiguous_node,
        target,
        null,
        null,
    )) == null);

    var tampered_arguments = arguments;
    tampered_arguments[1] = condition;
    var tampered_blocks = blocks;
    tampered_blocks[predecessor.index()].terminator = .{ .jump = .{
        .target = target,
        .arguments = &tampered_arguments,
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, function);
    defer tampered_analysis.deinit();
    var tampered_builder = builder;
    tampered_builder.analysis = &tampered_analysis;
    try std.testing.expect((try tampered_builder.visitedEntryContinuationProjection(
        node,
        target,
        null,
        null,
    )) == null);
}

test "raw parameterized numeric join authenticates a dominating tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const owner = ir.BlockId.fromIndex(2);
    const predecessor = ir.BlockId.fromIndex(3);
    const target = ir.BlockId.fromIndex(4);
    const body = ir.BlockId.fromIndex(5);
    const exit = ir.BlockId.fromIndex(6);
    const stop = ir.BlockId.fromIndex(7);
    const alternate = ir.BlockId.fromIndex(8);
    const input_first = ir.ValueId.fromIndex(0);
    const input_second = ir.ValueId.fromIndex(1);
    const input_third = ir.ValueId.fromIndex(2);
    const condition = ir.ValueId.fromIndex(3);
    const producer_first = ir.ValueId.fromIndex(4);
    const producer_second = ir.ValueId.fromIndex(5);
    const producer_third = ir.ValueId.fromIndex(6);
    const producer_fourth = ir.ValueId.fromIndex(7);
    const target_first = ir.ValueId.fromIndex(8);
    const target_second = ir.ValueId.fromIndex(9);
    const target_third = ir.ValueId.fromIndex(10);
    const target_fourth = ir.ValueId.fromIndex(11);
    const has_value = ir.ValueId.fromIndex(12);
    const next_limit = ir.ValueId.fromIndex(13);
    const next_step = ir.ValueId.fromIndex(14);
    const next_control = ir.ValueId.fromIndex(15);
    const effect_value = ir.ValueId.fromIndex(16);
    const transition_id = ir.InstructionId.fromIndex(0);
    const effect_constant_id = ir.InstructionId.fromIndex(1);
    const effect_write_id = ir.InstructionId.fromIndex(2);
    const place_id = ir.PlaceId.fromIndex(0);
    const incoming_arguments = [_]ir.ValueId{
        producer_first,
        producer_second,
        producer_third,
        producer_fourth,
    };

    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{
            .target = producer,
            .arguments = &.{ input_first, input_second, input_third, condition },
        } } },
        .{ .id = producer, .function = function_id, .parameters = &incoming_arguments, .terminator = .{ .jump = .{
            .target = owner,
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = predecessor },
            .else_edge = .{ .target = stop },
        } } },
        .{ .id = predecessor, .function = function_id, .instructions = &.{ effect_constant_id, effect_write_id }, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &incoming_arguments,
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{
            target_first,
            target_second,
            target_third,
            target_fourth,
        }, .instructions = &.{transition_id}, .terminator = .{ .branch = .{
            .condition = has_value,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = stop } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .jump = .{ .target = stop } } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = alternate, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &incoming_arguments,
        } } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ input_first, input_second, input_third, condition },
        .blocks = &.{ entry, producer, owner, predecessor, target, body, exit, stop },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = input_first, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = input_second, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = input_third, .function = function_id, .origin = .{ .parameter = 2 } },
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 3 } },
        .{ .id = producer_first, .function = function_id, .origin = .{ .block_parameter = .{ .block = producer, .index = 0 } } },
        .{ .id = producer_second, .function = function_id, .origin = .{ .block_parameter = .{ .block = producer, .index = 1 } } },
        .{ .id = producer_third, .function = function_id, .origin = .{ .block_parameter = .{ .block = producer, .index = 2 } } },
        .{ .id = producer_fourth, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = producer, .index = 3 } } },
        .{ .id = target_first, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = target_second, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 1 } } },
        .{ .id = target_third, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 2 } } },
        .{ .id = target_fourth, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = target, .index = 3 } } },
        .{ .id = has_value, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 0 } } },
        .{ .id = next_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 1 } } },
        .{ .id = next_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 3 } } },
        .{ .id = effect_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = effect_constant_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = transition_id, .block = target, .operation = .{ .numeric_for_next = .{
            .control = target_first,
            .limit = target_second,
            .step = target_third,
            .initial = target_fourth,
        } }, .results = &.{ has_value, next_limit, next_step, next_control }, .effects = .numeric_for_next },
        .{ .id = effect_constant_id, .block = predecessor, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{effect_value}, .effects = .pure },
        .{ .id = effect_write_id, .block = predecessor, .operation = .{ .place_write = .{ .place = place_id, .value = effect_value } }, .results = &.{}, .effects = .place_write },
    };
    const places = [_]ir.Place{.{ .id = place_id, .function = function_id, .origin = .{ .local = 0 } }};
    var program = ir.Program{
        .program_id = "raw-parameterized-numeric-join",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, false, true, false, true, false, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, .{
        .start = target,
        .stop = stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = null,
    }, null, .{
        .start = target,
        .stop = stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = null,
    }, null, null, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    var nested_nodes = [_]Node{.{ .block = predecessor }};
    var nested_region = Region{ .nodes = &nested_nodes, .stop = target, .loop_exit = null };
    var empty_nodes = [_]Node{};
    var empty_region = Region{ .nodes = &empty_nodes, .stop = stop, .loop_exit = null };
    const node: Node = .{ .branch = .{
        .block = owner,
        .then_region = &nested_region,
        .else_region = &empty_region,
        .join = target,
    } };

    const projected = (try builder.visitedEntryContinuationProjection(
        node,
        target,
        null,
        null,
    )).?;
    try std.testing.expect(projected.projection == .transferred);
    try std.testing.expect(projected.recovered_context_arguments);
    try std.testing.expectEqualSlices(ir.ValueId, &incoming_arguments, projected.arguments.?);

    var equivalent_owned_blocks = blocks;
    equivalent_owned_blocks[owner.index()].terminator = .{ .branch = .{
        .condition = condition,
        .then_edge = .{ .target = predecessor },
        .else_edge = .{ .target = target, .arguments = &incoming_arguments },
    } };
    var equivalent_owned_program = program;
    equivalent_owned_program.blocks = &equivalent_owned_blocks;
    var equivalent_owned_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &equivalent_owned_program,
        function,
    );
    defer equivalent_owned_analysis.deinit();
    var equivalent_owned_builder = builder;
    equivalent_owned_builder.analysis = &equivalent_owned_analysis;
    const equivalent_owned = (try equivalent_owned_builder.visitedEntryContinuationProjection(
        node,
        target,
        null,
        null,
    )).?;
    try std.testing.expect(equivalent_owned.projection == .transferred);
    try std.testing.expect(equivalent_owned.recovered_context_arguments);
    try std.testing.expectEqualSlices(ir.ValueId, &incoming_arguments, equivalent_owned.arguments.?);

    var malformed_arguments = incoming_arguments[0..3].*;
    var malformed_blocks = blocks;
    malformed_blocks[predecessor.index()].terminator = .{ .jump = .{
        .target = target,
        .arguments = &malformed_arguments,
    } };
    var malformed_program = program;
    malformed_program.blocks = &malformed_blocks;
    var malformed_analysis = try cfg.Analysis.init(std.testing.allocator, &malformed_program, function);
    defer malformed_analysis.deinit();
    var malformed_builder = builder;
    malformed_builder.analysis = &malformed_analysis;
    try std.testing.expect((try malformed_builder.visitedEntryContinuationProjection(
        node,
        target,
        null,
        null,
    )) == null);

    var tampered_arguments = incoming_arguments;
    tampered_arguments[1] = condition;
    var tampered_blocks = blocks;
    tampered_blocks[predecessor.index()].terminator = .{ .jump = .{
        .target = target,
        .arguments = &tampered_arguments,
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, function);
    defer tampered_analysis.deinit();
    var tampered_builder = builder;
    tampered_builder.analysis = &tampered_analysis;
    try std.testing.expect((try tampered_builder.visitedEntryContinuationProjection(
        node,
        target,
        null,
        null,
    )) == null);

    var ambiguous_blocks = blocks;
    ambiguous_blocks[owner.index()].terminator = .{ .branch = .{
        .condition = condition,
        .then_edge = .{ .target = predecessor },
        .else_edge = .{ .target = alternate },
    } };
    var ambiguous_function = function;
    ambiguous_function.blocks = &.{ entry, producer, owner, predecessor, target, body, exit, stop, alternate };
    var ambiguous_program = program;
    ambiguous_program.functions = &.{ambiguous_function};
    ambiguous_program.blocks = &ambiguous_blocks;
    var ambiguous_analysis = try cfg.Analysis.init(std.testing.allocator, &ambiguous_program, ambiguous_function);
    defer ambiguous_analysis.deinit();
    var ambiguous_builder = builder;
    ambiguous_builder.analysis = &ambiguous_analysis;
    var ambiguous_nodes = [_]Node{ .{ .block = predecessor }, .{ .block = alternate } };
    var ambiguous_then_region = Region{ .nodes = &ambiguous_nodes, .stop = target, .loop_exit = null };
    var ambiguous_empty_nodes = [_]Node{};
    var ambiguous_else_region = Region{ .nodes = &ambiguous_empty_nodes, .stop = target, .loop_exit = null };
    var ambiguous_node = node;
    ambiguous_node.branch.then_region = &ambiguous_then_region;
    ambiguous_node.branch.else_region = &ambiguous_else_region;
    try std.testing.expect((try ambiguous_builder.visitedEntryContinuationProjection(
        ambiguous_node,
        target,
        null,
        null,
    )) == null);
}

test "structured node split bridge follows owned nested predecessor" {
    const function_id = ir.FunctionId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(0);
    const predecessor = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const stop = ir.BlockId.fromIndex(3);
    const original = ir.BlockId.fromIndex(4);
    const blocks = [_]ir.Block{
        .{ .id = owner, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = predecessor },
            .else_edge = .{ .target = stop },
        } } },
        .{ .id = predecessor, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ir.ValueId.fromIndex(0)},
        .blocks = &.{ owner, predecessor, target, stop, original },
        .entry_block = owner,
    };
    const values = [_]ir.Value{.{
        .id = ir.ValueId.fromIndex(0),
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = predecessor,
        .kind = .jump,
        .from = .{ .target = original },
        .to = .{ .target = target },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const program: ir.Program = .{
        .program_id = "structured-stable-bridge-continuation",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();

    var then_nodes = [_]Node{.{ .block = predecessor }};
    var else_nodes = [_]Node{};
    var then_region = Region{ .nodes = &then_nodes, .stop = target, .loop_exit = null };
    var else_region = Region{ .nodes = &else_nodes, .stop = stop, .loop_exit = null };
    const node: Node = .{ .branch = .{
        .block = owner,
        .then_region = &then_region,
        .else_region = &else_region,
        .join = target,
    } };

    try std.testing.expect(try hasStableNodeSplitBridgeFromNode(
        std.testing.allocator,
        &analysis,
        node,
        target,
    ));
}

test "empty collision records one authenticated multi-entry clone group" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const first_source = ir.BlockId.fromIndex(1);
    const second_source = ir.BlockId.fromIndex(2);
    const original = ir.BlockId.fromIndex(3);
    const target = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first_source },
            .else_edge = .{ .target = second_source },
        } } },
        .{ .id = first_source, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = second_source, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = original, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, first_source, second_source, original, target },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = first_source,
            .kind = .jump,
            .from = .{ .target = original },
            .to = .{ .target = target },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = second_source,
            .kind = .jump,
            .from = .{ .target = original },
            .to = .{ .target = target },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
    };
    const program: ir.Program = .{
        .program_id = "empty-multi-entry-clone-group",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, false, false, false, true };
    var contexts = [_]?Builder.VisitContext{ null, null, null, null, .{
        .start = original,
        .stop = null,
        .loop_exit = null,
        .continue_target = null,
    } };
    var collision: ?Collision = null;
    defer if (collision) |*value| value.deinit(std.testing.allocator);
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
        .visited_count = 1,
        .collision = &collision,
    };

    try std.testing.expectError(
        error.UnsupportedShape,
        builder.buildRegionImpl(target, null, null, null, null, null, false, null),
    );
    try std.testing.expect(collision != null);
    const recorded = collision.?;
    try std.testing.expectEqual(@as(usize, 2), recorded.incoming_group.len);
    try std.testing.expect(recorded.incoming == null);
    for (recorded.incoming_group) |reference| {
        try std.testing.expectEqual(target, reference.target);
        try std.testing.expectEqual(ir.CfgEdgeKind.jump, reference.kind);
        try std.testing.expect(reference.source == first_source or reference.source == second_source);
    }
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

fn narrowIncomingGroupByContextAlloc(
    allocator: std.mem.Allocator,
    builder: *const Builder,
    group: []ir.CfgEdgeRef,
    representative: ir.CfgEdgeRef,
) std.mem.Allocator.Error![]ir.CfgEdgeRef {
    const representative_context = builder.contextForBlock(representative.source) orelse return group;
    var matching_count: usize = 0;
    for (group) |reference| {
        if (collisionContextsMatch(representative_context, builder.contextForBlock(reference.source))) matching_count += 1;
    }
    if (matching_count == group.len) return group;

    const narrowed = try allocator.alloc(ir.CfgEdgeRef, matching_count);
    var index: usize = 0;
    for (group) |reference| {
        if (!collisionContextsMatch(representative_context, builder.contextForBlock(reference.source))) continue;
        narrowed[index] = reference;
        index += 1;
    }
    allocator.free(group);
    return narrowed;
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

const StableNodeSplitBridge = struct {
    source: ir.BlockId,
    group: ir.NodeSplitGroupId,
};

fn stableNodeSplitBridgeForEdge(
    program: *const ir.Program,
    reference: ir.CfgEdgeRef,
) ?StableNodeSplitBridge {
    if (reference.source.index() >= program.blocks.len or reference.target.index() >= program.blocks.len) return null;
    const current = cfg_edge.value(program, reference) orelse return null;
    if (current.target != reference.target) return null;

    var selected: ?StableNodeSplitBridge = null;
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.rule != .node_split or rewrite.source != reference.source or
            rewrite.kind != reference.kind or rewrite.from.target == rewrite.to.target or
            rewrite.to.target != reference.target or rewrite.node_split_group == null or
            rewrite.from.arguments.len != rewrite.to.arguments.len or
            !std.mem.eql(ir.ValueId, rewrite.from.arguments, rewrite.to.arguments) or
            !std.mem.eql(ir.ValueId, current.arguments, rewrite.to.arguments)) continue;
        if (rewrite.from.target.index() >= program.blocks.len) return null;
        const source = program.blocks[rewrite.from.target.index()];
        const clone = program.blocks[rewrite.to.target.index()];
        if (source.id != rewrite.from.target or clone.id != rewrite.to.target or
            source.function != clone.function)
        {
            return null;
        }
        const candidate: StableNodeSplitBridge = .{
            .source = rewrite.from.target,
            .group = rewrite.node_split_group.?,
        };
        if (selected) |existing| {
            if (existing.source != candidate.source or existing.group != candidate.group) return null;
        } else {
            selected = candidate;
        }
    }
    return selected;
}

fn stableNodeSplitIncomingGroupAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    target: ir.BlockId,
) std.mem.Allocator.Error!?[]ir.CfgEdgeRef {
    var incoming: std.ArrayList(ir.CfgEdgeRef) = .empty;
    defer incoming.deinit(allocator);
    var bridge_source: ?ir.BlockId = null;
    var bridge_group: ?ir.NodeSplitGroupId = null;

    for (0..analysis.predecessorCount(target)) |predecessor_index| {
        const predecessor = analysis.predecessorAt(target, predecessor_index) orelse return null;
        if (!analysis.isReachable(predecessor)) return null;
        const reference = directEdgeReference(analysis.program, .{ .block = predecessor }, target) orelse return null;
        const bridge = stableNodeSplitBridgeForEdge(analysis.program, reference) orelse return null;
        if (bridge_source) |existing| {
            if (existing != bridge.source or bridge_group.? != bridge.group) return null;
        } else {
            bridge_source = bridge.source;
            bridge_group = bridge.group;
        }
        try incoming.append(allocator, reference);
    }

    if (incoming.items.len < 2) return null;
    const owned = try incoming.toOwnedSlice(allocator);
    return owned;
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

fn hasStableNodeSplitBridge(
    program: *const ir.Program,
    source_id: ir.BlockId,
    target: ir.BlockId,
) bool {
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.rule != .node_split or rewrite.source != source_id or
            rewrite.source.index() >= program.blocks.len or
            rewrite.to.target != target or rewrite.from.target == rewrite.to.target or
            rewrite.from.arguments.len != rewrite.to.arguments.len or
            !std.mem.eql(ir.ValueId, rewrite.from.arguments, rewrite.to.arguments)) continue;
        const source = program.blocks[rewrite.source.index()];
        const clone = program.blocks[rewrite.to.target.index()];
        if (source.id != rewrite.source or clone.id != rewrite.to.target or
            source.function != clone.function) continue;
        const current = cfg_edge.value(program, .{
            .source = rewrite.source,
            .kind = rewrite.kind,
            .target = rewrite.to.target,
        }) orelse continue;
        if (std.mem.eql(ir.ValueId, current.arguments, rewrite.to.arguments)) return true;
    }
    return false;
}

fn hasStableNodeSplitBridgeFromNode(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    node: Node,
    target: ir.BlockId,
) std.mem.Allocator.Error!bool {
    return hasStableNodeSplitBridgeFromNodeWithContext(allocator, analysis, node, target, null);
}

fn hasStableNodeSplitBridgeFromNodeWithContext(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    node: Node,
    target: ir.BlockId,
    replay_context: ?*structural_overlap.ReplayProjectionContext,
) std.mem.Allocator.Error!bool {
    if (node == .block) {
        const source = node.block;
        const reference = directEdgeReference(analysis.program, .{ .block = source }, target) orelse return false;
        return if (replay_context) |context|
            context.hasAuthenticatedContinuationBridgeForEdge(analysis, reference)
        else
            structural_overlap.hasAuthenticatedContinuationBridgeForEdgeAlloc(
                allocator,
                analysis.program,
                analysis,
                reference,
            );
    }

    // Structured nodes can own the real predecessor in a nested region. The
    // node header is not necessarily the block that enters the continuation.
    const incoming = try nodeIncomingEdgesAlloc(allocator, analysis, node, target);
    defer allocator.free(incoming);
    if (incoming.len == 0) return false;
    for (incoming) |reference| {
        const authenticated = if (replay_context) |context|
            try context.hasAuthenticatedContinuationBridgeForEdge(analysis, reference)
        else
            try structural_overlap.hasAuthenticatedContinuationBridgeForEdgeAlloc(
                allocator,
                analysis.program,
                analysis,
                reference,
            );
        if (!authenticated) return false;
    }
    return true;
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

const OwnedIncomingEntry = struct {
    reference: ir.CfgEdgeRef,
    arguments: []const ir.ValueId,
};

const VisitedEntryProjection = struct {
    projection: FinalContinueProjection,
    arguments: ?[]const ir.ValueId,
    recovered_context_arguments: bool,
    recovered_context_reference: ?ir.CfgEdgeRef,
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

// A structured node may finish through a nested arm whose raw predecessor is
// not the node header. Preserve that edge as the projection boundary only
// when the builder still owns the predecessor and the live edge carries the
// exact entry tuple being structured.
fn continuationProjectionForVisitedEntry(
    program: *const ir.Program,
    node: Node,
    target: ir.BlockId,
    incoming: ?ir.CfgEdgeRef,
    arguments: ?[]const ir.ValueId,
) ?FinalContinueProjection {
    if (finalContinueProjection(program, node, target)) |projection| return projection;

    const reference = incoming orelse return null;
    if (reference.target != target or !nodeOwnsBlock(node, reference.source)) return null;
    const expected_arguments = arguments orelse return null;
    const edge = cfg_edge.value(program, reference) orelse return null;
    if (edge.target != target or !std.mem.eql(ir.ValueId, edge.arguments, expected_arguments)) return null;
    return .{ .edge = edge };
}

test "authenticated clone boundary projection covers an owned continuation clone" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const root = ir.BlockId.fromIndex(1);
    const source = ir.BlockId.fromIndex(2);
    const clone = ir.BlockId.fromIndex(3);
    const selector = ir.ValueId.fromIndex(0);
    const outer = ir.ValueId.fromIndex(1);
    const root_parameter = ir.ValueId.fromIndex(2);
    const clone_parameter = ir.ValueId.fromIndex(3);
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = root, .arguments = &.{outer} },
            .else_edge = .{ .target = source },
        } } },
        .{ .id = root, .function = function_id, .parameters = &.{root_parameter}, .terminator = .{ .return_values = &.{root_parameter} } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = clone, .arguments = &.{outer} } } },
        .{ .id = clone, .function = function_id, .parameters = &.{clone_parameter}, .terminator = .{ .return_values = &.{clone_parameter} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ selector, outer },
        .blocks = &.{ entry, root, source, clone },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = outer, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = root_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = root, .index = 0 } } },
        .{ .id = clone_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 0 } } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = source,
        .kind = .jump,
        .from = .{ .target = root, .arguments = &.{outer} },
        .to = .{ .target = clone, .arguments = &.{outer} },
        .rule = .node_split,
        .node_split_group = group,
    }};
    var program = ir.Program{
        .program_id = "authenticated-clone-boundary-projection",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var replay = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay.deinit();

    var visited = [_]bool{ true, true, true, false };
    var visited_contexts = [_]?Builder.VisitContext{ null, .{
        .start = entry,
        .stop = null,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &.{outer},
    }, null, null };
    var loop_headers = [_]bool{ false, false, false, false };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &visited_contexts,
        .loop_headers = &loop_headers,
        .replay_context = &replay,
        .visited_count = 3,
    };
    var escape_target: Builder.EscapeTarget = .{ .block = root, .parent = null };
    const projection = (try builder.authenticatedUnvisitedBoundaryProjection(
        clone,
        root,
        null,
        null,
        null,
        &escape_target,
        null,
        &.{outer},
        .{ .source = source, .kind = .jump, .target = clone },
    )).?;
    try std.testing.expectEqual(root, projection.target);
    try std.testing.expectEqual(root, projection.edge.target);
    try std.testing.expectEqualSlices(ir.ValueId, &.{outer}, projection.edge.arguments);
    try std.testing.expect(!projection.continue_projection);
    try std.testing.expect(visited[clone.index()]);
    try std.testing.expectEqual(@as(usize, 4), builder.visited_count);

    // Covered clone members intentionally have no independent visit context.
    // A later authenticated entry may still revisit the member, so the
    // boundary proof must remain usable after the group is marked visited.
    visited = [_]bool{ true, true, true, true };
    visited_contexts = [_]?Builder.VisitContext{ null, .{
        .start = entry,
        .stop = null,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &.{outer},
    }, null, null };
    builder.visited_count = 4;
    const covered_member_projection = (try builder.authenticatedUnvisitedBoundaryProjection(
        clone,
        root,
        null,
        null,
        null,
        &escape_target,
        null,
        &.{outer},
        .{ .source = source, .kind = .jump, .target = clone },
    )).?;
    try std.testing.expectEqual(root, covered_member_projection.target);
    try std.testing.expectEqual(root, covered_member_projection.edge.target);
    try std.testing.expectEqual(@as(usize, 4), builder.visited_count);

    const allowed = [_]bool{ true, true, true, true };
    const included_covered_member = try builder.buildRegionIncludingStart(
        clone,
        clone,
        &allowed,
        null,
        &escape_target,
        null,
        clone,
        &.{outer},
        .{ .source = source, .kind = .jump, .target = clone },
    );
    defer destroyRegion(std.testing.allocator, included_covered_member);
    try std.testing.expectEqual(@as(usize, 0), included_covered_member.nodes.len);
    try std.testing.expectEqual(root, included_covered_member.escape_projection.?.target);

    // A clone can enter a region whose canonical root is its stop boundary.
    // The root is intentionally unvisited in that context; replay and the
    // canonical parameter tuple still authenticate the projection.
    visited = [_]bool{ true, false, true, false };
    visited_contexts = [_]?Builder.VisitContext{ null, null, null, null };
    builder.visited_count = 2;
    const unvisited_boundary_projection = (try builder.authenticatedUnvisitedBoundaryProjection(
        clone,
        root,
        null,
        null,
        null,
        &escape_target,
        null,
        &.{outer},
        .{ .source = source, .kind = .jump, .target = clone },
    )).?;
    try std.testing.expectEqual(root, unvisited_boundary_projection.target);
    try std.testing.expectEqual(root, unvisited_boundary_projection.edge.target);
    try std.testing.expectEqual(@as(usize, 3), builder.visited_count);
    try std.testing.expect(!visited[root.index()]);
}

test "nested structured continuation projection uses the owned incoming edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(0);
    const predecessor = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const stop = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const first = ir.ValueId.fromIndex(1);
    const second = ir.ValueId.fromIndex(2);
    const target_first = ir.ValueId.fromIndex(3);
    const target_second = ir.ValueId.fromIndex(4);
    const arguments = [_]ir.ValueId{ first, second };
    const wrong_arguments = [_]ir.ValueId{ second, first };
    const blocks = [_]ir.Block{
        .{ .id = owner, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = predecessor },
            .else_edge = .{ .target = stop },
        } } },
        .{ .id = predecessor, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &arguments,
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{ target_first, target_second }, .terminator = .{ .return_values = &.{} } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ condition, first, second },
        .blocks = &.{ owner, predecessor, target, stop },
        .entry_block = owner,
    };
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = first, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = second, .function = function_id, .origin = .{ .parameter = 2 } },
        .{ .id = target_first, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = target_second, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 1 } } },
    };
    const program: ir.Program = .{
        .program_id = "nested-structured-continuation-projection",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var nested_nodes = [_]Node{.{ .block = predecessor }};
    var nested_region = Region{
        .nodes = &nested_nodes,
        .stop = target,
        .loop_exit = null,
    };
    var empty_nodes = [_]Node{};
    var empty_region = Region{
        .nodes = &empty_nodes,
        .stop = stop,
        .loop_exit = null,
    };
    const node: Node = .{ .branch = .{
        .block = owner,
        .then_region = &nested_region,
        .else_region = &empty_region,
        .join = null,
    } };
    const incoming: ir.CfgEdgeRef = .{ .source = predecessor, .kind = .jump, .target = target };
    try std.testing.expect(continuationProjectionForVisitedEntry(
        &program,
        node,
        target,
        incoming,
        &arguments,
    ) != null);
    try std.testing.expect(continuationProjectionForVisitedEntry(
        &program,
        node,
        target,
        incoming,
        &wrong_arguments,
    ) == null);
}

test "numeric continuation recovers one authenticated nested incoming edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(0);
    const predecessor = ir.BlockId.fromIndex(1);
    const source_header = ir.BlockId.fromIndex(2);
    const target_header = ir.BlockId.fromIndex(3);
    const body = ir.BlockId.fromIndex(4);
    const exit = ir.BlockId.fromIndex(5);
    const source_transition = ir.InstructionId.fromIndex(0);
    const target_transition = ir.InstructionId.fromIndex(1);
    const source_control = ir.ValueId.fromIndex(0);
    const source_limit = ir.ValueId.fromIndex(1);
    const source_step = ir.ValueId.fromIndex(2);
    const source_initial = ir.ValueId.fromIndex(3);
    const source_has = ir.ValueId.fromIndex(4);
    const source_next_limit = ir.ValueId.fromIndex(5);
    const source_next_step = ir.ValueId.fromIndex(6);
    const source_next_control = ir.ValueId.fromIndex(7);
    const target_control = ir.ValueId.fromIndex(8);
    const target_limit = ir.ValueId.fromIndex(9);
    const target_step = ir.ValueId.fromIndex(10);
    const target_initial = ir.ValueId.fromIndex(11);
    const target_has = ir.ValueId.fromIndex(12);
    const target_next_limit = ir.ValueId.fromIndex(13);
    const target_next_step = ir.ValueId.fromIndex(14);
    const target_next_control = ir.ValueId.fromIndex(15);

    const source_parameters = [_]ir.ValueId{ source_control, source_limit, source_step, source_initial };
    const target_parameters = [_]ir.ValueId{ target_control, target_limit, target_step, target_initial };
    const entry_arguments = source_parameters;
    const blocks = [_]ir.Block{
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{ .target = predecessor } } },
        .{ .id = predecessor, .function = function_id, .terminator = .{ .jump = .{
            .target = target_header,
            .arguments = &entry_arguments,
        } } },
        .{ .id = source_header, .function = function_id, .parameters = &source_parameters, .instructions = &.{source_transition}, .terminator = .{ .branch = .{
            .condition = source_has,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = target_header, .function = function_id, .parameters = &target_parameters, .instructions = &.{target_transition}, .terminator = .{ .branch = .{
            .condition = target_has,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ owner, predecessor, source_header, target_header, body, exit },
        .entry_block = owner,
    };
    const values = [_]ir.Value{
        .{ .id = source_control, .function = function_id, .origin = .{ .block_parameter = .{ .block = source_header, .index = 0 } } },
        .{ .id = source_limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = source_header, .index = 1 } } },
        .{ .id = source_step, .function = function_id, .origin = .{ .block_parameter = .{ .block = source_header, .index = 2 } } },
        .{ .id = source_initial, .function = function_id, .origin = .{ .block_parameter = .{ .block = source_header, .index = 3 } } },
        .{ .id = source_has, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = source_transition, .index = 0 } } },
        .{ .id = source_next_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = source_transition, .index = 1 } } },
        .{ .id = source_next_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = source_transition, .index = 2 } } },
        .{ .id = source_next_control, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = source_transition, .index = 3 } } },
        .{ .id = target_control, .function = function_id, .origin = .{ .block_parameter = .{ .block = target_header, .index = 0 } } },
        .{ .id = target_limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = target_header, .index = 1 } } },
        .{ .id = target_step, .function = function_id, .origin = .{ .block_parameter = .{ .block = target_header, .index = 2 } } },
        .{ .id = target_initial, .function = function_id, .origin = .{ .block_parameter = .{ .block = target_header, .index = 3 } } },
        .{ .id = target_has, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = target_transition, .index = 0 } } },
        .{ .id = target_next_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = target_transition, .index = 1 } } },
        .{ .id = target_next_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = target_transition, .index = 2 } } },
        .{ .id = target_next_control, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = target_transition, .index = 3 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = source_transition, .block = source_header, .operation = .{ .numeric_for_next = .{
            .control = source_control,
            .limit = source_limit,
            .step = source_step,
            .initial = source_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ source_has, source_next_limit, source_next_step, source_next_control }, .effects = .numeric_for_next },
        .{ .id = target_transition, .block = target_header, .operation = .{ .numeric_for_next = .{
            .control = target_control,
            .limit = target_limit,
            .step = target_step,
            .initial = target_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ target_has, target_next_limit, target_next_step, target_next_control }, .effects = .numeric_for_next },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = predecessor,
        .kind = .jump,
        .from = .{ .target = source_header, .arguments = &entry_arguments },
        .to = .{ .target = target_header, .arguments = &entry_arguments },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    var program = ir.Program{
        .program_id = "nested-authenticated-numeric-entry",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);
    var visited = [_]bool{ false, false, false, true, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, .{
        .start = source_header,
        .stop = exit,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &entry_arguments,
    }, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    var nested_nodes = [_]Node{.{ .block = predecessor }};
    var nested_region = Region{ .nodes = &nested_nodes, .stop = target_header, .loop_exit = null };
    var empty_nodes = [_]Node{};
    var empty_region = Region{ .nodes = &empty_nodes, .stop = exit, .loop_exit = null };
    const node: Node = .{ .branch = .{
        .block = owner,
        .then_region = &nested_region,
        .else_region = &empty_region,
        .join = null,
    } };

    const projected = (try builder.visitedEntryContinuationProjection(
        node,
        target_header,
        null,
        null,
    )).?;
    try std.testing.expectEqualSlices(ir.ValueId, &entry_arguments, projected.arguments.?);
    switch (projected.projection) {
        .edge => |edge| {
            try std.testing.expectEqual(target_header, edge.target);
            try std.testing.expectEqualSlices(ir.ValueId, &entry_arguments, edge.arguments);
        },
        .transferred => return error.TestUnexpectedResult,
    }

    const same_entry_context = Builder.VisitContext{
        .start = target_header,
        .stop = exit,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &entry_arguments,
    };
    const continuation_reference = ir.CfgEdgeRef{
        .source = predecessor,
        .kind = .jump,
        .target = target_header,
    };
    const parameters_match = try builder.parameterProjectionMatches(
        target_header,
        &entry_arguments,
        &entry_arguments,
    );
    try std.testing.expect(try builder.authenticatedSameEntryNumericReentry(
        target_header,
        target_header,
        body,
        null,
        exit,
        same_entry_context,
        parameters_match,
        continuation_reference,
    ));

    var tampered_blocks = blocks;
    tampered_blocks[predecessor.index()].terminator = .{ .jump = .{
        .target = target_header,
        .arguments = &.{ source_control, source_limit, source_step, target_initial },
    } };
    program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer tampered_analysis.deinit();
    var tampered_builder = builder;
    tampered_builder.analysis = &tampered_analysis;
    try std.testing.expect(!(try tampered_builder.authenticatedSameEntryNumericReentry(
        target_header,
        target_header,
        body,
        null,
        exit,
        same_entry_context,
        parameters_match,
        continuation_reference,
    )));
    try std.testing.expect((try tampered_builder.visitedEntryContinuationProjection(
        node,
        target_header,
        null,
        null,
    )) == null);
}

test "builder consumes arbitrary parameterized continuation projection" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const reentry = ir.BlockId.fromIndex(2);
    const owner_first = ir.ValueId.fromIndex(0);
    const owner_second = ir.ValueId.fromIndex(1);
    const formal_first = ir.ValueId.fromIndex(2);
    const formal_second = ir.ValueId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(4);
    const expected = [_]ir.ValueId{ owner_first, owner_second };
    const actual = [_]ir.ValueId{ formal_first, formal_second };
    const target_parameters = [_]ir.ValueId{ formal_first, formal_second };

    const values = [_]ir.Value{
        .{ .id = owner_first, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = owner_second, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = formal_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = formal_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 1 } } },
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 2 } },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = target, .arguments = expected[0..] },
            .else_edge = .{ .target = reentry },
        } } },
        .{ .id = target, .function = function_id, .parameters = target_parameters[0..], .terminator = .{ .return_values = &.{} } },
        .{ .id = reentry, .function = function_id, .terminator = .{ .jump = .{ .target = target, .arguments = actual[0..] } } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ owner_first, owner_second, condition },
        .blocks = &.{ entry, target, reentry },
        .entry_block = entry,
    };
    const program = ir.Program{
        .program_id = "builder-arbitrary-parameterized-projection",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);
    var replay_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay_context.deinit();
    var visited = [_]bool{ false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
        .replay_context = &replay_context,
    };
    const incoming = ir.CfgEdgeRef{ .source = reentry, .kind = .jump, .target = target };
    try std.testing.expect(!try builder.hasAuthenticatedContinuationBridge(incoming));
    try std.testing.expect(!try replay_context.hasAuthenticatedIterationContextualProjectionForEdge(
        &analysis,
        incoming,
        expected[0..],
    ));
    try std.testing.expect(try builder.hasAuthenticatedContinuationBridgeForExpectedParameters(
        incoming,
        expected[0..],
    ));

    var tampered_blocks = blocks;
    tampered_blocks[entry.index()].terminator = .{ .branch = .{
        .condition = condition,
        .then_edge = .{ .target = target, .arguments = actual[0..] },
        .else_edge = .{ .target = reentry },
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, function);
    defer tampered_analysis.deinit();
    var tampered_replay_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &tampered_program,
        function_id,
    );
    defer tampered_replay_context.deinit();
    var tampered_builder = builder;
    tampered_builder.analysis = &tampered_analysis;
    tampered_builder.replay_context = &tampered_replay_context;
    try std.testing.expect(!try tampered_builder.hasAuthenticatedContinuationBridgeForExpectedParameters(
        incoming,
        expected[0..],
    ));
}

test "same-entry numeric reentry accepts contextual state without a node split; same-SCC numeric reentry requires an authenticated loop-carried tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const candidate = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);

    const selector = ir.ValueId.fromIndex(0);
    const owner_control = ir.ValueId.fromIndex(1);
    const owner_limit = ir.ValueId.fromIndex(2);
    const owner_step = ir.ValueId.fromIndex(3);
    const owner_initial = ir.ValueId.fromIndex(4);
    const candidate_control = ir.ValueId.fromIndex(5);
    const candidate_limit = ir.ValueId.fromIndex(6);
    const candidate_step = ir.ValueId.fromIndex(7);
    const candidate_initial = ir.ValueId.fromIndex(8);
    const target_control = ir.ValueId.fromIndex(9);
    const target_limit = ir.ValueId.fromIndex(10);
    const target_step = ir.ValueId.fromIndex(11);
    const target_initial = ir.ValueId.fromIndex(12);
    const false_value = ir.ValueId.fromIndex(13);
    const candidate_has = ir.ValueId.fromIndex(14);
    const candidate_result_limit = ir.ValueId.fromIndex(15);
    const candidate_result_step = ir.ValueId.fromIndex(16);
    const candidate_next = ir.ValueId.fromIndex(17);
    const target_has = ir.ValueId.fromIndex(18);
    const target_result_limit = ir.ValueId.fromIndex(19);
    const target_result_step = ir.ValueId.fromIndex(20);
    const target_next = ir.ValueId.fromIndex(21);
    const false_instruction = ir.InstructionId.fromIndex(0);
    const candidate_instruction = ir.InstructionId.fromIndex(1);
    const target_instruction = ir.InstructionId.fromIndex(2);

    const expected = [_]ir.ValueId{ owner_control, owner_limit, owner_step, owner_initial };
    const actual = [_]ir.ValueId{ candidate_next, candidate_result_limit, candidate_result_step, false_value };
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{false_instruction}, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = candidate, .arguments = &expected },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &expected,
        } } },
        .{ .id = candidate, .function = function_id, .parameters = &.{ candidate_control, candidate_limit, candidate_step, candidate_initial }, .instructions = &.{candidate_instruction}, .terminator = .{ .branch = .{
            .condition = candidate_has,
            .then_edge = .{ .target = target, .arguments = &actual },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{ target_control, target_limit, target_step, target_initial }, .instructions = &.{target_instruction}, .terminator = .{ .branch = .{
            .condition = target_has,
            .then_edge = .{ .target = target, .arguments = &.{ target_next, target_result_limit, target_result_step, false_value } },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ selector, owner_control, owner_limit, owner_step, owner_initial },
        .blocks = &.{ entry, owner, candidate, target, exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = owner_control, .function = function_id, .type = .number, .origin = .{ .parameter = 1 } },
        .{ .id = owner_limit, .function = function_id, .type = .number, .origin = .{ .parameter = 2 } },
        .{ .id = owner_step, .function = function_id, .type = .number, .origin = .{ .parameter = 3 } },
        .{ .id = owner_initial, .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } },
        .{ .id = candidate_control, .function = function_id, .origin = .{ .block_parameter = .{ .block = candidate, .index = 0 } } },
        .{ .id = candidate_limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = candidate, .index = 1 } } },
        .{ .id = candidate_step, .function = function_id, .origin = .{ .block_parameter = .{ .block = candidate, .index = 2 } } },
        .{ .id = candidate_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = candidate, .index = 3 } } },
        .{ .id = target_control, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = target_limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 1 } } },
        .{ .id = target_step, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 2 } } },
        .{ .id = target_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = target, .index = 3 } } },
        .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_instruction, .index = 0 } } },
        .{ .id = candidate_has, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = candidate_instruction, .index = 0 } } },
        .{ .id = candidate_result_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = candidate_instruction, .index = 1 } } },
        .{ .id = candidate_result_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = candidate_instruction, .index = 2 } } },
        .{ .id = candidate_next, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = candidate_instruction, .index = 3 } } },
        .{ .id = target_has, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = target_instruction, .index = 0 } } },
        .{ .id = target_result_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = target_instruction, .index = 1 } } },
        .{ .id = target_result_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = target_instruction, .index = 2 } } },
        .{ .id = target_next, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = target_instruction, .index = 3 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = false_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = candidate_instruction, .block = candidate, .operation = .{ .numeric_for_next = .{
            .control = candidate_control,
            .limit = candidate_limit,
            .step = candidate_step,
            .initial = candidate_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ candidate_has, candidate_result_limit, candidate_result_step, candidate_next }, .effects = .numeric_for_next },
        .{ .id = target_instruction, .block = target, .operation = .{ .numeric_for_next = .{
            .control = target_control,
            .limit = target_limit,
            .step = target_step,
            .initial = target_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ target_has, target_result_limit, target_result_step, target_next }, .effects = .numeric_for_next },
    };
    var program = ir.Program{
        .program_id = "same-entry-contextual-numeric-reentry",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);
    var replay_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay_context.deinit();
    var visited = [_]bool{ false, false, false, true, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, .{
        .start = target,
        .stop = exit,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &expected,
    }, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
        .replay_context = &replay_context,
    };
    const incoming = ir.CfgEdgeRef{ .source = candidate, .kind = .branch_then, .target = target };
    // The caller supplies this only after its separate entry-projection proof.
    // This fixture isolates the same-entry helper's contextual edge witness.
    const parameters_match = true;
    try std.testing.expect(!try builder.hasAuthenticatedContinuationBridge(incoming));
    try std.testing.expect(try builder.hasAuthenticatedContinuationBridgeForExpectedParameters(incoming, &expected));
    const context = contexts[target.index()].?;
    try std.testing.expect(try builder.authenticatedSameEntryNumericReentry(
        target,
        target,
        candidate,
        null,
        null,
        context,
        parameters_match,
        incoming,
    ));
    try std.testing.expect(try builder.authenticatedSameEntryNumericReentry(
        target,
        target,
        candidate,
        null,
        exit,
        context,
        false,
        incoming,
    ));

    // A distinct tuple may enter the already-owned numeric header from an
    // acyclic prefix of the same owner context.  The live owner edge and the
    // replay projection authenticate this reuse without requiring a node
    // split.
    const distinct_context = Builder.VisitContext{
        .start = entry,
        .stop = exit,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &expected,
    };
    const distinct_formal_arguments = [_]ir.ValueId{
        target_control,
        target_limit,
        target_step,
        target_initial,
    };
    const target_to_candidate_arguments = [_]ir.ValueId{
        target_next,
        target_result_limit,
        target_result_step,
        false_value,
    };
    var parameterized_blocks = blocks;
    parameterized_blocks[candidate.index()].terminator = .{ .branch = .{
        .condition = candidate_has,
        .then_edge = .{ .target = target, .arguments = &distinct_formal_arguments },
        .else_edge = .{ .target = exit },
    } };
    var parameterized_values = values;
    parameterized_values[target_control.index()].type = .number;
    parameterized_values[target_limit.index()].type = .number;
    parameterized_values[target_step.index()].type = .number;
    var parameterized_program = program;
    parameterized_program.blocks = &parameterized_blocks;
    parameterized_program.values = &parameterized_values;
    var parameterized_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &parameterized_program,
        function,
    );
    defer parameterized_analysis.deinit();
    var parameterized_replay_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &parameterized_program,
        function_id,
    );
    defer parameterized_replay_context.deinit();
    var parameterized_builder = builder;
    parameterized_builder.analysis = &parameterized_analysis;
    parameterized_builder.replay_context = &parameterized_replay_context;
    const parameterized_incoming = ir.CfgEdgeRef{
        .source = candidate,
        .kind = .branch_then,
        .target = target,
    };
    try std.testing.expect(try parameterized_builder.authenticatedSameContextDistinctNumericReentry(
        target,
        entry,
        exit,
        null,
        null,
        distinct_context,
        true,
        parameterized_incoming,
    ));

    // Once the numeric header can reach the prefix source, the same replay
    // witness is insufficient: accepting it would erase a live cycle.
    var cyclic_blocks = parameterized_blocks;
    cyclic_blocks[target.index()].terminator = .{ .branch = .{
        .condition = target_has,
        .then_edge = .{ .target = candidate, .arguments = &target_to_candidate_arguments },
        .else_edge = .{ .target = exit },
    } };
    var cyclic_program = parameterized_program;
    cyclic_program.blocks = &cyclic_blocks;
    var cyclic_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &cyclic_program,
        function,
    );
    defer cyclic_analysis.deinit();
    var cyclic_replay_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &cyclic_program,
        function_id,
    );
    defer cyclic_replay_context.deinit();
    var cyclic_builder = parameterized_builder;
    cyclic_builder.analysis = &cyclic_analysis;
    cyclic_builder.replay_context = &cyclic_replay_context;
    try std.testing.expect(!(try cyclic_builder.authenticatedSameContextDistinctNumericReentry(
        target,
        entry,
        exit,
        null,
        null,
        distinct_context,
        true,
        incoming,
    )));

    // The owner context may begin at the current numeric header while a
    // nonempty candidate region re-enters it. This is valid only when the
    // candidate and header are in one SCC and the existing tuple proof still
    // authenticates the incoming edge.
    var same_boundary_blocks = blocks;
    same_boundary_blocks[target.index()].terminator = .{ .branch = .{
        .condition = target_has,
        .then_edge = .{ .target = candidate, .arguments = &target_to_candidate_arguments },
        .else_edge = .{ .target = exit },
    } };
    var same_boundary_program = program;
    same_boundary_program.blocks = &same_boundary_blocks;
    var same_boundary_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &same_boundary_program,
        function,
    );
    defer same_boundary_analysis.deinit();
    const same_boundary_loop_headers = try natural_loop.headerCandidatesAlloc(
        std.testing.allocator,
        &same_boundary_analysis,
    );
    defer std.testing.allocator.free(same_boundary_loop_headers);
    var same_boundary_replay_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &same_boundary_program,
        function_id,
    );
    defer same_boundary_replay_context.deinit();
    var same_boundary_visited = visited;
    var same_boundary_contexts = contexts;
    same_boundary_contexts[target.index()] = .{
        .start = target,
        .stop = exit,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &expected,
        .entry_reference = .{ .source = owner, .kind = .jump, .target = target },
    };
    var same_boundary_builder = builder;
    same_boundary_builder.analysis = &same_boundary_analysis;
    same_boundary_builder.visited = &same_boundary_visited;
    same_boundary_builder.visited_contexts = &same_boundary_contexts;
    same_boundary_builder.loop_headers = same_boundary_loop_headers;
    same_boundary_builder.replay_context = &same_boundary_replay_context;
    const same_boundary_incoming = ir.CfgEdgeRef{
        .source = candidate,
        .kind = .branch_then,
        .target = target,
    };
    try std.testing.expect(try same_boundary_builder.authenticatedSameBoundaryNumericReentry(
        target,
        candidate,
        exit,
        null,
        null,
        same_boundary_contexts[target.index()].?,
        true,
        same_boundary_incoming,
    ));

    // A different region start may re-enter the same numeric header while
    // preserving the enclosing boundary. The SCC edge and contextual tuple
    // proof are required in addition to the direct projection.
    const same_scc_context = Builder.VisitContext{
        .start = owner,
        .stop = exit,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &expected,
        .entry_reference = .{ .source = owner, .kind = .jump, .target = target },
    };
    try std.testing.expect(try same_boundary_builder.authenticatedSameSccNumericReentry(
        target,
        candidate,
        exit,
        null,
        null,
        same_scc_context,
        true,
        true,
        same_boundary_incoming,
    ));
    try std.testing.expect(try same_boundary_builder.authenticatedSameStopDistinctNumericReentry(
        target,
        candidate,
        exit,
        null,
        null,
        same_scc_context,
        false,
        true,
        same_boundary_incoming,
    ));
    try std.testing.expect(!(try builder.authenticatedSameStopDistinctNumericReentry(
        target,
        candidate,
        exit,
        null,
        null,
        same_scc_context,
        true,
        true,
        same_boundary_incoming,
    )));
    try std.testing.expect(!(try builder.authenticatedSameStopDistinctNumericReentry(
        target,
        candidate,
        exit,
        null,
        null,
        same_scc_context,
        false,
        false,
        same_boundary_incoming,
    )));
    try std.testing.expect(!(try builder.authenticatedSameStopDistinctNumericReentry(
        target,
        candidate,
        exit,
        null,
        null,
        same_scc_context,
        false,
        true,
        incoming,
    )));
    try std.testing.expect(!(try same_boundary_builder.authenticatedSameStopDistinctNumericReentry(
        target,
        candidate,
        exit,
        null,
        null,
        same_boundary_contexts[target.index()].?,
        false,
        true,
        same_boundary_incoming,
    )));
    try std.testing.expect(!(try same_boundary_builder.authenticatedSameSccNumericReentry(
        target,
        candidate,
        owner,
        null,
        null,
        same_scc_context,
        true,
        true,
        same_boundary_incoming,
    )));
    try std.testing.expect(!(try same_boundary_builder.authenticatedSameSccNumericReentry(
        target,
        candidate,
        exit,
        null,
        null,
        same_scc_context,
        true,
        false,
        same_boundary_incoming,
    )));
    var acyclic_same_scc_builder = builder;
    acyclic_same_scc_builder.replay_context = &replay_context;
    try std.testing.expect(!(try acyclic_same_scc_builder.authenticatedSameSccNumericReentry(
        target,
        candidate,
        exit,
        null,
        null,
        same_scc_context,
        true,
        true,
        incoming,
    )));

    // The same owner context remains rejected when the incoming source is not
    // in the header's SCC or when the enclosing stop differs.
    var acyclic_boundary_builder = builder;
    acyclic_boundary_builder.replay_context = &replay_context;
    try std.testing.expect(!(try acyclic_boundary_builder.authenticatedSameBoundaryNumericReentry(
        target,
        candidate,
        exit,
        null,
        null,
        context,
        true,
        incoming,
    )));
    try std.testing.expect(!(try same_boundary_builder.authenticatedSameBoundaryNumericReentry(
        target,
        candidate,
        owner,
        null,
        null,
        same_boundary_contexts[target.index()].?,
        true,
        same_boundary_incoming,
    )));

    try std.testing.expect(try builder.authenticatedVisitedParameterizedContinuationProjection(
        target,
        candidate,
        null,
        null,
        exit,
        context,
        false,
        &actual,
        incoming,
        true,
        true,
    ));

    var tampered_blocks = blocks;
    tampered_blocks[candidate.index()].terminator = .{ .branch = .{
        .condition = candidate_has,
        .then_edge = .{ .target = target, .arguments = &.{ candidate_next, candidate_result_limit, candidate_result_step, selector } },
        .else_edge = .{ .target = exit },
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, function);
    defer tampered_analysis.deinit();
    var tampered_replay_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &tampered_program,
        function_id,
    );
    defer tampered_replay_context.deinit();
    var tampered_builder = builder;
    tampered_builder.analysis = &tampered_analysis;
    tampered_builder.replay_context = &tampered_replay_context;
    const tampered_actual = [_]ir.ValueId{ candidate_next, candidate_result_limit, candidate_result_step, selector };
    try std.testing.expect(!(try tampered_builder.authenticatedSameSccNumericReentry(
        target,
        candidate,
        exit,
        null,
        null,
        same_scc_context,
        true,
        true,
        incoming,
    )));
    const tampered_parameters_match = try tampered_builder.parameterProjectionMatches(
        target,
        &expected,
        &tampered_actual,
    );
    try std.testing.expect(!tampered_parameters_match);
    try std.testing.expect(!(try tampered_builder.authenticatedSameEntryNumericReentry(
        target,
        target,
        candidate,
        null,
        null,
        context,
        parameters_match,
        incoming,
    )));
    try std.testing.expect(!(try tampered_builder.authenticatedSameEntryNumericReentry(
        target,
        target,
        candidate,
        null,
        exit,
        context,
        false,
        incoming,
    )));
    try std.testing.expect(!(try tampered_builder.authenticatedVisitedParameterizedContinuationProjection(
        target,
        candidate,
        null,
        null,
        exit,
        context,
        false,
        &tampered_actual,
        incoming,
        true,
        true,
    )));
}

test "non-header parameterized continuation recovers one authenticated nested incoming edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(0);
    const predecessor = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const stop = ir.BlockId.fromIndex(3);
    const original = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const argument = ir.ValueId.fromIndex(1);
    const target_parameter = ir.ValueId.fromIndex(2);
    const original_parameter = ir.ValueId.fromIndex(3);
    const arguments = [_]ir.ValueId{argument};
    var blocks = [_]ir.Block{
        .{ .id = owner, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = predecessor },
            .else_edge = .{ .target = stop },
        } } },
        .{ .id = predecessor, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &arguments,
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{target_parameter}, .terminator = .{ .jump = .{ .target = stop } } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original, .function = function_id, .parameters = &.{original_parameter}, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ condition, argument },
        .blocks = &.{ owner, predecessor, target, stop, original },
        .entry_block = owner,
    };
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = argument, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = target_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = original_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = original, .index = 0 } } },
    };
    var rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = predecessor,
        .kind = .jump,
        .from = .{ .target = original, .arguments = &arguments },
        .to = .{ .target = target, .arguments = &arguments },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    var program = ir.Program{
        .program_id = "non-header-authenticated-continuation",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var nested_nodes = [_]Node{.{ .block = predecessor }};
    var nested_region = Region{ .nodes = &nested_nodes, .stop = target, .loop_exit = null };
    var empty_nodes = [_]Node{};
    var empty_region = Region{ .nodes = &empty_nodes, .stop = stop, .loop_exit = null };
    const node: Node = .{ .branch = .{
        .block = owner,
        .then_region = &nested_region,
        .else_region = &empty_region,
        .join = null,
    } };

    var visited = [_]bool{ false, false, true, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, .{
        .start = target,
        .stop = stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &arguments,
    }, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const projected = (try builder.visitedEntryContinuationProjection(
        node,
        target,
        null,
        null,
    )).?;
    try std.testing.expectEqualSlices(ir.ValueId, &arguments, projected.arguments.?);
    switch (projected.projection) {
        .edge => |edge| {
            try std.testing.expectEqual(target, edge.target);
            try std.testing.expectEqualSlices(ir.ValueId, &arguments, edge.arguments);
        },
        .transferred => return error.TestUnexpectedResult,
    }

    const same_entry_context = Builder.VisitContext{
        .start = target,
        .stop = stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &arguments,
    };
    const continuation_reference = ir.CfgEdgeRef{
        .source = predecessor,
        .kind = .jump,
        .target = target,
    };
    const parameters_match = try builder.parameterProjectionMatches(
        target,
        &arguments,
        &arguments,
    );
    try std.testing.expect(try builder.authenticatedSameEntryParameterizedReentry(
        target,
        target,
        null,
        null,
        null,
        same_entry_context,
        parameters_match,
        &arguments,
        continuation_reference,
    ));
    const empty_arguments = [_]ir.ValueId{};
    try std.testing.expect(!(try builder.authenticatedSameEntryParameterizedReentry(
        target,
        target,
        null,
        null,
        null,
        same_entry_context,
        parameters_match,
        &empty_arguments,
        continuation_reference,
    )));

    var tampered_arguments = arguments;
    tampered_arguments[0] = condition;
    blocks[predecessor.index()].terminator = .{ .jump = .{
        .target = target,
        .arguments = &tampered_arguments,
    } };
    program.blocks = &blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer tampered_analysis.deinit();
    var tampered_builder = builder;
    tampered_builder.analysis = &tampered_analysis;
    try std.testing.expect((try tampered_builder.visitedEntryContinuationProjection(
        node,
        target,
        null,
        null,
    )) == null);
}

test "same-entry identity parameterized forwarder projects without a clone bridge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const suffix = ir.BlockId.fromIndex(2);
    const owner_stop = ir.BlockId.fromIndex(3);
    const current_stop = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const argument = ir.ValueId.fromIndex(1);
    const target_parameter = ir.ValueId.fromIndex(2);
    const arguments = [_]ir.ValueId{argument};
    const target_arguments = [_]ir.ValueId{target_parameter};

    var blocks = [_]ir.Block{
        .{ .id = owner, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = target, .arguments = &arguments },
            .else_edge = .{ .target = owner_stop },
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{target_parameter}, .terminator = .{ .jump = .{
            .target = suffix,
            .arguments = &target_arguments,
        } } },
        .{ .id = suffix, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = current_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ condition, argument },
        .blocks = &.{ owner, target, suffix, owner_stop, current_stop },
        .entry_block = owner,
    };
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = argument, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = target_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
    };
    var program = ir.Program{
        .program_id = "identity-parameterized-forwarder",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, true, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, .{
        .start = target,
        .stop = owner_stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &arguments,
    }, null, null, null };
    const context = contexts[target.index()].?;
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    try std.testing.expect(builder.identityParameterizedContinuationContextMatches(
        target,
        target,
        current_stop,
        null,
        null,
        context,
        true,
        &arguments,
    ));

    blocks[target.index()].terminator = .{ .jump = .{ .target = suffix, .arguments = &.{argument} } };
    try std.testing.expect(!builder.identityParameterizedContinuationContextMatches(
        target,
        target,
        current_stop,
        null,
        null,
        context,
        true,
        &arguments,
    ));
}

test "empty zero-parameter forwarder accepts canonical successor tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(0);
    const forwarder = ir.BlockId.fromIndex(1);
    const successor = ir.BlockId.fromIndex(2);
    const owner_stop = ir.BlockId.fromIndex(3);
    const current_stop = ir.BlockId.fromIndex(4);
    const input = ir.ValueId.fromIndex(0);
    const formal = ir.ValueId.fromIndex(1);
    var forwarded = [_]ir.ValueId{input};
    var blocks = [_]ir.Block{
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{ .target = forwarder } } },
        .{ .id = forwarder, .function = function_id, .terminator = .{ .jump = .{
            .target = successor,
            .arguments = forwarded[0..],
        } } },
        .{
            .id = successor,
            .function = function_id,
            .parameters = &.{formal},
            .terminator = .{ .return_values = &.{formal} },
        },
        .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = current_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{input},
        .blocks = &.{ owner, forwarder, successor, owner_stop, current_stop },
        .entry_block = owner,
    };
    const values = [_]ir.Value{
        .{ .id = input, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = formal, .function = function_id, .origin = .{ .block_parameter = .{ .block = successor, .index = 0 } } },
    };
    var program = ir.Program{
        .program_id = "empty-zero-parameter-forwarder",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);
    var visited = [_]bool{ false, true, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, null, null };
    const context: Builder.VisitContext = .{
        .start = forwarder,
        .stop = owner_stop,
        .loop_exit = null,
        .continue_target = null,
    };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    try std.testing.expect(builder.transparentEmptyContinuationContextMatches(
        forwarder,
        forwarder,
        current_stop,
        context,
        true,
    ));

    blocks[forwarder.index()].terminator = .{ .jump = .{ .target = successor, .arguments = &.{} } };
    try std.testing.expect(!builder.transparentEmptyContinuationContextMatches(
        forwarder,
        forwarder,
        current_stop,
        context,
        true,
    ));
}

test "empty numeric forwarder reentry requires an authenticated SCC" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const forwarder = ir.BlockId.fromIndex(1);
    const header = ir.BlockId.fromIndex(2);
    const body = ir.BlockId.fromIndex(3);
    const incoming = ir.BlockId.fromIndex(4);
    const stop = ir.BlockId.fromIndex(5);
    const control = ir.ValueId.fromIndex(0);
    const limit = ir.ValueId.fromIndex(1);
    const step = ir.ValueId.fromIndex(2);
    const initial = ir.ValueId.fromIndex(3);
    const has_value = ir.ValueId.fromIndex(4);
    const normalized_limit = ir.ValueId.fromIndex(5);
    const normalized_step = ir.ValueId.fromIndex(6);
    const next_control = ir.ValueId.fromIndex(7);
    const transition_id = ir.InstructionId.fromIndex(0);
    const tuple = [_]ir.ValueId{ control, limit, step, initial };

    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = forwarder } } },
        .{ .id = forwarder, .function = function_id, .terminator = .{ .jump = .{
            .target = header,
            .arguments = &tuple,
        } } },
        .{ .id = header, .function = function_id, .parameters = &.{
            control,
            limit,
            step,
            initial,
        }, .instructions = &.{transition_id}, .terminator = .{ .branch = .{
            .condition = has_value,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = stop },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = incoming } } },
        .{ .id = incoming, .function = function_id, .terminator = .{ .jump = .{ .target = forwarder } } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{},
        .blocks = &.{ entry, forwarder, header, body, incoming, stop },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = control, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
        .{ .id = limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 1 } } },
        .{ .id = step, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 2 } } },
        .{ .id = initial, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 3 } } },
        .{ .id = has_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 3 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = transition_id,
        .block = header,
        .operation = .{ .numeric_for_next = .{
            .control = control,
            .limit = limit,
            .step = step,
            .initial = initial,
        } },
        .results = &.{ has_value, normalized_limit, normalized_step, next_control },
        .effects = .numeric_for_next,
    }};
    const program = ir.Program{
        .program_id = "empty-numeric-forwarder-reentry",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);
    var visited = [_]bool{ false, true, false, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, null, null, null };
    const context = Builder.VisitContext{
        .start = forwarder,
        .stop = stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &.{},
    };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const edge = ir.CfgEdgeRef{ .source = incoming, .kind = .jump, .target = forwarder };

    try std.testing.expect(try builder.authenticatedEmptyNumericForwarderReentry(
        forwarder,
        entry,
        stop,
        context,
        true,
        edge,
    ));

    blocks[incoming.index()].terminator = .{ .jump = .{ .target = stop } };
    try std.testing.expect(!(try builder.authenticatedEmptyNumericForwarderReentry(
        forwarder,
        entry,
        stop,
        context,
        true,
        edge,
    )));
    blocks[incoming.index()].terminator = .{ .jump = .{ .target = forwarder } };

    blocks[forwarder.index()].terminator = .{ .jump = .{ .target = stop, .arguments = &tuple } };
    try std.testing.expect(!(try builder.authenticatedEmptyNumericForwarderReentry(
        forwarder,
        entry,
        stop,
        context,
        true,
        edge,
    )));
    blocks[forwarder.index()].terminator = .{ .jump = .{ .target = header, .arguments = &tuple } };

    blocks[incoming.index()].terminator = .{ .jump = .{ .target = forwarder, .arguments = &.{control} } };
    try std.testing.expect(!(try builder.authenticatedEmptyNumericForwarderReentry(
        forwarder,
        entry,
        stop,
        context,
        true,
        edge,
    )));
}

test "parameterized continuation composes after an authenticated prefix" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner_stop = ir.BlockId.fromIndex(1);
    const prefix = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const incoming_stop = ir.BlockId.fromIndex(4);
    const loop_exit = ir.BlockId.fromIndex(5);
    const incoming_continue = ir.BlockId.fromIndex(6);
    const owner_continue = ir.BlockId.fromIndex(7);
    const original = ir.BlockId.fromIndex(8);
    const condition = ir.ValueId.fromIndex(0);
    const argument = ir.ValueId.fromIndex(1);
    const target_parameter = ir.ValueId.fromIndex(2);
    const original_parameter = ir.ValueId.fromIndex(3);
    const arguments = [_]ir.ValueId{argument};

    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = owner_stop },
            .else_edge = .{ .target = prefix },
        } } },
        .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = prefix, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &arguments,
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{target_parameter}, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = incoming_stop },
            .else_edge = .{ .target = loop_exit },
        } } },
        .{ .id = incoming_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = loop_exit, .function = function_id, .terminator = .{ .jump = .{ .target = incoming_continue } } },
        .{ .id = incoming_continue, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = owner_continue, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original, .function = function_id, .parameters = &.{original_parameter}, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = incoming_stop },
            .else_edge = .{ .target = loop_exit },
        } } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ condition, argument },
        .blocks = &.{ entry, owner_stop, prefix, target, incoming_stop, loop_exit, incoming_continue, owner_continue, original },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = argument, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = target_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = original_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = original, .index = 0 } } },
    };
    var rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = prefix,
        .kind = .jump,
        .from = .{ .target = original, .arguments = &arguments },
        .to = .{ .target = target, .arguments = &arguments },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    var program = ir.Program{
        .program_id = "parameterized-continuation-prefix-composition",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, false, false, true, false, false, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, .{
        .start = target,
        .stop = owner_stop,
        .loop_exit = loop_exit,
        .continue_target = owner_continue,
        .parameter_arguments = &arguments,
    }, null, null, null, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const incoming_reference = ir.CfgEdgeRef{
        .source = prefix,
        .kind = .jump,
        .target = target,
    };
    const parameters_match = try builder.parameterProjectionMatches(
        target,
        &arguments,
        &arguments,
    );
    try std.testing.expect(parameters_match);
    const bridge_authenticated = try builder.hasAuthenticatedContinuationBridge(incoming_reference);
    try std.testing.expect(bridge_authenticated);

    // The same authenticated edge must also be rejected when the owner is
    // not in the incoming edge's SCC.  Add a backedge for the positive
    // witness, then reuse the original acyclic graph as the negative case.
    var scc_blocks = blocks;
    scc_blocks[target.index()].terminator = .{ .branch = .{
        .condition = condition,
        .then_edge = .{ .target = prefix, .arguments = &.{} },
        .else_edge = .{ .target = loop_exit },
    } };
    var scc_program = program;
    scc_program.blocks = &scc_blocks;
    var scc_analysis = try cfg.Analysis.init(std.testing.allocator, &scc_program, function);
    defer scc_analysis.deinit();
    var scc_visited = visited;
    var scc_contexts = contexts;
    scc_contexts[target.index()] = .{
        .start = owner_stop,
        .stop = owner_stop,
        .loop_exit = loop_exit,
        .continue_target = incoming_continue,
        .parameter_arguments = &arguments,
        .entry_reference = incoming_reference,
    };
    var scc_builder = builder;
    scc_builder.analysis = &scc_analysis;
    scc_builder.visited = &scc_visited;
    scc_builder.visited_contexts = &scc_contexts;
    try std.testing.expect(try scc_builder.authenticatedSameSccParameterizedReentry(
        target,
        target,
        loop_exit,
        incoming_continue,
        scc_contexts[target.index()].?,
        parameters_match,
        incoming_reference,
    ));

    var acyclic_contexts = scc_contexts;
    var acyclic_builder = builder;
    acyclic_builder.visited_contexts = &acyclic_contexts;
    try std.testing.expect(!try acyclic_builder.authenticatedSameSccParameterizedReentry(
        target,
        target,
        loop_exit,
        incoming_continue,
        acyclic_contexts[target.index()].?,
        parameters_match,
        incoming_reference,
    ));

    const prefix_projection_authenticated = try builder.authenticatedVisitedParameterizedContinuationProjection(
        target,
        prefix,
        incoming_stop,
        loop_exit,
        incoming_continue,
        contexts[target.index()].?,
        parameters_match,
        &arguments,
        incoming_reference,
        true,
        true,
    );
    try std.testing.expect(prefix_projection_authenticated);
    const projected = try builder.buildRegionImplWithEntryArguments(
        prefix,
        incoming_stop,
        null,
        loop_exit,
        null,
        null,
        false,
        incoming_continue,
        &arguments,
    );
    defer destroyRegion(std.testing.allocator, projected);
    try std.testing.expectEqual(@as(usize, 1), projected.nodes.len);
    try std.testing.expectEqual(prefix, projected.nodes[0].blockId());
    try std.testing.expect(projected.escape_projection != null);
    try std.testing.expectEqual(target, projected.escape_projection.?.target);

    var tampered_arguments = arguments;
    tampered_arguments[0] = condition;
    blocks[prefix.index()].terminator = .{ .jump = .{
        .target = target,
        .arguments = &tampered_arguments,
    } };
    program.blocks = &blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer tampered_analysis.deinit();
    var rejected_visited = [_]bool{ false, false, false, true, false, false, false, false, false };
    var rejected_contexts = [_]?Builder.VisitContext{ null, null, null, .{
        .start = target,
        .stop = owner_stop,
        .loop_exit = loop_exit,
        .continue_target = owner_continue,
        .parameter_arguments = &arguments,
    }, null, null, null, null, null };
    var rejected_builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &tampered_analysis,
        .visited = &rejected_visited,
        .visited_contexts = &rejected_contexts,
        .loop_headers = loop_headers,
    };
    try std.testing.expectError(
        error.UnsupportedShape,
        rejected_builder.buildRegionImplWithEntryArguments(
            prefix,
            incoming_stop,
            null,
            loop_exit,
            null,
            null,
            false,
            incoming_continue,
            &tampered_arguments,
        ),
    );
}

test "parameterized continuation composes across a prefixed four-value header pair" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const prefix = ir.BlockId.fromIndex(1);
    const owner = ir.BlockId.fromIndex(2);
    const bridge = ir.BlockId.fromIndex(3);
    const original = ir.BlockId.fromIndex(4);
    const current = ir.BlockId.fromIndex(5);
    const suffix = ir.BlockId.fromIndex(6);
    const continuation = ir.BlockId.fromIndex(7);
    const terminal = ir.BlockId.fromIndex(8);

    const selector = ir.ValueId.fromIndex(0);
    const argument_1 = ir.ValueId.fromIndex(1);
    const argument_2 = ir.ValueId.fromIndex(2);
    const argument_3 = ir.ValueId.fromIndex(3);
    const argument_4 = ir.ValueId.fromIndex(4);
    const owner_parameter_1 = ir.ValueId.fromIndex(5);
    const owner_parameter_2 = ir.ValueId.fromIndex(6);
    const owner_parameter_3 = ir.ValueId.fromIndex(7);
    const owner_parameter_4 = ir.ValueId.fromIndex(8);
    const original_parameter_1 = ir.ValueId.fromIndex(9);
    const original_parameter_2 = ir.ValueId.fromIndex(10);
    const original_parameter_3 = ir.ValueId.fromIndex(11);
    const original_parameter_4 = ir.ValueId.fromIndex(12);
    const current_parameter_1 = ir.ValueId.fromIndex(13);
    const current_parameter_2 = ir.ValueId.fromIndex(14);
    const current_parameter_3 = ir.ValueId.fromIndex(15);
    const current_parameter_4 = ir.ValueId.fromIndex(16);
    const suffix_parameter_1 = ir.ValueId.fromIndex(17);
    const suffix_parameter_2 = ir.ValueId.fromIndex(18);
    const suffix_parameter_3 = ir.ValueId.fromIndex(19);
    const suffix_parameter_4 = ir.ValueId.fromIndex(20);

    const arguments = [_]ir.ValueId{ selector, argument_1, argument_2, argument_3 };
    const owner_parameters = [_]ir.ValueId{
        owner_parameter_1,
        owner_parameter_2,
        owner_parameter_3,
        owner_parameter_4,
    };
    const original_parameters = [_]ir.ValueId{
        original_parameter_1,
        original_parameter_2,
        original_parameter_3,
        original_parameter_4,
    };
    const current_parameters = [_]ir.ValueId{
        current_parameter_1,
        current_parameter_2,
        current_parameter_3,
        current_parameter_4,
    };
    const suffix_parameters = [_]ir.ValueId{
        suffix_parameter_1,
        suffix_parameter_2,
        suffix_parameter_3,
        suffix_parameter_4,
    };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = prefix },
            .else_edge = .{ .target = original, .arguments = &arguments },
        } } },
        .{ .id = prefix, .function = function_id, .terminator = .{ .jump = .{
            .target = owner,
            .arguments = &arguments,
        } } },
        .{ .id = owner, .function = function_id, .parameters = &owner_parameters, .terminator = .{ .jump = .{
            .target = bridge,
            .arguments = &owner_parameters,
        } } },
        .{ .id = bridge, .function = function_id, .terminator = .{ .jump = .{
            .target = current,
            .arguments = &arguments,
        } } },
        .{ .id = original, .function = function_id, .parameters = &original_parameters, .terminator = .{ .jump = .{
            .target = suffix,
            .arguments = &original_parameters,
        } } },
        .{ .id = current, .function = function_id, .parameters = &current_parameters, .terminator = .{ .jump = .{
            .target = suffix,
            .arguments = &current_parameters,
        } } },
        .{ .id = suffix, .function = function_id, .parameters = &suffix_parameters, .terminator = .{ .jump = .{
            .target = continuation,
            .arguments = &suffix_parameters,
        } } },
        .{ .id = continuation, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ selector, argument_1, argument_2, argument_3, argument_4 },
        .blocks = &.{ entry, prefix, owner, bridge, original, current, suffix, continuation, terminal },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = argument_1, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = argument_2, .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = argument_3, .function = function_id, .type = .integer, .origin = .{ .parameter = 3 } },
        .{ .id = argument_4, .function = function_id, .type = .integer, .origin = .{ .parameter = 4 } },
        .{ .id = owner_parameter_1, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = owner, .index = 0 } } },
        .{ .id = owner_parameter_2, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = owner, .index = 1 } } },
        .{ .id = owner_parameter_3, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = owner, .index = 2 } } },
        .{ .id = owner_parameter_4, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = owner, .index = 3 } } },
        .{ .id = original_parameter_1, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = original, .index = 0 } } },
        .{ .id = original_parameter_2, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = original, .index = 1 } } },
        .{ .id = original_parameter_3, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = original, .index = 2 } } },
        .{ .id = original_parameter_4, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = original, .index = 3 } } },
        .{ .id = current_parameter_1, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = current, .index = 0 } } },
        .{ .id = current_parameter_2, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = current, .index = 1 } } },
        .{ .id = current_parameter_3, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = current, .index = 2 } } },
        .{ .id = current_parameter_4, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = current, .index = 3 } } },
        .{ .id = suffix_parameter_1, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = suffix, .index = 0 } } },
        .{ .id = suffix_parameter_2, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = suffix, .index = 1 } } },
        .{ .id = suffix_parameter_3, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = suffix, .index = 2 } } },
        .{ .id = suffix_parameter_4, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = suffix, .index = 3 } } },
    };
    var rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = bridge,
        .kind = .jump,
        .from = .{ .target = original, .arguments = &arguments },
        .to = .{ .target = current, .arguments = &arguments },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    var program = ir.Program{
        .program_id = "prefixed-four-value-continuation-composition",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, false, false, false, false, true, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, null, null, .{
        .start = owner,
        .stop = suffix,
        .loop_exit = null,
        .continue_target = continuation,
        .parameter_arguments = &arguments,
    }, null, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const incoming = ir.CfgEdgeRef{ .source = bridge, .kind = .jump, .target = current };
    try std.testing.expect(try builder.parameterProjectionMatches(current, &arguments, &arguments));
    try std.testing.expect(try builder.hasAuthenticatedContinuationBridge(incoming));
    try std.testing.expect(try builder.authenticatedVisitedParameterizedContinuationProjection(
        current,
        prefix,
        suffix,
        null,
        continuation,
        contexts[current.index()].?,
        true,
        &arguments,
        incoming,
        true,
        true,
    ));

    var tampered_arguments = arguments;
    tampered_arguments[2] = argument_4;
    var tampered_blocks = blocks;
    tampered_blocks[bridge.index()].terminator = .{ .jump = .{
        .target = current,
        .arguments = &tampered_arguments,
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, function);
    defer tampered_analysis.deinit();
    var tampered_builder = builder;
    tampered_builder.analysis = &tampered_analysis;
    try std.testing.expect(!(try tampered_builder.authenticatedVisitedParameterizedContinuationProjection(
        current,
        prefix,
        suffix,
        null,
        continuation,
        contexts[current.index()].?,
        true,
        &arguments,
        incoming,
        true,
        true,
    )));

    var tampered_rewrite_arguments = arguments;
    tampered_rewrite_arguments[1] = argument_4;
    var tampered_rewrites = rewrites;
    tampered_rewrites[0].from.arguments = &tampered_rewrite_arguments;
    var tampered_rewrite_program = program;
    tampered_rewrite_program.edge_rewrites = &tampered_rewrites;
    var tampered_rewrite_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &tampered_rewrite_program,
        function,
    );
    defer tampered_rewrite_analysis.deinit();
    var tampered_rewrite_builder = builder;
    tampered_rewrite_builder.analysis = &tampered_rewrite_analysis;
    try std.testing.expect(!(try tampered_rewrite_builder.authenticatedVisitedParameterizedContinuationProjection(
        current,
        prefix,
        suffix,
        null,
        continuation,
        contexts[current.index()].?,
        true,
        &arguments,
        incoming,
        true,
        true,
    )));

    var bypass_blocks = blocks;
    bypass_blocks[current.index()].terminator = .{ .jump = .{
        .target = owner,
        .arguments = &current_parameters,
    } };
    var bypass_program = program;
    bypass_program.blocks = &bypass_blocks;
    var bypass_analysis = try cfg.Analysis.init(std.testing.allocator, &bypass_program, function);
    defer bypass_analysis.deinit();
    var bypass_builder = builder;
    bypass_builder.analysis = &bypass_analysis;
    try std.testing.expect(!(try bypass_builder.authenticatedVisitedParameterizedContinuationProjection(
        current,
        prefix,
        suffix,
        null,
        continuation,
        contexts[current.index()].?,
        true,
        &arguments,
        incoming,
        true,
        true,
    )));

    {
        const replay_constant = ir.InstructionId.fromIndex(0);
        const replay_write = ir.InstructionId.fromIndex(1);
        const effect_value = ir.ValueId.fromIndex(21);
        const replay_place = ir.PlaceId.fromIndex(0);

        const replay_instructions = [_]ir.Instruction{
            .{ .id = replay_constant, .block = current, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{effect_value}, .effects = .pure },
            .{ .id = replay_write, .block = current, .operation = .{ .place_write = .{ .place = replay_place, .value = effect_value } }, .results = &.{}, .effects = .place_write },
        };
        const replay_values = values ++ [_]ir.Value{
            .{ .id = effect_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = replay_constant, .index = 0 } } },
        };
        var replay_blocks = blocks;
        replay_blocks[current.index()].instructions = &.{ replay_constant, replay_write };
        var replay_program = program;
        replay_program.blocks = &replay_blocks;
        replay_program.instructions = &replay_instructions;
        replay_program.values = &replay_values;
        replay_program.places = &.{.{ .id = replay_place, .function = function_id, .type = .integer, .origin = .{ .local = 0 } }};

        var replay_analysis = try cfg.Analysis.init(std.testing.allocator, &replay_program, function);
        defer replay_analysis.deinit();
        var replay_visited = visited;
        var replay_contexts = contexts;
        replay_contexts[current.index()] = .{
            .start = current,
            .stop = continuation,
            .loop_exit = null,
            .continue_target = null,
            .parameter_arguments = &arguments,
        };
        var replay_builder = builder;
        replay_builder.analysis = &replay_analysis;
        replay_builder.visited = &replay_visited;
        replay_builder.visited_contexts = &replay_contexts;
        const replay = (try replay_builder.authenticatedEffectfulTerminalReplay(
            current,
            current,
            suffix,
            &arguments,
            incoming,
        )) orelse return error.TestUnexpectedResult;
        defer replay_builder.allocator.free(replay.nodes);
        try std.testing.expectEqual(@as(usize, 1), replay.nodes.len);
        try std.testing.expectEqual(current, replay.nodes[0].blockId());
        try std.testing.expect(replay.terminal == null);

        var replay_tampered_arguments = arguments;
        replay_tampered_arguments[0] = argument_4;
        var replay_tampered_blocks = replay_blocks;
        replay_tampered_blocks[bridge.index()].terminator = .{ .jump = .{
            .target = current,
            .arguments = &replay_tampered_arguments,
        } };
        var replay_tampered_program = replay_program;
        replay_tampered_program.blocks = &replay_tampered_blocks;
        var replay_tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &replay_tampered_program, function);
        defer replay_tampered_analysis.deinit();
        var replay_tampered_builder = replay_builder;
        replay_tampered_builder.analysis = &replay_tampered_analysis;
        try std.testing.expect((try replay_tampered_builder.authenticatedEffectfulTerminalReplay(
            current,
            current,
            suffix,
            &replay_tampered_arguments,
            incoming,
        )) == null);

        var replay_unauthenticated_rewrites = rewrites;
        replay_unauthenticated_rewrites[0].source = prefix;
        var replay_unauthenticated_program = replay_program;
        replay_unauthenticated_program.edge_rewrites = &replay_unauthenticated_rewrites;
        var replay_unauthenticated_analysis = try cfg.Analysis.init(std.testing.allocator, &replay_unauthenticated_program, function);
        defer replay_unauthenticated_analysis.deinit();
        var replay_unauthenticated_builder = replay_builder;
        replay_unauthenticated_builder.analysis = &replay_unauthenticated_analysis;
        try std.testing.expect((try replay_unauthenticated_builder.authenticatedEffectfulTerminalReplay(
            current,
            current,
            suffix,
            &arguments,
            incoming,
        )) == null);
    }
}

test "effectful parameterized replay rebinds distinct canonical incoming tuples" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const incoming = ir.BlockId.fromIndex(2);
    const current = ir.BlockId.fromIndex(3);
    const suffix = ir.BlockId.fromIndex(4);
    const stop = ir.BlockId.fromIndex(5);
    const owner_stop = ir.BlockId.fromIndex(6);

    const selector = ir.ValueId.fromIndex(0);
    const owner_first = ir.ValueId.fromIndex(1);
    const owner_second = ir.ValueId.fromIndex(2);
    const owner_third = ir.ValueId.fromIndex(3);
    const owner_fourth = ir.ValueId.fromIndex(4);
    const incoming_first = ir.ValueId.fromIndex(5);
    const incoming_second = ir.ValueId.fromIndex(6);
    const incoming_third = ir.ValueId.fromIndex(7);
    const incoming_fourth = ir.ValueId.fromIndex(8);
    const formal_first = ir.ValueId.fromIndex(9);
    const formal_second = ir.ValueId.fromIndex(10);
    const formal_third = ir.ValueId.fromIndex(11);
    const formal_fourth = ir.ValueId.fromIndex(12);
    const stop_first = ir.ValueId.fromIndex(13);
    const stop_second = ir.ValueId.fromIndex(14);
    const stop_third = ir.ValueId.fromIndex(15);
    const stop_fourth = ir.ValueId.fromIndex(16);
    const effect_value = ir.ValueId.fromIndex(17);
    const copied_formal = ir.ValueId.fromIndex(18);

    const effect_constant = ir.InstructionId.fromIndex(0);
    const effect_write = ir.InstructionId.fromIndex(1);
    const copy_formal = ir.InstructionId.fromIndex(2);
    const boundary_copy = ir.InstructionId.fromIndex(3);
    const owner_arguments = [_]ir.ValueId{ owner_first, owner_second, owner_third, owner_fourth };
    const incoming_arguments = [_]ir.ValueId{ incoming_first, incoming_second, incoming_third, incoming_fourth };
    const current_parameters = [_]ir.ValueId{ formal_first, formal_second, formal_third, formal_fourth };
    const stop_parameters = [_]ir.ValueId{ stop_first, stop_second, stop_third, stop_fourth };
    const function_parameters = [_]ir.ValueId{
        selector,
        owner_first,
        owner_second,
        owner_third,
        owner_fourth,
        incoming_first,
        incoming_second,
        incoming_third,
        incoming_fourth,
    };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = incoming },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{
            .target = current,
            .arguments = &owner_arguments,
        } } },
        .{ .id = incoming, .function = function_id, .terminator = .{ .jump = .{
            .target = current,
            .arguments = &incoming_arguments,
        } } },
        .{ .id = current, .function = function_id, .parameters = &current_parameters, .instructions = &.{ effect_constant, effect_write }, .terminator = .{ .jump = .{
            .target = suffix,
        } } },
        .{ .id = suffix, .function = function_id, .terminator = .{ .jump = .{
            .target = stop,
            .arguments = &current_parameters,
        } } },
        .{ .id = stop, .function = function_id, .parameters = &stop_parameters, .terminator = .{ .return_values = &.{} } },
        .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &function_parameters,
        .blocks = &.{ entry, owner, incoming, current, suffix, stop, owner_stop },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = owner_first, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = owner_second, .function = function_id, .origin = .{ .parameter = 2 } },
        .{ .id = owner_third, .function = function_id, .origin = .{ .parameter = 3 } },
        .{ .id = owner_fourth, .function = function_id, .origin = .{ .parameter = 4 } },
        .{ .id = incoming_first, .function = function_id, .origin = .{ .parameter = 5 } },
        .{ .id = incoming_second, .function = function_id, .origin = .{ .parameter = 6 } },
        .{ .id = incoming_third, .function = function_id, .origin = .{ .parameter = 7 } },
        .{ .id = incoming_fourth, .function = function_id, .origin = .{ .parameter = 8 } },
        .{ .id = formal_first, .function = function_id, .origin = .{ .block_parameter = .{ .block = current, .index = 0 } } },
        .{ .id = formal_second, .function = function_id, .origin = .{ .block_parameter = .{ .block = current, .index = 1 } } },
        .{ .id = formal_third, .function = function_id, .origin = .{ .block_parameter = .{ .block = current, .index = 2 } } },
        .{ .id = formal_fourth, .function = function_id, .origin = .{ .block_parameter = .{ .block = current, .index = 3 } } },
        .{ .id = stop_first, .function = function_id, .origin = .{ .block_parameter = .{ .block = stop, .index = 0 } } },
        .{ .id = stop_second, .function = function_id, .origin = .{ .block_parameter = .{ .block = stop, .index = 1 } } },
        .{ .id = stop_third, .function = function_id, .origin = .{ .block_parameter = .{ .block = stop, .index = 2 } } },
        .{ .id = stop_fourth, .function = function_id, .origin = .{ .block_parameter = .{ .block = stop, .index = 3 } } },
        .{ .id = effect_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = effect_constant, .index = 0 } } },
        .{ .id = copied_formal, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = copy_formal, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = effect_constant, .block = current, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{effect_value}, .effects = .pure },
        .{ .id = effect_write, .block = current, .operation = .{ .place_write = .{ .place = ir.PlaceId.fromIndex(0), .value = effect_value } }, .results = &.{}, .effects = .place_write },
        .{ .id = copy_formal, .block = current, .operation = .{ .copy = formal_first }, .results = &.{copied_formal}, .effects = .pure },
    };
    const places = [_]ir.Place{.{
        .id = ir.PlaceId.fromIndex(0),
        .function = function_id,
        .origin = .{ .local = 0 },
    }};
    var program = ir.Program{
        .program_id = "parameterized-effectful-rebind",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);
    var visited = [_]bool{ false, false, false, true, true, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, .{
        .start = current,
        .stop = owner_stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &owner_arguments,
    }, null, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const incoming_reference = ir.CfgEdgeRef{ .source = incoming, .kind = .jump, .target = current };
    const replay = (try builder.authenticatedEffectfulTerminalReplay(
        current,
        current,
        stop,
        &incoming_arguments,
        incoming_reference,
    )) orelse return error.TestUnexpectedResult;
    defer builder.allocator.free(replay.nodes);
    try std.testing.expectEqual(@as(usize, 2), replay.nodes.len);
    try std.testing.expectEqual(current, replay.nodes[0].blockId());
    try std.testing.expectEqual(suffix, replay.nodes[1].blockId());

    const boundary_value = ir.ValueId.fromIndex(19);
    var boundary_blocks = blocks;
    boundary_blocks[stop.index()].instructions = &.{boundary_copy};
    const boundary_instructions = instructions ++ [_]ir.Instruction{.{
        .id = boundary_copy,
        .block = stop,
        .operation = .{ .copy = effect_value },
        .results = &.{boundary_value},
        .effects = .pure,
    }};
    const boundary_values = values ++ [_]ir.Value{.{
        .id = boundary_value,
        .function = function_id,
        .type = .integer,
        .origin = .{ .instruction_result = .{ .instruction = boundary_copy, .index = 0 } },
    }};
    var boundary_program = program;
    boundary_program.blocks = &boundary_blocks;
    boundary_program.instructions = &boundary_instructions;
    boundary_program.values = &boundary_values;
    var boundary_analysis = try cfg.Analysis.init(std.testing.allocator, &boundary_program, function);
    defer boundary_analysis.deinit();
    var boundary_builder = builder;
    boundary_builder.analysis = &boundary_analysis;
    try std.testing.expect((try boundary_builder.authenticatedEffectfulTerminalReplay(
        current,
        current,
        stop,
        &incoming_arguments,
        incoming_reference,
    )) == null);

    var parameter_use_blocks = blocks;
    parameter_use_blocks[current.index()].instructions = &.{copy_formal};
    var parameter_use_program = program;
    parameter_use_program.blocks = &parameter_use_blocks;
    var parameter_use_analysis = try cfg.Analysis.init(std.testing.allocator, &parameter_use_program, function);
    defer parameter_use_analysis.deinit();
    var parameter_use_builder = builder;
    parameter_use_builder.analysis = &parameter_use_analysis;
    try std.testing.expect((try parameter_use_builder.authenticatedEffectfulTerminalReplay(
        current,
        current,
        stop,
        &incoming_arguments,
        incoming_reference,
    )) == null);

    var wrong_terminal_blocks = blocks;
    wrong_terminal_blocks[suffix.index()].terminator = .{ .jump = .{
        .target = stop,
        .arguments = &incoming_arguments,
    } };
    var wrong_terminal_program = program;
    wrong_terminal_program.blocks = &wrong_terminal_blocks;
    var wrong_terminal_analysis = try cfg.Analysis.init(std.testing.allocator, &wrong_terminal_program, function);
    defer wrong_terminal_analysis.deinit();
    var wrong_terminal_builder = builder;
    wrong_terminal_builder.analysis = &wrong_terminal_analysis;
    try std.testing.expect((try wrong_terminal_builder.authenticatedEffectfulTerminalReplay(
        current,
        current,
        stop,
        &incoming_arguments,
        incoming_reference,
    )) == null);

    var missing_owner_blocks = blocks;
    missing_owner_blocks[owner.index()].terminator = .{ .return_values = &.{} };
    var missing_owner_program = program;
    missing_owner_program.blocks = &missing_owner_blocks;
    var missing_owner_analysis = try cfg.Analysis.init(std.testing.allocator, &missing_owner_program, function);
    defer missing_owner_analysis.deinit();
    var missing_owner_builder = builder;
    missing_owner_builder.analysis = &missing_owner_analysis;
    try std.testing.expect((try missing_owner_builder.authenticatedEffectfulTerminalReplay(
        current,
        current,
        stop,
        &incoming_arguments,
        incoming_reference,
    )) == null);
}

test "effectful parameterized prefix replay hands off before a branch" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const incoming = ir.BlockId.fromIndex(2);
    const current = ir.BlockId.fromIndex(3);
    const prefix = ir.BlockId.fromIndex(4);
    const branch = ir.BlockId.fromIndex(5);
    const then_block = ir.BlockId.fromIndex(6);
    const else_block = ir.BlockId.fromIndex(7);
    const owner_stop = ir.BlockId.fromIndex(8);

    const selector = ir.ValueId.fromIndex(0);
    const owner_first = ir.ValueId.fromIndex(1);
    const owner_second = ir.ValueId.fromIndex(2);
    const owner_third = ir.ValueId.fromIndex(3);
    const owner_fourth = ir.ValueId.fromIndex(4);
    const incoming_first = ir.ValueId.fromIndex(5);
    const incoming_second = ir.ValueId.fromIndex(6);
    const incoming_third = ir.ValueId.fromIndex(7);
    const incoming_fourth = ir.ValueId.fromIndex(8);
    const formal_first = ir.ValueId.fromIndex(9);
    const formal_second = ir.ValueId.fromIndex(10);
    const formal_third = ir.ValueId.fromIndex(11);
    const formal_fourth = ir.ValueId.fromIndex(12);
    const effect_value = ir.ValueId.fromIndex(13);
    const prefix_value = ir.ValueId.fromIndex(14);
    const copied_formal = ir.ValueId.fromIndex(15);

    const effect_constant = ir.InstructionId.fromIndex(0);
    const effect_write = ir.InstructionId.fromIndex(1);
    const prefix_constant = ir.InstructionId.fromIndex(2);
    const prefix_write = ir.InstructionId.fromIndex(3);
    const copy_formal = ir.InstructionId.fromIndex(4);
    const owner_arguments = [_]ir.ValueId{ owner_first, owner_second, owner_third, owner_fourth };
    const incoming_arguments = [_]ir.ValueId{ incoming_first, incoming_second, incoming_third, incoming_fourth };
    const current_parameters = [_]ir.ValueId{ formal_first, formal_second, formal_third, formal_fourth };
    const function_parameters = [_]ir.ValueId{
        selector,
        owner_first,
        owner_second,
        owner_third,
        owner_fourth,
        incoming_first,
        incoming_second,
        incoming_third,
        incoming_fourth,
    };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = incoming },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{
            .target = current,
            .arguments = &owner_arguments,
        } } },
        .{ .id = incoming, .function = function_id, .terminator = .{ .jump = .{
            .target = current,
            .arguments = &incoming_arguments,
        } } },
        .{ .id = current, .function = function_id, .parameters = &current_parameters, .instructions = &.{ effect_constant, effect_write }, .terminator = .{ .jump = .{
            .target = prefix,
        } } },
        .{ .id = prefix, .function = function_id, .instructions = &.{ prefix_constant, prefix_write }, .terminator = .{ .jump = .{
            .target = branch,
        } } },
        .{ .id = branch, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = then_block },
            .else_edge = .{ .target = else_block },
        } } },
        .{ .id = then_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = else_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &function_parameters,
        .blocks = &.{ entry, owner, incoming, current, prefix, branch, then_block, else_block, owner_stop },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = owner_first, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = owner_second, .function = function_id, .origin = .{ .parameter = 2 } },
        .{ .id = owner_third, .function = function_id, .origin = .{ .parameter = 3 } },
        .{ .id = owner_fourth, .function = function_id, .origin = .{ .parameter = 4 } },
        .{ .id = incoming_first, .function = function_id, .origin = .{ .parameter = 5 } },
        .{ .id = incoming_second, .function = function_id, .origin = .{ .parameter = 6 } },
        .{ .id = incoming_third, .function = function_id, .origin = .{ .parameter = 7 } },
        .{ .id = incoming_fourth, .function = function_id, .origin = .{ .parameter = 8 } },
        .{ .id = formal_first, .function = function_id, .origin = .{ .block_parameter = .{ .block = current, .index = 0 } } },
        .{ .id = formal_second, .function = function_id, .origin = .{ .block_parameter = .{ .block = current, .index = 1 } } },
        .{ .id = formal_third, .function = function_id, .origin = .{ .block_parameter = .{ .block = current, .index = 2 } } },
        .{ .id = formal_fourth, .function = function_id, .origin = .{ .block_parameter = .{ .block = current, .index = 3 } } },
        .{ .id = effect_value, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = effect_constant, .index = 0 } } },
        .{ .id = prefix_value, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = prefix_constant, .index = 0 } } },
        .{ .id = copied_formal, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = copy_formal, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = effect_constant, .block = current, .operation = .{ .constant = .{ .number = 1 } }, .results = &.{effect_value}, .effects = .pure },
        .{ .id = effect_write, .block = current, .operation = .{ .place_write = .{ .place = ir.PlaceId.fromIndex(0), .value = effect_value } }, .results = &.{}, .effects = .place_write },
        .{ .id = prefix_constant, .block = prefix, .operation = .{ .constant = .{ .number = 2 } }, .results = &.{prefix_value}, .effects = .pure },
        .{ .id = prefix_write, .block = prefix, .operation = .{ .place_write = .{ .place = ir.PlaceId.fromIndex(0), .value = prefix_value } }, .results = &.{}, .effects = .place_write },
        .{ .id = copy_formal, .block = current, .operation = .{ .copy = formal_first }, .results = &.{copied_formal}, .effects = .pure },
    };
    const places = [_]ir.Place{.{
        .id = ir.PlaceId.fromIndex(0),
        .function = function_id,
        .type = .number,
        .origin = .{ .local = 0 },
    }};
    var program = ir.Program{
        .program_id = "parameterized-effectful-prefix-replay",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);

    var visited = [_]bool{ false, false, false, true, true, false, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, .{
        .start = current,
        .stop = owner_stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &owner_arguments,
    }, null, null, null, null, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const incoming_reference = ir.CfgEdgeRef{ .source = incoming, .kind = .jump, .target = current };
    const replay = (try builder.authenticatedEffectfulPrefixReplay(
        current,
        incoming,
        else_block,
        contexts[current.index()].?,
        &incoming_arguments,
        incoming_reference,
    )) orelse return error.TestUnexpectedResult;
    defer builder.allocator.free(replay.nodes);
    try std.testing.expectEqual(@as(usize, 2), replay.nodes.len);
    try std.testing.expectEqual(current, replay.nodes[0].blockId());
    try std.testing.expectEqual(prefix, replay.nodes[1].blockId());
    try std.testing.expectEqual(prefix, replay.source);
    try std.testing.expectEqual(branch, replay.next);
    try std.testing.expectEqual(@as(usize, 0), replay.arguments.len);

    var parameter_use_blocks = blocks;
    parameter_use_blocks[current.index()].instructions = &.{copy_formal};
    var parameter_use_program = program;
    parameter_use_program.blocks = &parameter_use_blocks;
    var parameter_use_analysis = try cfg.Analysis.init(std.testing.allocator, &parameter_use_program, function);
    defer parameter_use_analysis.deinit();
    var parameter_use_builder = builder;
    parameter_use_builder.analysis = &parameter_use_analysis;
    try std.testing.expect((try parameter_use_builder.authenticatedEffectfulPrefixReplay(
        current,
        incoming,
        else_block,
        contexts[current.index()].?,
        &incoming_arguments,
        incoming_reference,
    )) == null);

    var no_effect_blocks = blocks;
    no_effect_blocks[current.index()].instructions = &.{effect_constant};
    no_effect_blocks[prefix.index()].instructions = &.{prefix_constant};
    var no_effect_program = program;
    no_effect_program.blocks = &no_effect_blocks;
    var no_effect_analysis = try cfg.Analysis.init(std.testing.allocator, &no_effect_program, function);
    defer no_effect_analysis.deinit();
    var no_effect_builder = builder;
    no_effect_builder.analysis = &no_effect_analysis;
    try std.testing.expect((try no_effect_builder.authenticatedEffectfulPrefixReplay(
        current,
        incoming,
        else_block,
        contexts[current.index()].?,
        &incoming_arguments,
        incoming_reference,
    )) == null);

    var dependent_branch_blocks = blocks;
    dependent_branch_blocks[branch.index()].terminator = .{ .branch = .{
        .condition = formal_first,
        .then_edge = .{ .target = then_block },
        .else_edge = .{ .target = else_block },
    } };
    var dependent_branch_program = program;
    dependent_branch_program.blocks = &dependent_branch_blocks;
    var dependent_branch_analysis = try cfg.Analysis.init(std.testing.allocator, &dependent_branch_program, function);
    defer dependent_branch_analysis.deinit();
    var dependent_branch_builder = builder;
    dependent_branch_builder.analysis = &dependent_branch_analysis;
    try std.testing.expect((try dependent_branch_builder.authenticatedEffectfulPrefixReplay(
        current,
        incoming,
        else_block,
        contexts[current.index()].?,
        &incoming_arguments,
        incoming_reference,
    )) == null);

    var cyclic_blocks = blocks;
    cyclic_blocks[prefix.index()].terminator = .{ .jump = .{ .target = prefix } };
    var cyclic_program = program;
    cyclic_program.blocks = &cyclic_blocks;
    var cyclic_analysis = try cfg.Analysis.init(std.testing.allocator, &cyclic_program, function);
    defer cyclic_analysis.deinit();
    var cyclic_builder = builder;
    cyclic_builder.analysis = &cyclic_analysis;
    try std.testing.expect((try cyclic_builder.authenticatedEffectfulPrefixReplay(
        current,
        incoming,
        else_block,
        contexts[current.index()].?,
        &incoming_arguments,
        incoming_reference,
    )) == null);

    var invalid_tuple = incoming_arguments;
    invalid_tuple[0] = owner_first;
    var invalid_tuple_blocks = blocks;
    invalid_tuple_blocks[incoming.index()].terminator = .{ .jump = .{
        .target = current,
        .arguments = &invalid_tuple,
    } };
    var invalid_tuple_program = program;
    invalid_tuple_program.blocks = &invalid_tuple_blocks;
    var invalid_tuple_analysis = try cfg.Analysis.init(std.testing.allocator, &invalid_tuple_program, function);
    defer invalid_tuple_analysis.deinit();
    var invalid_tuple_builder = builder;
    invalid_tuple_builder.analysis = &invalid_tuple_analysis;
    try std.testing.expect((try invalid_tuple_builder.authenticatedEffectfulPrefixReplay(
        current,
        incoming,
        else_block,
        contexts[current.index()].?,
        &incoming_arguments,
        incoming_reference,
    )) == null);
}

const SameEntryParameterizedPrefixMutation = enum {
    valid,
    same_context,
    parameter_use,
    prefix_parameter_use,
    no_effect,
    non_iteration_handoff,
    altered_forwarding,
    noncanonical_prefix,
    ambiguous_branch,
    cyclic_prefix,
    unvisited_prefix,
};

fn sameEntryParameterizedPrefixWitness(
    mutation: SameEntryParameterizedPrefixMutation,
) BuildError!bool {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const incoming = ir.BlockId.fromIndex(2);
    const current = ir.BlockId.fromIndex(3);
    const prefix = ir.BlockId.fromIndex(4);
    const header = ir.BlockId.fromIndex(5);
    const body = ir.BlockId.fromIndex(6);
    const exit = ir.BlockId.fromIndex(7);
    const owner_stop = ir.BlockId.fromIndex(8);

    const selector = ir.ValueId.fromIndex(0);
    const owner_first = ir.ValueId.fromIndex(1);
    const owner_second = ir.ValueId.fromIndex(2);
    const owner_third = ir.ValueId.fromIndex(3);
    const owner_fourth = ir.ValueId.fromIndex(4);
    const incoming_first = ir.ValueId.fromIndex(5);
    const incoming_second = ir.ValueId.fromIndex(6);
    const incoming_third = ir.ValueId.fromIndex(7);
    const incoming_fourth = ir.ValueId.fromIndex(8);
    const formal_first = ir.ValueId.fromIndex(9);
    const formal_second = ir.ValueId.fromIndex(10);
    const formal_third = ir.ValueId.fromIndex(11);
    const formal_fourth = ir.ValueId.fromIndex(12);
    const header_control = ir.ValueId.fromIndex(13);
    const header_limit = ir.ValueId.fromIndex(14);
    const header_step = ir.ValueId.fromIndex(15);
    const header_initial = ir.ValueId.fromIndex(16);
    const has_value = ir.ValueId.fromIndex(17);
    const next_limit = ir.ValueId.fromIndex(18);
    const next_step = ir.ValueId.fromIndex(19);
    const next_control = ir.ValueId.fromIndex(20);
    const effect_value = ir.ValueId.fromIndex(21);
    const prefix_value = ir.ValueId.fromIndex(22);
    const copied_formal = ir.ValueId.fromIndex(23);
    const prefix_first = ir.ValueId.fromIndex(24);
    const prefix_second = ir.ValueId.fromIndex(25);
    const prefix_third = ir.ValueId.fromIndex(26);
    const prefix_fourth = ir.ValueId.fromIndex(27);
    const copied_prefix = ir.ValueId.fromIndex(28);

    const effect_constant = ir.InstructionId.fromIndex(0);
    const effect_write = ir.InstructionId.fromIndex(1);
    const prefix_constant = ir.InstructionId.fromIndex(2);
    const prefix_write = ir.InstructionId.fromIndex(3);
    const copy_formal = ir.InstructionId.fromIndex(4);
    const transition = ir.InstructionId.fromIndex(5);
    const copy_prefix_formal = ir.InstructionId.fromIndex(6);

    const owner_arguments = [_]ir.ValueId{ owner_first, owner_second, owner_third, owner_fourth };
    const incoming_arguments = [_]ir.ValueId{
        incoming_first,
        incoming_second,
        incoming_third,
        incoming_fourth,
    };
    const current_parameters = [_]ir.ValueId{ formal_first, formal_second, formal_third, formal_fourth };
    const prefix_parameters = [_]ir.ValueId{ prefix_first, prefix_second, prefix_third, prefix_fourth };
    var altered_prefix_arguments = prefix_parameters;

    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = incoming },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{
            .target = current,
            .arguments = &owner_arguments,
        } } },
        .{ .id = incoming, .function = function_id, .terminator = .{ .jump = .{
            .target = current,
            .arguments = &incoming_arguments,
        } } },
        .{ .id = current, .function = function_id, .parameters = &current_parameters, .instructions = &.{
            effect_constant,
            effect_write,
        }, .terminator = .{ .jump = .{
            .target = prefix,
            .arguments = &current_parameters,
        } } },
        .{ .id = prefix, .function = function_id, .parameters = &prefix_parameters, .instructions = &.{
            prefix_constant,
            prefix_write,
        }, .terminator = .{ .jump = .{
            .target = header,
            .arguments = &prefix_parameters,
        } } },
        .{ .id = header, .function = function_id, .parameters = &.{
            header_control,
            header_limit,
            header_step,
            header_initial,
        }, .instructions = &.{transition}, .terminator = .{ .branch = .{
            .condition = has_value,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    if (mutation == .non_iteration_handoff) {
        blocks[prefix.index()].terminator = .{ .jump = .{ .target = body } };
    }
    if (mutation == .parameter_use) {
        blocks[current.index()].instructions = &.{ effect_constant, effect_write, copy_formal };
    }
    if (mutation == .prefix_parameter_use) {
        blocks[prefix.index()].instructions = &.{ prefix_constant, prefix_write, copy_prefix_formal };
    }
    if (mutation == .no_effect) {
        blocks[current.index()].instructions = &.{effect_constant};
        blocks[prefix.index()].instructions = &.{prefix_constant};
    }
    if (mutation == .altered_forwarding) {
        altered_prefix_arguments[0] = owner_first;
        blocks[current.index()].terminator = .{ .jump = .{
            .target = prefix,
            .arguments = &altered_prefix_arguments,
        } };
    }
    if (mutation == .ambiguous_branch) {
        blocks[prefix.index()].terminator = .{ .branch = .{
            .condition = prefix_fourth,
            .then_edge = .{ .target = header, .arguments = &prefix_parameters },
            .else_edge = .{ .target = exit },
        } };
    }
    if (mutation == .cyclic_prefix) {
        blocks[prefix.index()].terminator = .{ .jump = .{
            .target = prefix,
            .arguments = &prefix_parameters,
        } };
    }

    const function = ir.Function{
        .id = function_id,
        .parameters = &.{
            selector,
            owner_first,
            owner_second,
            owner_third,
            owner_fourth,
            incoming_first,
            incoming_second,
            incoming_third,
            incoming_fourth,
        },
        .blocks = &.{ entry, owner, incoming, current, prefix, header, body, exit, owner_stop },
        .entry_block = entry,
    };
    var values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = owner_first, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = owner_second, .function = function_id, .origin = .{ .parameter = 2 } },
        .{ .id = owner_third, .function = function_id, .origin = .{ .parameter = 3 } },
        .{ .id = owner_fourth, .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } },
        .{ .id = incoming_first, .function = function_id, .origin = .{ .parameter = 5 } },
        .{ .id = incoming_second, .function = function_id, .origin = .{ .parameter = 6 } },
        .{ .id = incoming_third, .function = function_id, .origin = .{ .parameter = 7 } },
        .{ .id = incoming_fourth, .function = function_id, .type = .boolean, .origin = .{ .parameter = 8 } },
        .{ .id = formal_first, .function = function_id, .origin = .{ .block_parameter = .{ .block = current, .index = 0 } } },
        .{ .id = formal_second, .function = function_id, .origin = .{ .block_parameter = .{ .block = current, .index = 1 } } },
        .{ .id = formal_third, .function = function_id, .origin = .{ .block_parameter = .{ .block = current, .index = 2 } } },
        .{ .id = formal_fourth, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = current, .index = 3 } } },
        .{ .id = header_control, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
        .{ .id = header_limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 1 } } },
        .{ .id = header_step, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 2 } } },
        .{ .id = header_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = header, .index = 3 } } },
        .{ .id = has_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition, .index = 0 } } },
        .{ .id = next_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition, .index = 1 } } },
        .{ .id = next_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition, .index = 3 } } },
        .{ .id = effect_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = effect_constant, .index = 0 } } },
        .{ .id = prefix_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = prefix_constant, .index = 0 } } },
        .{ .id = copied_formal, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = copy_formal, .index = 0 } } },
        .{ .id = prefix_first, .function = function_id, .origin = .{ .block_parameter = .{ .block = prefix, .index = 0 } } },
        .{ .id = prefix_second, .function = function_id, .origin = .{ .block_parameter = .{ .block = prefix, .index = 1 } } },
        .{ .id = prefix_third, .function = function_id, .origin = .{ .block_parameter = .{ .block = prefix, .index = 2 } } },
        .{ .id = prefix_fourth, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = prefix, .index = 3 } } },
        .{ .id = copied_prefix, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = copy_prefix_formal, .index = 0 } } },
    };
    if (mutation == .noncanonical_prefix) {
        values[prefix_first.index()].origin = .{ .parameter = 0 };
    }
    const instructions = [_]ir.Instruction{
        .{ .id = effect_constant, .block = current, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{effect_value}, .effects = .pure },
        .{ .id = effect_write, .block = current, .operation = .{ .place_write = .{ .place = ir.PlaceId.fromIndex(0), .value = effect_value } }, .results = &.{}, .effects = .place_write },
        .{ .id = prefix_constant, .block = prefix, .operation = .{ .constant = .{ .integer = "2" } }, .results = &.{prefix_value}, .effects = .pure },
        .{ .id = prefix_write, .block = prefix, .operation = .{ .place_write = .{ .place = ir.PlaceId.fromIndex(0), .value = prefix_value } }, .results = &.{}, .effects = .place_write },
        .{ .id = copy_formal, .block = current, .operation = .{ .copy = formal_first }, .results = &.{copied_formal}, .effects = .pure },
        .{ .id = transition, .block = header, .operation = .{ .numeric_for_next = .{
            .control = header_control,
            .limit = header_limit,
            .step = header_step,
            .initial = header_initial,
        } }, .results = &.{ has_value, next_limit, next_step, next_control }, .effects = .numeric_for_next },
        .{ .id = copy_prefix_formal, .block = prefix, .operation = .{ .copy = prefix_first }, .results = &.{copied_prefix}, .effects = .pure },
    };
    const places = [_]ir.Place{.{
        .id = ir.PlaceId.fromIndex(0),
        .function = function_id,
        .type = .integer,
        .origin = .{ .local = 0 },
    }};
    const program = ir.Program{
        .program_id = "same-entry-parameterized-prefix-replay",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };
    var analysis = cfg.Analysis.init(allocator, &program, function) catch |err| switch (err) {
        error.InvalidCfg => return false,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(allocator, &analysis);
    defer allocator.free(loop_headers);

    var visited = [_]bool{ false, false, false, true, true, false, false, false, false };
    if (mutation == .unvisited_prefix) visited[prefix.index()] = false;
    var contexts = [_]?Builder.VisitContext{ null, null, null, .{
        .start = current,
        .stop = owner_stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &owner_arguments,
    }, null, null, null, null, null };
    var builder: Builder = .{
        .allocator = allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const incoming_reference = ir.CfgEdgeRef{ .source = incoming, .kind = .jump, .target = current };
    const replay_stop = if (mutation == .same_context) owner_stop else exit;
    const replay = try builder.authenticatedSameEntryParameterizedPrefixReplay(
        current,
        current,
        replay_stop,
        null,
        null,
        contexts[current.index()].?,
        &incoming_arguments,
        incoming_reference,
    ) orelse return false;
    defer allocator.free(replay.nodes);
    if (mutation != .valid and mutation != .same_context) return false;
    return replay.nodes.len == 2 and
        replay.nodes[0].blockId() == current and
        replay.nodes[1].blockId() == prefix and
        replay.source == prefix and
        replay.next == header and
        std.mem.eql(ir.ValueId, replay.arguments, &prefix_parameters);
}

test "same-entry parameterized prefix replay requires a semantic handoff" {
    try std.testing.expect(try sameEntryParameterizedPrefixWitness(.valid));
    try std.testing.expect(try sameEntryParameterizedPrefixWitness(.same_context));
    try std.testing.expect(!(try sameEntryParameterizedPrefixWitness(.parameter_use)));
    try std.testing.expect(!(try sameEntryParameterizedPrefixWitness(.prefix_parameter_use)));
    try std.testing.expect(!(try sameEntryParameterizedPrefixWitness(.no_effect)));
    try std.testing.expect(!(try sameEntryParameterizedPrefixWitness(.non_iteration_handoff)));
    try std.testing.expect(!(try sameEntryParameterizedPrefixWitness(.altered_forwarding)));
    try std.testing.expect(!(try sameEntryParameterizedPrefixWitness(.noncanonical_prefix)));
    try std.testing.expect(!(try sameEntryParameterizedPrefixWitness(.ambiguous_branch)));
    try std.testing.expect(!(try sameEntryParameterizedPrefixWitness(.cyclic_prefix)));
    try std.testing.expect(!(try sameEntryParameterizedPrefixWitness(.unvisited_prefix)));
}

const ZeroParameterPrefixReplayMutation = enum {
    valid,
    stop_boundary,
    acyclic,
    no_effect,
    mismatched_stop,
    unvisited,
};

fn zeroParameterPrefixReplayWitness(
    mutation: ZeroParameterPrefixReplayMutation,
) BuildError!bool {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const incoming = ir.BlockId.fromIndex(2);
    const current = ir.BlockId.fromIndex(3);
    const prefix = ir.BlockId.fromIndex(4);
    const branch = ir.BlockId.fromIndex(5);
    const owner_stop = ir.BlockId.fromIndex(6);
    const alternate_stop = ir.BlockId.fromIndex(7);

    const selector = ir.ValueId.fromIndex(0);
    const effect_value = ir.ValueId.fromIndex(1);
    const prefix_value = ir.ValueId.fromIndex(2);
    const effect_constant = ir.InstructionId.fromIndex(0);
    const effect_write = ir.InstructionId.fromIndex(1);
    const prefix_constant = ir.InstructionId.fromIndex(2);
    const prefix_write = ir.InstructionId.fromIndex(3);

    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = incoming },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{ .target = current } } },
        .{ .id = incoming, .function = function_id, .terminator = .{ .jump = .{ .target = current } } },
        .{ .id = current, .function = function_id, .instructions = &.{ effect_constant, effect_write }, .terminator = .{ .jump = .{ .target = prefix } } },
        .{ .id = prefix, .function = function_id, .instructions = &.{ prefix_constant, prefix_write }, .terminator = .{ .jump = .{ .target = branch } } },
        .{ .id = branch, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = incoming },
        } } },
        .{ .id = owner_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = alternate_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    if (mutation == .acyclic) {
        blocks[branch.index()].terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = owner_stop },
        } };
    }
    if (mutation == .stop_boundary) {
        blocks[prefix.index()].terminator = .{ .jump = .{ .target = owner_stop } };
        blocks[owner_stop.index()].terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = incoming },
        } };
    }

    var instructions = [_]ir.Instruction{
        .{ .id = effect_constant, .block = current, .operation = .{ .constant = .{ .number = 1 } }, .results = &.{effect_value}, .effects = .pure },
        .{ .id = effect_write, .block = current, .operation = .{ .place_write = .{ .place = ir.PlaceId.fromIndex(0), .value = effect_value } }, .results = &.{}, .effects = .place_write },
        .{ .id = prefix_constant, .block = prefix, .operation = .{ .constant = .{ .number = 2 } }, .results = &.{prefix_value}, .effects = .pure },
        .{ .id = prefix_write, .block = prefix, .operation = .{ .place_write = .{ .place = ir.PlaceId.fromIndex(0), .value = prefix_value } }, .results = &.{}, .effects = .place_write },
    };
    if (mutation == .no_effect) {
        instructions[effect_write.index()].effects = .pure;
        instructions[prefix_write.index()].effects = .pure;
    }

    const function = ir.Function{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ entry, owner, incoming, current, prefix, branch, owner_stop, alternate_stop },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = effect_value, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = effect_constant, .index = 0 } } },
        .{ .id = prefix_value, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = prefix_constant, .index = 0 } } },
    };
    const places = [_]ir.Place{.{
        .id = ir.PlaceId.fromIndex(0),
        .function = function_id,
        .type = .number,
        .origin = .{ .local = 0 },
    }};
    const program = ir.Program{
        .program_id = "zero-parameter-effectful-prefix-replay",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };
    var analysis = cfg.Analysis.init(allocator, &program, function) catch |err| switch (err) {
        error.InvalidCfg => return false,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(allocator, &analysis);
    defer allocator.free(loop_headers);

    var visited = [_]bool{ false, false, true, true, false, false, false, false };
    if (mutation == .unvisited) visited[current.index()] = false;
    visited[prefix.index()] = true;
    var contexts = [_]?Builder.VisitContext{ null, null, null, null, null, null, null, null };
    var builder: Builder = .{
        .allocator = allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const owner_context: Builder.VisitContext = .{
        .start = owner,
        .stop = owner_stop,
        .loop_exit = null,
        .continue_target = null,
    };
    const current_arguments = [_]ir.ValueId{};
    const incoming_reference = ir.CfgEdgeRef{ .source = incoming, .kind = .jump, .target = current };
    const stop = if (mutation == .mismatched_stop) alternate_stop else owner_stop;
    const replay = try builder.authenticatedEffectfulZeroParameterPrefixReplay(
        current,
        incoming,
        stop,
        null,
        null,
        owner_context,
        &current_arguments,
        incoming_reference,
    );
    if (mutation != .valid and mutation != .stop_boundary) return replay == null;
    const result = replay orelse return false;
    defer allocator.free(result.nodes);
    if (mutation == .stop_boundary) {
        return result.nodes.len == 2 and
            result.nodes[0].blockId() == current and
            result.nodes[1].blockId() == prefix and
            result.source == prefix and
            result.next == owner_stop and
            result.arguments.len == 0;
    }
    return result.nodes.len == 2 and
        result.nodes[0].blockId() == current and
        result.nodes[1].blockId() == prefix and
        result.source == prefix and
        result.next == branch and
        result.arguments.len == 0;
}

test "effectful zero-parameter prefix replay requires an authenticated SCC" {
    try std.testing.expect(try zeroParameterPrefixReplayWitness(.valid));
    try std.testing.expect(try zeroParameterPrefixReplayWitness(.stop_boundary));
    try std.testing.expect(try zeroParameterPrefixReplayWitness(.acyclic));
    try std.testing.expect(try zeroParameterPrefixReplayWitness(.no_effect));
    try std.testing.expect(try zeroParameterPrefixReplayWitness(.mismatched_stop));
    try std.testing.expect(try zeroParameterPrefixReplayWitness(.unvisited));
}

test "parameterized stop replay rejects non-carried continuation values" {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const incoming = ir.BlockId.fromIndex(2);
    const current = ir.BlockId.fromIndex(3);
    const prefix = ir.BlockId.fromIndex(4);
    const stop = ir.BlockId.fromIndex(5);
    const continuation = ir.BlockId.fromIndex(6);

    const selector = ir.ValueId.fromIndex(0);
    const effect_value = ir.ValueId.fromIndex(1);
    const prefix_value = ir.ValueId.fromIndex(2);
    const stop_parameter = ir.ValueId.fromIndex(3);
    const continuation_value = ir.ValueId.fromIndex(4);
    const effect_constant = ir.InstructionId.fromIndex(0);
    const effect_write = ir.InstructionId.fromIndex(1);
    const prefix_constant = ir.InstructionId.fromIndex(2);
    const prefix_write = ir.InstructionId.fromIndex(3);
    const continuation_copy = ir.InstructionId.fromIndex(4);
    const owner_arguments = [_]ir.ValueId{selector};
    const prefix_arguments = [_]ir.ValueId{prefix_value};

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = incoming },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{
            .target = stop,
            .arguments = &owner_arguments,
        } } },
        .{ .id = incoming, .function = function_id, .terminator = .{ .jump = .{ .target = current } } },
        .{ .id = current, .function = function_id, .instructions = &.{ effect_constant, effect_write }, .terminator = .{ .jump = .{ .target = prefix } } },
        .{ .id = prefix, .function = function_id, .instructions = &.{ prefix_constant, prefix_write }, .terminator = .{ .jump = .{
            .target = stop,
            .arguments = &prefix_arguments,
        } } },
        .{ .id = stop, .function = function_id, .parameters = &.{stop_parameter}, .terminator = .{ .jump = .{ .target = continuation } } },
        .{ .id = continuation, .function = function_id, .instructions = &.{continuation_copy}, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = incoming },
        } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = effect_constant, .block = current, .operation = .{ .constant = .{ .number = 1 } }, .results = &.{effect_value}, .effects = .pure },
        .{ .id = effect_write, .block = current, .operation = .{ .place_write = .{ .place = ir.PlaceId.fromIndex(0), .value = effect_value } }, .results = &.{}, .effects = .place_write },
        .{ .id = prefix_constant, .block = prefix, .operation = .{ .constant = .{ .number = 2 } }, .results = &.{prefix_value}, .effects = .pure },
        .{ .id = prefix_write, .block = prefix, .operation = .{ .place_write = .{ .place = ir.PlaceId.fromIndex(0), .value = prefix_value } }, .results = &.{}, .effects = .place_write },
        .{ .id = continuation_copy, .block = continuation, .operation = .{ .copy = prefix_value }, .results = &.{continuation_value}, .effects = .pure },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ entry, owner, incoming, current, prefix, stop, continuation },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = effect_value, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = effect_constant, .index = 0 } } },
        .{ .id = prefix_value, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = prefix_constant, .index = 0 } } },
        .{ .id = stop_parameter, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = stop, .index = 0 } } },
        .{ .id = continuation_value, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = continuation_copy, .index = 0 } } },
    };
    const places = [_]ir.Place{.{
        .id = ir.PlaceId.fromIndex(0),
        .function = function_id,
        .type = .number,
        .origin = .{ .local = 0 },
    }};
    const program = ir.Program{
        .program_id = "parameterized-stop-boundary-value-closure",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };
    var analysis = try cfg.Analysis.init(allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(allocator, &analysis);
    defer allocator.free(loop_headers);

    var visited = [_]bool{ false, false, true, true, false, false, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, null, null, null, null };
    var builder: Builder = .{
        .allocator = allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
    };
    const owner_context: Builder.VisitContext = .{
        .start = owner,
        .stop = stop,
        .loop_exit = null,
        .continue_target = null,
    };
    const current_arguments = [_]ir.ValueId{};
    const incoming_reference = ir.CfgEdgeRef{ .source = incoming, .kind = .jump, .target = current };
    const replay = try builder.authenticatedEffectfulZeroParameterPrefixReplay(
        current,
        incoming,
        stop,
        null,
        null,
        owner_context,
        &current_arguments,
        incoming_reference,
    );
    try std.testing.expect(replay == null);
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
            continueProjectionUsesFlag(region, region.continue_projection.?)) or
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
            // A body exit continue carried by flag escapes to the body region's stop (`markFlaggedContinues`).
            if (control.continue_via_flag and control.body_region.stop != null and
                control.body_region.stop.? == target) break :boundary true;
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

fn nodeHasLoopBoundaryContinueNotTo(node: Node, region_stop: ir.BlockId, region_continue_target: ?ir.BlockId) bool {
    return switch (node) {
        .block, .loop_control, .loop_terminal => false,
        .branch => |branch| nestedRegionHasLoopBoundaryContinueNotTo(branch.then_region) or
            nestedRegionHasLoopBoundaryContinueNotTo(branch.else_region),
        .loop, .latch_loop => false,
        .infinite_loop => |loop| loop.shared_side_exit != null and
            sharedSideExitHasLoopBoundaryContinueNotTo(loop.shared_side_exit.?),
        .loop_boundary => |control| blk: {
            // A body exit continue carried by flag (`markFlaggedContinues`) is written as the flag and a `break`.
            if (control.body_region.stop) |body| {
                if (!control.continue_via_flag and body != region_stop) {
                    if (region_continue_target) |continue_target| {
                        if (body == continue_target) break :blk true;
                    }
                }
            }
            if (nestedRegionHasLoopBoundaryContinueNotTo(control.body_region)) break :blk true;
            break :blk switch (control.boundary) {
                .side_exit => |side| nestedRegionHasLoopBoundaryContinueNotTo(side.region),
                .side_escape => |side| nestedRegionHasLoopBoundaryContinueNotTo(side.region),
                .exit, .escape, .terminal, .shared_exit => false,
            };
        },
    };
}

fn nestedRegionHasLoopBoundaryContinueNotTo(region: *const Region) bool {
    const stop = region.stop orelse return false;
    return regionHasLoopBoundaryContinueNotTo(region, stop);
}

fn sharedSideExitHasLoopBoundaryContinueNotTo(side_exit: SharedSideExit) bool {
    for (side_exit.entries) |entry| {
        if (nestedRegionHasLoopBoundaryContinueNotTo(entry.region)) return true;
    }
    return false;
}

fn nodeHasUnflaggedLoopExitBreak(program: *const ir.Program, node: Node) bool {
    return switch (node) {
        .block, .loop_terminal => false,
        .loop_control => true,
        .branch => |branch| regionHasUnflaggedLoopExitBreak(program, branch.then_region) or
            regionHasUnflaggedLoopExitBreak(program, branch.else_region),
        .loop, .latch_loop => false,
        .infinite_loop => |loop| loop.shared_side_exit != null and
            sharedSideExitHasUnflaggedLoopExitBreak(program, loop.shared_side_exit.?),
        .loop_boundary => |control| blk: {
            if (regionHasUnflaggedLoopExitBreak(program, control.body_region)) break :blk true;
            break :blk switch (control.boundary) {
                .side_exit => |side| !regionAlwaysFunctionTerminates(program, side.region) or
                    regionHasUnflaggedLoopExitBreak(program, side.region),
                .side_escape => |side| regionHasUnflaggedLoopExitBreak(program, side.region),
                .shared_exit => true,
                .exit, .escape, .terminal => false,
            };
        },
    };
}

fn sharedSideExitHasUnflaggedLoopExitBreak(program: *const ir.Program, side_exit: SharedSideExit) bool {
    for (side_exit.entries) |entry| {
        if (regionHasUnflaggedLoopExitBreak(program, entry.region)) return true;
    }
    return false;
}

/// The emitter's termination test (`regionAlwaysFunctionTerminates` in
/// src/emit_luau.zig): the side-exit arm writes no `break` after a side region
/// it reports. A lockstep copy, like the one in
/// src/validate_luau_syntax_depth.zig; the three must change together.
fn regionAlwaysFunctionTerminates(program: *const ir.Program, region: *const Region) bool {
    if (region.terminal_projection != null) return true;
    if (region.escape_projection != null) return false;
    if (region.nodes.len == 0) return false;
    return nodeAlwaysFunctionTerminates(program, region.nodes[region.nodes.len - 1]);
}

fn nodeAlwaysFunctionTerminates(program: *const ir.Program, node: Node) bool {
    return switch (node) {
        .block => |block_id| switch (program.blocks[block_id.index()].terminator) {
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => true,
            else => false,
        },
        .branch => |branch| branch.join == null and
            regionAlwaysFunctionTerminates(program, branch.then_region) and
            regionAlwaysFunctionTerminates(program, branch.else_region),
        else => false,
    };
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
        if (continueProjectionUsesFlag(region, projection)) {
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
            if (control.continue_via_flag) {
                if (control.body_region.stop) |stop| try addFreeTarget(allocator, targets, captures, stop);
            }
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

test "nonempty prefix reuses an authenticated same-SCC parameterized branch" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const prefix = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const stop = ir.BlockId.fromIndex(4);

    const selector = ir.ValueId.fromIndex(0);
    const owner_first = ir.ValueId.fromIndex(1);
    const owner_second = ir.ValueId.fromIndex(2);
    const target_first = ir.ValueId.fromIndex(3);
    const target_second = ir.ValueId.fromIndex(4);
    const expected = [_]ir.ValueId{ owner_first, owner_second };
    const actual = [_]ir.ValueId{ target_first, target_second };
    const owner_reference: ir.CfgEdgeRef = .{
        .source = owner,
        .kind = .jump,
        .target = target,
    };
    const incoming_reference: ir.CfgEdgeRef = .{
        .source = prefix,
        .kind = .jump,
        .target = target,
    };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = prefix },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = expected[0..],
        } } },
        .{ .id = prefix, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = actual[0..],
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{ target_first, target_second }, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = prefix },
            .else_edge = .{ .target = stop },
        } } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ selector, owner_first, owner_second },
        .blocks = &.{ entry, owner, prefix, target, stop },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = owner_first, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = owner_second, .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = target_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = target_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 1 } } },
    };
    var program = ir.Program{
        .program_id = "same-scc-parameterized-branch-prefix",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const loop_headers = try natural_loop.headerCandidatesAlloc(std.testing.allocator, &analysis);
    defer std.testing.allocator.free(loop_headers);
    var replay_context = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay_context.deinit();

    var visited = [_]bool{ false, false, false, true, false };
    var contexts = [_]?Builder.VisitContext{ null, null, null, .{
        .start = owner,
        .stop = stop,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &expected,
        .entry_reference = owner_reference,
    }, null };
    var builder: Builder = .{
        .allocator = std.testing.allocator,
        .analysis = &analysis,
        .visited = &visited,
        .visited_contexts = &contexts,
        .loop_headers = loop_headers,
        .replay_context = &replay_context,
    };

    const parameters_match = try builder.parameterProjectionMatches(target, &expected, &actual);
    try std.testing.expect(parameters_match);
    try std.testing.expect(try builder.authenticatedSameSccParameterizedReentry(
        target,
        prefix,
        null,
        null,
        contexts[target.index()].?,
        parameters_match,
        incoming_reference,
    ));

    const projected = try builder.buildRegionImplWithEntryArguments(
        prefix,
        stop,
        null,
        null,
        null,
        null,
        false,
        null,
        null,
    );
    defer destroyRegion(std.testing.allocator, projected);
    try std.testing.expectEqual(@as(usize, 1), projected.nodes.len);
    try std.testing.expectEqual(prefix, projected.nodes[0].blockId());
    try std.testing.expectEqual(target, projected.escape_projection.?.target);
    try std.testing.expectEqualSlices(ir.ValueId, actual[0..], projected.escape_projection.?.edge.?.arguments);

    var acyclic_blocks = blocks;
    acyclic_blocks[target.index()].terminator = .{ .branch = .{
        .condition = selector,
        .then_edge = .{ .target = stop },
        .else_edge = .{ .target = stop },
    } };
    var acyclic_program = program;
    acyclic_program.blocks = &acyclic_blocks;
    var acyclic_analysis = try cfg.Analysis.init(std.testing.allocator, &acyclic_program, function);
    defer acyclic_analysis.deinit();
    var acyclic_replay = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &acyclic_program,
        function_id,
    );
    defer acyclic_replay.deinit();
    var acyclic_builder = builder;
    acyclic_builder.analysis = &acyclic_analysis;
    acyclic_builder.replay_context = &acyclic_replay;
    try std.testing.expect(!try acyclic_builder.authenticatedSameSccParameterizedReentry(
        target,
        prefix,
        null,
        null,
        contexts[target.index()].?,
        parameters_match,
        incoming_reference,
    ));
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
