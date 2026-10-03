const std = @import("std");
const Io = std.Io;
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const cfg_edge = @import("cfg_edge.zig");
const irreducible_region = @import("irreducible_region.zig");
const irreducible_policy = @import("irreducible_policy.zig");
const node_split = @import("node_split.zig");
const control_flow = @import("control_flow.zig");
const iteration_protocol = @import("iteration_protocol.zig");
const structural_overlap = @import("structural_overlap.zig");
const clone_availability = @import("clone_availability.zig");
const structure = @import("structure.zig");
const build_options = @import("build_options");

pub const NormalizeError = error{NormalizationInvariantFailed} || std.mem.Allocator.Error;

const trace_normalize_phases = build_options.trace_normalize_phases;

fn normalizationIterationLimit(source: *const ir.Program, only_function: ?usize) usize {
    if (only_function) |function_index| {
        if (function_index < source.functions.len) {
            return @max(source.functions[function_index].blocks.len, 1);
        }
    }
    return @max(source.blocks.len, 1);
}

test "targeted normalization uses the selected function budget" {
    const function_zero = ir.Function{
        .id = ir.FunctionId.fromIndex(0),
        .blocks = &.{ ir.BlockId.fromIndex(0), ir.BlockId.fromIndex(1) },
        .entry_block = ir.BlockId.fromIndex(0),
    };
    const function_one = ir.Function{
        .id = ir.FunctionId.fromIndex(1),
        .blocks = &.{
            ir.BlockId.fromIndex(2),
            ir.BlockId.fromIndex(3),
            ir.BlockId.fromIndex(4),
            ir.BlockId.fromIndex(5),
            ir.BlockId.fromIndex(6),
        },
        .entry_block = ir.BlockId.fromIndex(2),
    };
    const functions = [_]ir.Function{ function_zero, function_one };
    const program = ir.Program{
        .program_id = "targeted-normalization-budget",
        .entry_function = function_zero.id,
        .functions = &functions,
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
    };

    try std.testing.expectEqual(@as(usize, 2), normalizationIterationLimit(&program, 0));
    try std.testing.expectEqual(@as(usize, 5), normalizationIterationLimit(&program, 1));
    try std.testing.expectEqual(@as(usize, 1), normalizationIterationLimit(&program, 99));
    try std.testing.expectEqual(@as(usize, 1), normalizationIterationLimit(&program, null));
}

pub const Result = struct {
    program: ir.Program,
    resume_seed: ?ResumeSeed = null,
    cloned_blocks: usize = 0,
    cloned_values: usize = 0,
    cloned_packs: usize = 0,
    cloned_instructions: usize = 0,
    rewritten_edges: usize = 0,
};

const Secondary = struct {
    block: ir.BlockId,
    incoming: []ir.CfgEdgeRef,
    closure: []ir.BlockId,
    // Optional context aligned with incoming.  Ordinary overlap plans do not
    // need it; unvisited frontier plans preserve it for feedback freshness.
    incoming_contexts: []?structure.CollisionContext = &.{},
};

const SplitPlan = struct {
    allocator: std.mem.Allocator,
    function_index: usize,
    secondaries: []Secondary,
    secondary_count: usize,

    fn deinit(self: *SplitPlan) void {
        for (self.secondaries[0..self.secondary_count]) |secondary| {
            self.allocator.free(secondary.incoming);
            if (secondary.incoming_contexts.len != 0) self.allocator.free(secondary.incoming_contexts);
            self.allocator.free(secondary.closure);
        }
        self.allocator.free(self.secondaries);
        self.* = undefined;
    }
};

const CollisionArm = struct {
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    target: ir.BlockId,
    // A resume reservation marks only the exact live edge consumed by a
    // clone-fold step.  It must not suppress a distinct predecessor that
    // reaches the same continuation target.
    reserved: bool = false,
    // A node-split lineage can be revisited from different structured
    // continuation contexts. Preserve the authenticated context when the
    // structurer provides it; an unknown context remains conservative.
    context: ?structure.CollisionContext = null,
};

fn reserveCloneFoldResumeArm(
    allocator: std.mem.Allocator,
    arms: *std.ArrayList(CollisionArm),
    seed: CollisionSeed,
) NormalizeError!void {
    if (seed.proof != .clone_fold) return;
    const source = seed.source orelse return;
    const kind = seed.kind orelse return;
    for (arms.items) |arm| {
        if (arm.source == source and arm.kind == kind and arm.target == seed.target) return;
    }
    try arms.append(allocator, .{
        .source = source,
        .kind = kind,
        .target = seed.target,
        .reserved = true,
        .context = seed.context,
    });
}

pub const CollisionSeedProof = enum {
    node_split,
    paired_forwarding,
    clone_fold,
};

pub const ResumeSeed = struct {
    function_index: usize,
    target: ir.BlockId,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    original_target: ir.BlockId,
    previous: ir.BlockId,
    context_start: ir.BlockId,
    context_stop: ?ir.BlockId,
    context_loop_exit: ?ir.BlockId,
    context_continue_target: ?ir.BlockId,
    parameter_arguments: ?[]const ir.ValueId = null,
    proof: CollisionSeedProof = .node_split,
};

const CollisionSeed = struct {
    function_index: usize,
    target: ir.BlockId,
    source: ?ir.BlockId,
    kind: ?ir.CfgEdgeKind,
    original_target: ?ir.BlockId,
    previous: ?ir.BlockId,
    context: ?structure.CollisionContext,
    proof: CollisionSeedProof = .node_split,
};

fn collisionSeedForAppliedArm(
    function_index: usize,
    target: ir.BlockId,
    arm: CollisionArm,
) CollisionSeed {
    return .{
        .function_index = function_index,
        .target = target,
        .source = arm.source,
        .kind = arm.kind,
        .original_target = arm.target,
        .previous = null,
        .context = arm.context,
    };
}

// A direct sibling or predecessor search returns an overlap split, but it
// does not return the structured visit context that authenticated the edge.
// Do not turn an unknown context into a lineage-directed retry: the next full
// scan must rebuild the context from the actual post-split graph.
fn collisionSeedForAppliedArmIfAuthenticated(
    function_index: usize,
    target: ir.BlockId,
    arm: CollisionArm,
) ?CollisionSeed {
    if (arm.context == null) return null;
    return collisionSeedForAppliedArm(function_index, target, arm);
}

test "collision seed preserves the applied arm context" {
    const applied_context: structure.CollisionContext = .{
        .start = ir.BlockId.fromIndex(21),
        .stop = ir.BlockId.fromIndex(22),
        .loop_exit = ir.BlockId.fromIndex(23),
        .continue_target = ir.BlockId.fromIndex(24),
    };
    const seed = collisionSeedForAppliedArm(
        7,
        ir.BlockId.fromIndex(30),
        .{
            .source = ir.BlockId.fromIndex(31),
            .kind = .jump,
            .target = ir.BlockId.fromIndex(32),
            .context = applied_context,
        },
    );

    try std.testing.expectEqual(@as(usize, 7), seed.function_index);
    try std.testing.expectEqual(ir.BlockId.fromIndex(30), seed.target);
    try std.testing.expectEqual(ir.BlockId.fromIndex(31), seed.source.?);
    try std.testing.expectEqual(ir.CfgEdgeKind.jump, seed.kind.?);
    try std.testing.expectEqual(ir.BlockId.fromIndex(32), seed.original_target.?);
    try std.testing.expect(seed.context != null);
    try std.testing.expectEqual(applied_context.start, seed.context.?.start);
    try std.testing.expectEqual(applied_context.stop, seed.context.?.stop);
    try std.testing.expectEqual(applied_context.loop_exit, seed.context.?.loop_exit);
    try std.testing.expectEqual(applied_context.continue_target, seed.context.?.continue_target);
}

test "unproven fallback context does not seed a directed retry" {
    const arm: CollisionArm = .{
        .source = ir.BlockId.fromIndex(31),
        .kind = .jump,
        .target = ir.BlockId.fromIndex(32),
    };
    try std.testing.expect(
        collisionSeedForAppliedArmIfAuthenticated(7, ir.BlockId.fromIndex(30), arm) == null,
    );
}

test "clone-fold resume arm reservation is idempotent" {
    var arms: std.ArrayList(CollisionArm) = .empty;
    defer arms.deinit(std.testing.allocator);

    const source = ir.BlockId.fromIndex(31);
    const target = ir.BlockId.fromIndex(32);
    const seed: CollisionSeed = .{
        .function_index = 7,
        .target = target,
        .source = source,
        .kind = .jump,
        .original_target = ir.BlockId.fromIndex(33),
        .previous = target,
        .context = null,
        .proof = .clone_fold,
    };

    try reserveCloneFoldResumeArm(std.testing.allocator, &arms, seed);
    try reserveCloneFoldResumeArm(std.testing.allocator, &arms, seed);
    try std.testing.expectEqual(@as(usize, 1), arms.items.len);
    try std.testing.expectEqual(source, arms.items[0].source);
    try std.testing.expectEqual(target, arms.items[0].target);

    var non_clone = seed;
    non_clone.proof = .node_split;
    non_clone.target = ir.BlockId.fromIndex(34);
    try reserveCloneFoldResumeArm(std.testing.allocator, &arms, non_clone);
    try std.testing.expectEqual(@as(usize, 1), arms.items.len);

    var distinct = seed;
    distinct.target = ir.BlockId.fromIndex(35);
    try reserveCloneFoldResumeArm(std.testing.allocator, &arms, distinct);
    try std.testing.expectEqual(@as(usize, 2), arms.items.len);
}

test "clone-fold reservation does not consume a distinct predecessor" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const alternate_entry = ir.BlockId.fromIndex(2);
    const source_clone = ir.BlockId.fromIndex(3);
    const alternate_source_clone = ir.BlockId.fromIndex(4);
    const target = ir.BlockId.fromIndex(5);
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = alternate_entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source_clone, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = alternate_source_clone, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, source, alternate_entry, source_clone, alternate_source_clone, target },
        .entry_block = entry,
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .jump,
            .from = .{ .target = source },
            .to = .{ .target = source_clone },
            .rule = .node_split,
            .node_split_group = group,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = alternate_entry,
            .kind = .jump,
            .from = .{ .target = source },
            .to = .{ .target = alternate_source_clone },
            .rule = .node_split,
            .node_split_group = group,
        },
    };
    const program = ir.Program{
        .program_id = "reserved-predecessor-distinction",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };
    var projection = try structural_overlap.ReplayProjectionContext.init(std.testing.allocator, &program);
    defer projection.deinit();

    const reserved = [_]CollisionArm{.{
        .source = source_clone,
        .kind = .jump,
        .target = target,
        .reserved = true,
    }};
    const distinct_predecessor: CollisionArm = .{
        .source = alternate_source_clone,
        .kind = .jump,
        .target = target,
    };
    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &program,
        &reserved,
        distinct_predecessor,
        &projection,
    )) == null);

    var ordinary = reserved;
    ordinary[0].reserved = false;
    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &program,
        &ordinary,
        distinct_predecessor,
        &projection,
    )) != null);
}

// A cloned block may have several authenticated incoming edges after a
// continuation closure is copied.  In that case nodeSplitLineageParent
// deliberately reports an ambiguous parent, but an exact rewrite on the
// current edge still proves the target relationship.  Keep this proof
// edge-specific instead of treating every block sharing a split root as one
// context.
fn sameNodeSplitDirectTargetLineage(
    rewrites: []const ir.CfgEdgeRewrite,
    left: ir.BlockId,
    right: ir.BlockId,
) bool {
    for (rewrites) |rewrite| {
        if (rewrite.rule == .node_split and
            rewrite.from.target == left and
            rewrite.to.target == right)
        {
            return true;
        }
    }
    return false;
}

fn findNodeSplitArmEdgeInGroup(
    rewrites: []const ir.CfgEdgeRewrite,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    from: ir.BlockId,
    to: ir.BlockId,
    group: ir.NodeSplitGroupId,
) ?ir.CfgEdgeRewrite {
    for (rewrites) |rewrite| {
        if (rewrite.rule == .node_split and
            rewrite.source == source and
            rewrite.kind == kind and
            rewrite.from.target == from and
            rewrite.to.target == to and
            rewrite.node_split_group == group)
        {
            return rewrite;
        }
    }
    return null;
}

fn findNodeSplitArmEdge(
    rewrites: []const ir.CfgEdgeRewrite,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    from: ir.BlockId,
    to: ir.BlockId,
) ?ir.CfgEdgeRewrite {
    for (rewrites) |rewrite| {
        if (rewrite.rule == .node_split and
            rewrite.source == source and
            rewrite.kind == kind and
            rewrite.from.target == from and
            rewrite.to.target == to and
            rewrite.node_split_group != null)
        {
            return rewrite;
        }
    }
    return null;
}

fn collisionContextsEquivalent(
    program: *const ir.Program,
    left: CollisionArm,
    right: CollisionArm,
    projection_context: *structural_overlap.ReplayProjectionContext,
    lineage_index: ?*const FeedbackLineageIndex,
) NormalizeError!bool {
    _ = lineage_index;
    if (left.context == null or right.context == null) {
        // An unknown context cannot consume a later authenticated context.
        // Both unknown contexts remain equivalent, but a parameterized loop
        // frontier needs its own proof rather than a lineage-only wildcard.
        if ((left.context == null) != (right.context == null)) return false;
        const adjacent_lineage = sameNodeSplitAdjacentArmLineageWithReplay(
            projection_context,
            left,
            right,
        );
        if (left.source != right.source and adjacent_lineage) {
            return false;
        }
        return true;
    }
    const left_context = left.context.?;
    const right_context = right.context.?;
    const stop_matches = left_context.stop == right_context.stop or
        (left_context.parameter_arguments != null and
            right_context.parameter_arguments != null and
            sameCollisionContextStopWithReplay(
                projection_context,
                program.edge_rewrites,
                left_context.stop,
                right_context.stop,
            ));
    const continue_matches = left_context.continue_target == right_context.continue_target or
        (left_context.parameter_arguments != null and
            right_context.parameter_arguments != null and
            sameCollisionContextContinueWithReplay(
                projection_context,
                program.edge_rewrites,
                left_context.continue_target,
                right_context.continue_target,
            ));
    if (!stop_matches or
        left_context.loop_exit != right_context.loop_exit or
        !continue_matches)
    {
        return false;
    }

    if (left_context.start != right_context.start) {
        const paired_with_target = left_context.start == left.target and
            right_context.start == right.target and
            projection_context.cloneLineageRoot(left.target) != null and
            projection_context.cloneLineageRoot(left.target) ==
                projection_context.cloneLineageRoot(right.target);
        const start_boundary = sameCollisionBoundaryWithReplay(
            projection_context,
            program.edge_rewrites,
            left_context.start,
            right_context.start,
        );
        if (!paired_with_target and !start_boundary) {
            return false;
        }
    }

    // Missing tuples do not prove distinction. When both are present, the
    // replay context must authenticate the value/pack projection at the
    // candidate target; type or shape equality alone is insufficient.
    if (left_context.parameter_arguments == null or right_context.parameter_arguments == null) return true;
    return try projection_context.parametersEquivalent(
        right.target,
        left_context.parameter_arguments,
        right_context.parameter_arguments,
    );
}

fn findPreviouslyTriedCollisionArm(
    program: *const ir.Program,
    arms: []const CollisionArm,
    candidate: CollisionArm,
    projection_context: *structural_overlap.ReplayProjectionContext,
) NormalizeError!?CollisionArm {
    return findPreviouslyTriedCollisionArmWithAnalysis(
        program,
        null,
        arms,
        candidate,
        projection_context,
    );
}

fn findPreviouslyTriedCollisionArmWithAnalysis(
    program: *const ir.Program,
    analysis: ?*const cfg.Analysis,
    arms: []const CollisionArm,
    candidate: CollisionArm,
    projection_context: *structural_overlap.ReplayProjectionContext,
) NormalizeError!?CollisionArm {
    return findPreviouslyTriedCollisionArmWithAnalysisAndLineage(
        program,
        analysis,
        arms,
        candidate,
        projection_context,
        null,
    );
}

fn findPreviouslyTriedCollisionArmWithAnalysisAndLineage(
    program: *const ir.Program,
    analysis: ?*const cfg.Analysis,
    arms: []const CollisionArm,
    candidate: CollisionArm,
    projection_context: *structural_overlap.ReplayProjectionContext,
    lineage_index: ?*const FeedbackLineageIndex,
) NormalizeError!?CollisionArm {
    for (arms) |arm| {
        const exact_position = arm.source == candidate.source and
            arm.kind == candidate.kind and
            arm.target == candidate.target;
        if (arm.reserved and !exact_position) continue;
        const owner_composed = if (analysis) |graph|
            try sameNodeSplitOwnerComposedArmLineageWithReplay(
                program,
                graph,
                projection_context,
                arm,
                candidate,
            )
        else
            false;
        const position_matches = sameCollisionArmPositionWithReplay(
            projection_context,
            arm,
            candidate,
        ) or sameNodeSplitPairedArmLineageWithReplay(
            program,
            projection_context,
            arm,
            candidate,
        ) or owner_composed;
        if (!position_matches) continue;
        if (analysis) |graph| {
            // Clone lineage and projected tuples identify a possible
            // continuation family, but they do not authenticate the live
            // edge being scheduled. An unauthenticated non-identical edge
            // must remain fresh so the contextual splitter can prove its own
            // ownership boundary.
            if (!exact_position and !try projection_context.hasAuthenticatedContinuationBridgeForEdge(
                graph,
                .{
                    .source = candidate.source,
                    .kind = candidate.kind,
                    .target = candidate.target,
                },
            )) continue;
        }
        const context_matches = try collisionContextsEquivalent(
            program,
            arm,
            candidate,
            projection_context,
            lineage_index,
        );
        if (context_matches) return arm;
    }
    return null;
}

const NodeSplitLineageParent = struct {
    block: ir.BlockId,
    group: ?ir.NodeSplitGroupId,
};

const NodeSplitLineageStep = union(enum) {
    none,
    invalid,
    parent: NodeSplitLineageParent,
};

const FeedbackArmRewriteKey = struct {
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    from: ir.BlockId,
    to: ir.BlockId,
};

const FeedbackGroupedArmRewriteKey = struct {
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    from: ir.BlockId,
    to: ir.BlockId,
    group: ir.NodeSplitGroupId,
};

/// Immutable rewrite ownership for one feedback scan.  The normalizer's
/// collision history is append-only, so parent and exact-edge ownership can
/// be indexed once per post-apply graph instead of rescanning every rewrite
/// for every prior arm.  Invalid or conflicting lineage remains rejected.
const FeedbackLineageIndex = struct {
    allocator: std.mem.Allocator,
    root_parents: []?ir.BlockId,
    root_invalid: []bool,
    lineage_parents: []?NodeSplitLineageParent,
    lineage_invalid: []bool,
    direct_edges: std.AutoHashMapUnmanaged(FeedbackArmRewriteKey, void) = .empty,
    grouped_edges: std.AutoHashMapUnmanaged(FeedbackGroupedArmRewriteKey, void) = .empty,

    fn init(allocator: std.mem.Allocator, program: *const ir.Program) NormalizeError!FeedbackLineageIndex {
        const root_parents = try allocator.alloc(?ir.BlockId, program.blocks.len);
        errdefer allocator.free(root_parents);
        @memset(root_parents, null);
        const root_invalid = try allocator.alloc(bool, program.blocks.len);
        errdefer allocator.free(root_invalid);
        @memset(root_invalid, false);
        const lineage_parents = try allocator.alloc(?NodeSplitLineageParent, program.blocks.len);
        errdefer allocator.free(lineage_parents);
        @memset(lineage_parents, null);
        const lineage_invalid = try allocator.alloc(bool, program.blocks.len);
        errdefer allocator.free(lineage_invalid);
        @memset(lineage_invalid, false);

        var index = FeedbackLineageIndex{
            .allocator = allocator,
            .root_parents = root_parents,
            .root_invalid = root_invalid,
            .lineage_parents = lineage_parents,
            .lineage_invalid = lineage_invalid,
        };
        errdefer index.deinit();

        for (program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split) continue;
            if (rewrite.to.target.index() >= program.blocks.len) continue;

            const target_index = rewrite.to.target.index();
            if (index.root_parents[target_index]) |existing| {
                if (existing != rewrite.from.target) index.root_invalid[target_index] = true;
            } else {
                index.root_parents[target_index] = rewrite.from.target;
            }
            const candidate_parent: NodeSplitLineageParent = .{
                .block = rewrite.from.target,
                .group = rewrite.node_split_group,
            };
            if (index.lineage_parents[target_index]) |existing| {
                if (existing.block != candidate_parent.block or
                    existing.group != candidate_parent.group)
                {
                    index.lineage_invalid[target_index] = true;
                }
            } else {
                index.lineage_parents[target_index] = candidate_parent;
            }

            try index.direct_edges.put(index.allocator, .{
                .source = rewrite.source,
                .kind = rewrite.kind,
                .from = rewrite.from.target,
                .to = rewrite.to.target,
            }, {});
            if (rewrite.node_split_group) |group| {
                try index.grouped_edges.put(index.allocator, .{
                    .source = rewrite.source,
                    .kind = rewrite.kind,
                    .from = rewrite.from.target,
                    .to = rewrite.to.target,
                    .group = group,
                }, {});
            }
        }
        return index;
    }

    fn deinit(self: *FeedbackLineageIndex) void {
        self.grouped_edges.deinit(self.allocator);
        self.direct_edges.deinit(self.allocator);
        self.allocator.free(self.lineage_invalid);
        self.allocator.free(self.lineage_parents);
        self.allocator.free(self.root_invalid);
        self.allocator.free(self.root_parents);
        self.* = undefined;
    }

    fn root(self: *const FeedbackLineageIndex, block: ir.BlockId) ?ir.BlockId {
        if (block.index() >= self.root_parents.len or self.root_invalid[block.index()]) return null;
        var current = block;
        var depth: usize = 0;
        while (true) {
            if (current.index() >= self.root_parents.len or self.root_invalid[current.index()]) return null;
            const parent = self.root_parents[current.index()] orelse return current;
            if (parent == current or depth >= self.root_parents.len) return null;
            current = parent;
            depth += 1;
        }
    }

    fn lineageParent(self: *const FeedbackLineageIndex, block: ir.BlockId) NodeSplitLineageStep {
        if (block.index() >= self.lineage_parents.len or self.lineage_invalid[block.index()]) return .invalid;
        return if (self.lineage_parents[block.index()]) |parent|
            .{ .parent = parent }
        else
            .none;
    }

    fn sameLineage(self: *const FeedbackLineageIndex, left: ir.BlockId, right: ir.BlockId) bool {
        const left_root = self.root(left) orelse return false;
        const right_root = self.root(right) orelse return false;
        if (left_root != right_root) return false;

        var left_current = left;
        var right_current = right;
        var depth: usize = 0;
        while (depth <= self.lineage_parents.len) : (depth += 1) {
            const left_parent = self.lineageParent(left_current);
            const right_parent = self.lineageParent(right_current);
            switch (left_parent) {
                .invalid => return false,
                .none => return switch (right_parent) {
                    .none => true,
                    else => false,
                },
                .parent => |left_step| switch (right_parent) {
                    .invalid, .none => return false,
                    .parent => |right_step| {
                        if (left_step.block != right_step.block or left_step.group != right_step.group) return false;
                        left_current = left_step.block;
                        right_current = right_step.block;
                    },
                },
            }
        }
        return false;
    }

    fn hasDirectEdge(
        self: *const FeedbackLineageIndex,
        source: ir.BlockId,
        kind: ir.CfgEdgeKind,
        from: ir.BlockId,
        to: ir.BlockId,
    ) bool {
        return self.direct_edges.contains(.{ .source = source, .kind = kind, .from = from, .to = to });
    }

    fn hasGroupedEdge(
        self: *const FeedbackLineageIndex,
        source: ir.BlockId,
        kind: ir.CfgEdgeKind,
        from: ir.BlockId,
        to: ir.BlockId,
        group: ir.NodeSplitGroupId,
    ) bool {
        return self.grouped_edges.contains(.{
            .source = source,
            .kind = kind,
            .from = from,
            .to = to,
            .group = group,
        });
    }
};

fn sameNodeSplitRootBoundaryWithReplay(
    projection: *const structural_overlap.ReplayProjectionContext,
    left: ir.BlockId,
    right: ir.BlockId,
) bool {
    const left_root = projection.cloneLineageRoot(left) orelse return false;
    const right_root = projection.cloneLineageRoot(right) orelse return false;
    if (left_root != right_root) return false;
    if (left == left_root) {
        return if (projection.cloneLineageParent(right)) |parent|
            parent.block == left_root
        else
            false;
    }
    if (right == right_root) {
        return if (projection.cloneLineageParent(left)) |parent|
            parent.block == right_root
        else
            false;
    }
    return false;
}

fn sameNodeSplitAdjacentArmLineageWithReplay(
    projection: *const structural_overlap.ReplayProjectionContext,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    if (left.kind != right.kind) return false;
    const left_parent = projection.cloneLineageParent(left.target);
    const right_parent = projection.cloneLineageParent(right.target);
    const left_to_right = left_parent != null and left_parent.?.block == right.target;
    const right_to_left = right_parent != null and right_parent.?.block == left.target;
    return (left_to_right and projection.hasNodeSplitArmEdge(
        left.source,
        left.kind,
        right.target,
        left.target,
        null,
    )) or (right_to_left and projection.hasNodeSplitArmEdge(
        right.source,
        right.kind,
        left.target,
        right.target,
        null,
    ));
}

fn sameNodeSplitAncestorArmLineageWithReplay(
    projection: *const structural_overlap.ReplayProjectionContext,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    if (left.kind != right.kind or left.source != right.source or left.target == right.target) return false;
    var current = right.target;
    var depth: usize = 0;
    while (current != left.target) : (depth += 1) {
        if (depth > projection.blockCount()) return false;
        const parent = projection.cloneLineageParent(current) orelse return false;
        if (!projection.hasNodeSplitArmEdge(right.source, right.kind, parent.block, current, null)) return false;
        current = parent.block;
    }
    return true;
}

fn sameNodeSplitPairedArmLineageForwardWithReplay(
    program: *const ir.Program,
    projection: *const structural_overlap.ReplayProjectionContext,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    if (left.kind != right.kind or
        (left.source == right.source and left.target == right.target)) return false;
    var current_source = right.source;
    var current_target = right.target;
    var steps: usize = 0;
    var paired_steps: usize = 0;
    while (current_source != left.source or current_target != left.target) : (steps += 1) {
        if (steps >= program.blocks.len) return false;
        const source_parent = projection.cloneLineageParent(current_source);
        const target_parent = projection.cloneLineageParent(current_target);
        if (source_parent) |source_step| {
            if (target_parent) |target_step| {
                if (source_step.group == target_step.group and projection.hasNodeSplitArmEdge(
                    current_source,
                    right.kind,
                    target_step.block,
                    current_target,
                    source_step.group,
                )) {
                    if (steps == 0) {
                        const live = cfg_edge.value(program, .{
                            .source = current_source,
                            .kind = right.kind,
                            .target = current_target,
                        }) orelse return false;
                        const rewrite = findNodeSplitArmEdgeInGroup(
                            program.edge_rewrites,
                            current_source,
                            right.kind,
                            target_step.block,
                            current_target,
                            source_step.group,
                        ) orelse return false;
                        if (live.target != current_target or
                            !std.mem.eql(ir.ValueId, live.arguments, rewrite.to.arguments)) return false;
                    }
                    current_source = source_step.block;
                    current_target = target_step.block;
                    paired_steps += 1;
                    continue;
                }
            }
        }
        const target_step = target_parent orelse return false;
        if (!projection.hasNodeSplitArmEdge(
            current_source,
            right.kind,
            target_step.block,
            current_target,
            null,
        )) return false;
        if (steps == 0) {
            const live = cfg_edge.value(program, .{
                .source = current_source,
                .kind = right.kind,
                .target = current_target,
            }) orelse return false;
            const rewrite = findNodeSplitArmEdge(
                program.edge_rewrites,
                current_source,
                right.kind,
                target_step.block,
                current_target,
            ) orelse return false;
            if (live.target != current_target or
                !std.mem.eql(ir.ValueId, live.arguments, rewrite.to.arguments)) return false;
        }
        current_target = target_step.block;
    }
    return steps != 0 and paired_steps != 0;
}

fn sameNodeSplitPairedArmLineageWithReplay(
    program: *const ir.Program,
    projection: *const structural_overlap.ReplayProjectionContext,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    return sameNodeSplitPairedArmLineageForwardWithReplay(program, projection, left, right) or
        sameNodeSplitPairedArmLineageForwardWithReplay(program, projection, right, left);
}

// A continuation may clone both endpoints of the owner arm through separate
// split groups.  The parent pair identifies the owner; the live-edge bridge
// authenticates the handoff and its complete tuple.  Group equality is not a
// proof requirement because source and target endpoints can be split by
// different structural decisions.
fn sameNodeSplitOwnerComposedArmLineageWithReplay(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    projection: *structural_overlap.ReplayProjectionContext,
    owner: CollisionArm,
    candidate: CollisionArm,
) NormalizeError!bool {
    if (owner.kind != candidate.kind or
        owner.source == candidate.source or
        owner.target == candidate.target)
    {
        return false;
    }
    if (owner.source.index() >= program.blocks.len or
        owner.target.index() >= program.blocks.len or
        program.blocks[owner.source.index()].id != owner.source or
        program.blocks[owner.target.index()].id != owner.target)
    {
        return false;
    }
    const source_parent = projection.cloneLineageParent(candidate.source) orelse return false;
    const target_parent = projection.cloneLineageParent(candidate.target) orelse return false;
    if (source_parent.block != owner.source or target_parent.block != owner.target) return false;
    return try projection.hasAuthenticatedOwnerComposedContinuationBridgeForEdge(
        analysis,
        .{
            .source = candidate.source,
            .kind = candidate.kind,
            .target = candidate.target,
        },
    );
}

fn sameCollisionArmPositionWithReplay(
    projection: *const structural_overlap.ReplayProjectionContext,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    if (left.kind != right.kind) return false;
    if ((left.source == right.source and
        projection.hasNodeSplitArmEdge(left.source, left.kind, left.target, right.target, null)) or
        (left.source == right.source and
            projection.hasNodeSplitArmEdge(right.source, right.kind, right.target, left.target, null))) return true;
    if (sameNodeSplitAdjacentArmLineageWithReplay(projection, left, right)) return true;
    if (left.source != right.source and !projection.sameCloneLineage(left.source, right.source)) return false;
    return left.target == right.target or
        sameNodeSplitAncestorArmLineageWithReplay(projection, left, right) or
        sameNodeSplitAncestorArmLineageWithReplay(projection, right, left) or
        projection.sameCloneLineage(left.target, right.target) or
        sameNodeSplitRootBoundaryWithReplay(projection, left.target, right.target);
}

fn sameCollisionBoundaryWithReplay(
    projection: *const structural_overlap.ReplayProjectionContext,
    rewrites: []const ir.CfgEdgeRewrite,
    left: ir.BlockId,
    right: ir.BlockId,
) bool {
    return left == right or projection.sameCloneLineage(left, right) or
        sameNodeSplitDirectTargetLineage(rewrites, left, right);
}

fn sameCollisionContextStopWithReplay(
    projection: *const structural_overlap.ReplayProjectionContext,
    rewrites: []const ir.CfgEdgeRewrite,
    left: ?ir.BlockId,
    right: ?ir.BlockId,
) bool {
    if (left == null or right == null) return left == right;
    if (sameCollisionBoundaryWithReplay(projection, rewrites, left.?, right.?)) return true;
    const left_root = projection.cloneLineageRoot(left.?) orelse return false;
    const right_root = projection.cloneLineageRoot(right.?) orelse return false;
    return left_root == right_root;
}

fn sameCollisionContextContinueWithReplay(
    projection: *const structural_overlap.ReplayProjectionContext,
    rewrites: []const ir.CfgEdgeRewrite,
    left: ?ir.BlockId,
    right: ?ir.BlockId,
) bool {
    if (left == null or right == null) return left == right;
    return sameCollisionBoundaryWithReplay(projection, rewrites, left.?, right.?);
}

const FreshAlternativeContext = union(enum) {
    fixed: ?structure.CollisionContext,
    deferred: CollisionArm,
};
