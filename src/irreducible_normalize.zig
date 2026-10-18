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
const stage_trace = @import("stage_trace.zig");

pub const NormalizeError = error{NormalizationInvariantFailed} || std.mem.Allocator.Error;

pub const NormalizeOptions = struct {
    // A bounded feedback pass returns the current serialized IR instead of
    // treating the budget as a normalization failure. The next invocation
    // can resume from that IR and retain its authenticated rewrite history.
    feedback_iteration_limit: ?usize = null,
    // Checkpoints are emitted after the irreducible and overlap phases. A
    // resumed pass must not pay for those already-proven scans again.
    skip_initial_phases: bool = false,
    initial_resume_seed: ?ResumeSeed = null,
};

const trace_normalize_phases = build_options.trace_normalize_phases;

fn normalizePhaseNow() i96 {
    if (!trace_normalize_phases) return 0;
    return Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds;
}

fn normalizePhaseMillis(start: i96) i64 {
    if (!trace_normalize_phases) return 0;
    return @intCast(@divTrunc(normalizePhaseNow() - start, std.time.ns_per_ms));
}

fn traceNormalize(comptime format: []const u8, args: anytype) void {
    if (trace_normalize_phases) std.debug.print(format, args);
}

fn traceAppliedSplit(phase: []const u8, function_index: usize, before: Result, after: Result) void {
    traceNormalize("normalize_research phase={s} function={} blocks={} instructions={} values={} packs={} rewrite_start={} rewrite_end={}\n", .{
        phase,
        function_index,
        after.cloned_blocks - before.cloned_blocks,
        after.cloned_instructions - before.cloned_instructions,
        after.cloned_values - before.cloned_values,
        after.cloned_packs - before.cloned_packs,
        before.program.edge_rewrites.len,
        after.program.edge_rewrites.len,
    });
}

const max_structural_clone_expansion = 4;

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

const OverlapIdentity = struct {
    branch: ir.BlockId,
    entry: ir.BlockId,
    join: ir.BlockId,
    entry_measure_kind: structural_overlap.EntryMeasureKind,
};

const PreparedSecondary = struct {
    external: structural_overlap.ExternalCloneMappings,
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

const CollisionSeedValidation = enum {
    live,
    invalid_function,
    missing_provenance,
    invalid_block,
    unreachable_graph,
    missing_live_edge,
    live_target_mismatch,
    missing_rewrite,
    forwarding_shape_mismatch,
    owner_edge_missing,
    owner_edge_mismatch,
    owner_tuple_mismatch,
    no_reentry,
    parameter_mismatch,
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

fn collisionSeedFromResumeSeed(seed: ResumeSeed) CollisionSeed {
    return .{
        .function_index = seed.function_index,
        .target = seed.target,
        .source = seed.source,
        .kind = seed.kind,
        .original_target = seed.original_target,
        .previous = seed.previous,
        .context = .{
            .start = seed.context_start,
            .stop = seed.context_stop,
            .loop_exit = seed.context_loop_exit,
            .continue_target = seed.context_continue_target,
            .parameter_arguments = seed.parameter_arguments,
        },
        .proof = seed.proof,
    };
}

fn resumeSeedFromCollisionSeed(seed: CollisionSeed) ?ResumeSeed {
    const context = seed.context orelse return null;
    const source = seed.source orelse return null;
    const kind = seed.kind orelse return null;
    const original_target = seed.original_target orelse return null;
    const previous = seed.previous orelse return null;
    return .{
        .function_index = seed.function_index,
        .target = seed.target,
        .source = source,
        .kind = kind,
        .original_target = original_target,
        .previous = previous,
        .context_start = context.start,
        .context_stop = context.stop,
        .context_loop_exit = context.loop_exit,
        .context_continue_target = context.continue_target,
        .parameter_arguments = context.parameter_arguments,
        .proof = seed.proof,
    };
}

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

fn collisionSeedForAppliedArmWithPrevious(
    function_index: usize,
    target: ir.BlockId,
    arm: CollisionArm,
    previous: ?ir.BlockId,
) ?CollisionSeed {
    if (arm.context == null) return null;
    var seed = collisionSeedForAppliedArm(function_index, target, arm);
    // The first authenticated split has no earlier collision arm, but its
    // original target is still the owned continuation that the clone must
    // re-enter. Retain that proof so the next feedback iteration can use the
    // live node-split edge instead of rebuilding the full structural plan.
    seed.previous = previous orelse arm.target;
    return seed;
}

fn appliedCloneForBlock(
    block: ir.BlockId,
    closure: []const ir.BlockId,
    clone_base: usize,
) ?ir.BlockId {
    for (closure, 0..) |source, index| {
        if (source == block) return ir.BlockId.fromIndex(clone_base + index);
    }
    return null;
}

fn remapCollisionContextThroughAppliedClone(
    context: structure.CollisionContext,
    closure: []const ir.BlockId,
    clone_base: usize,
) structure.CollisionContext {
    var remapped = context;
    if (appliedCloneForBlock(context.start, closure, clone_base)) |clone| {
        remapped.start = clone;
    }
    if (context.stop) |block| {
        if (appliedCloneForBlock(block, closure, clone_base)) |clone| remapped.stop = clone;
    }
    if (context.loop_exit) |block| {
        if (appliedCloneForBlock(block, closure, clone_base)) |clone| remapped.loop_exit = clone;
    }
    if (context.continue_target) |block| {
        if (appliedCloneForBlock(block, closure, clone_base)) |clone| remapped.continue_target = clone;
    }
    return remapped;
}

// A feedback split publishes new block IDs while the old closure members stay
// in the IR for provenance.  A resume seed must name the live clone as its
// owner, not the now-unreachable historical block.  If the owner was not
// cloned and is no longer reachable, discard the scheduling hint and let the
// next full scan rebuild it from the live graph.
fn collisionSeedForAppliedArmAfterApply(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function_index: usize,
    target: ir.BlockId,
    arm: CollisionArm,
    previous: ?ir.BlockId,
    closure: []const ir.BlockId,
    clone_base: usize,
) NormalizeError!?CollisionSeed {
    if (function_index >= program.functions.len) return null;
    var analysis = cfg.Analysis.init(
        allocator,
        program,
        program.functions[function_index],
    ) catch |err| switch (err) {
        error.InvalidCfg => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();

    if (!analysis.isReachable(target)) return null;
    const historical_owner = previous orelse arm.target;
    const owner = appliedCloneForBlock(historical_owner, closure, clone_base) orelse historical_owner;
    if (!analysis.isReachable(owner)) return null;
    // The live target may itself be the remapped owner.  Reflexive
    // reachability is enough to preserve the authenticated scheduling hint;
    // seededCollisionStatus performs the later non-empty-cycle check before
    // the hint can drive another split.
    const has_reentry = try analysis.canReach(target, owner);
    if (!has_reentry) return null;

    var seed = collisionSeedForAppliedArmWithPrevious(
        function_index,
        target,
        arm,
        owner,
    ) orelse return null;
    seed.context = remapCollisionContextThroughAppliedClone(
        seed.context.?,
        closure,
        clone_base,
    );
    return seed;
}

// A lineage fold leaves a live edge at the authenticated owner while its
// clone-fold record identifies the historical clone that was removed from
// that edge. Preserve that exact boundary as a resume cursor only when the
// post-fold graph still has a cyclic re-entry and the structured context can
// be moved from the clone to its owner.
fn collisionSeedForCloneFoldRewrite(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function_index: usize,
    rewrite: ir.CfgEdgeRewrite,
    context: ?structure.CollisionContext,
    projection: *const structural_overlap.ReplayProjectionContext,
) NormalizeError!?CollisionSeed {
    if (rewrite.rule != .clone_fold or rewrite.node_split_group == null or
        function_index >= program.functions.len or
        rewrite.source.index() >= program.blocks.len or
        rewrite.from.target.index() >= program.blocks.len or
        rewrite.to.target.index() >= program.blocks.len)
    {
        return null;
    }
    const function_id = program.functions[function_index].id;
    if (program.blocks[rewrite.source.index()].function != function_id or
        program.blocks[rewrite.from.target.index()].function != function_id or
        program.blocks[rewrite.to.target.index()].function != function_id)
    {
        return null;
    }
    const parent = projection.cloneLineageParent(rewrite.from.target) orelse return null;
    if (parent.block != rewrite.to.target or parent.group != rewrite.node_split_group.?) return null;

    const reference = ir.CfgEdgeRef{
        .source = rewrite.source,
        .kind = rewrite.kind,
        .target = rewrite.to.target,
    };
    const live = cfg_edge.value(program, reference) orelse return null;
    if (!std.mem.eql(ir.ValueId, live.arguments, rewrite.to.arguments)) return null;

    var analysis = cfg.Analysis.init(
        allocator,
        program,
        program.functions[function_index],
    ) catch |err| switch (err) {
        error.InvalidCfg => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    if (!analysis.isReachable(rewrite.source) or
        !analysis.isReachable(rewrite.to.target) or
        !try analysis.canReachNonEmptyPath(rewrite.to.target, rewrite.to.target))
    {
        return null;
    }

    var remapped_context = context orelse return null;
    if (remapped_context.start != rewrite.from.target) return null;
    remapped_context.start = rewrite.to.target;
    if (remapped_context.stop) |block| {
        if (block == rewrite.from.target) remapped_context.stop = rewrite.to.target;
    }
    if (remapped_context.loop_exit) |block| {
        if (block == rewrite.from.target) remapped_context.loop_exit = rewrite.to.target;
    }
    if (remapped_context.continue_target) |block| {
        if (block == rewrite.from.target) remapped_context.continue_target = rewrite.to.target;
    }
    if (remapped_context.parameter_arguments) |arguments| {
        if (!std.mem.eql(ir.ValueId, arguments, live.arguments)) return null;
    } else if (live.arguments.len != 0) {
        return null;
    }

    return .{
        .function_index = function_index,
        .target = rewrite.to.target,
        .source = rewrite.source,
        .kind = rewrite.kind,
        .original_target = rewrite.from.target,
        .previous = rewrite.to.target,
        .context = remapped_context,
        .proof = .clone_fold,
    };
}

fn collisionSeedForLatestCloneFold(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function_index: usize,
    rewrite_start: usize,
    context: ?structure.CollisionContext,
    projection: *const structural_overlap.ReplayProjectionContext,
) NormalizeError!?CollisionSeed {
    var index = program.edge_rewrites.len;
    while (index > rewrite_start) {
        index -= 1;
        const rewrite = program.edge_rewrites[index];
        if (rewrite.rule != .clone_fold) continue;
        if (try collisionSeedForCloneFoldRewrite(
            allocator,
            program,
            function_index,
            rewrite,
            context,
            projection,
        )) |seed| return seed;
    }
    return null;
}

// Older checkpoints may have serialized the historical owner itself.  When
// that owner was the direct target replaced by the authenticated node-split
// rewrite, rebase the seed onto the live clone before validating it.  This is
// deliberately limited to the exact rewrite and a real clone-local cycle;
// an arbitrary reachable clone must still fall back to a fresh scan.
fn rebaseUnreachableNodeSplitSeedOwner(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    seed: *CollisionSeed,
    projection: *structural_overlap.ReplayProjectionContext,
) NormalizeError!bool {
    const previous = seed.previous orelse return false;
    if (seed.proof != .node_split or
        seed.original_target == null or
        previous != seed.original_target.? or
        analysis.isReachable(previous) or
        !analysis.isReachable(seed.source orelse return false) or
        !analysis.isReachable(seed.target)) return false;

    const rewrite = findNodeSplitArmEdge(
        program.edge_rewrites,
        seed.source.?,
        seed.kind orelse return false,
        seed.original_target.?,
        seed.target,
    ) orelse return false;
    _ = rewrite.node_split_group orelse return false;
    if (!try authenticatedSourceOwnedNodeSplitStep(
        program,
        projection,
        rewrite,
        analysis.function,
    )) return false;
    if (!try analysis.canReachNonEmptyPath(seed.target, seed.target)) return false;

    var context = seed.context orelse return false;
    if (context.start == previous) context.start = seed.target;
    if (context.stop) |block| {
        if (block == previous) context.stop = seed.target;
    }
    if (context.loop_exit) |block| {
        if (block == previous) context.loop_exit = seed.target;
    }
    if (context.continue_target) |block| {
        if (block == previous) context.continue_target = seed.target;
    }
    seed.previous = seed.target;
    seed.context = context;
    return true;
}

// A paired replay fold has already authenticated the owner/candidate lineage
// before replacing the candidate edge with a forwarding edge. Preserve that
// proof for one feedback iteration so the scheduler does not immediately
// rebuild the full structural plan. The owner context is the post-fold target
// context; the candidate context described the pre-fold target and cannot be
// reused for the owner tuple.
fn collisionSeedForPairedForwarding(
    function_index: usize,
    owner: CollisionArm,
    candidate: CollisionArm,
) ?CollisionSeed {
    if (owner.context == null) return null;
    return .{
        .function_index = function_index,
        .target = owner.target,
        .source = candidate.source,
        .kind = candidate.kind,
        .original_target = candidate.target,
        .previous = owner.source,
        .context = owner.context,
        .proof = .paired_forwarding,
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

test "first authenticated split seeds its original target as reentry owner" {
    const seed = collisionSeedForAppliedArmWithPrevious(
        7,
        ir.BlockId.fromIndex(30),
        .{
            .source = ir.BlockId.fromIndex(31),
            .kind = .jump,
            .target = ir.BlockId.fromIndex(32),
            .context = .{
                .start = ir.BlockId.fromIndex(32),
                .stop = null,
                .loop_exit = null,
                .continue_target = null,
            },
        },
        null,
    ).?;
    try std.testing.expectEqual(ir.BlockId.fromIndex(32), seed.previous.?);
}

test "post-apply seed remaps a cloned owner to a reachable block" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const historical_owner = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const context = structure.CollisionContext{
        .start = historical_owner,
        .stop = historical_owner,
        .loop_exit = null,
        .continue_target = historical_owner,
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = clone } } },
        .{ .id = historical_owner, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = clone, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, historical_owner, clone },
        .entry_block = entry,
    };
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = entry,
        .kind = .jump,
        .from = .{ .target = historical_owner },
        .to = .{ .target = clone },
        .rule = .node_split,
        .node_split_group = group,
    }};
    const program = ir.Program{
        .program_id = "post-apply-live-owner",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };
    const closure = [_]ir.BlockId{historical_owner};
    const seed = (try collisionSeedForAppliedArmAfterApply(
        std.testing.allocator,
        &program,
        0,
        clone,
        .{
            .source = entry,
            .kind = .jump,
            .target = historical_owner,
            .context = context,
        },
        historical_owner,
        &closure,
        2,
    )).?;

    try std.testing.expectEqual(clone, seed.previous.?);
    try std.testing.expectEqual(clone, seed.context.?.start);
    try std.testing.expectEqual(clone, seed.context.?.stop.?);
    try std.testing.expectEqual(clone, seed.context.?.continue_target.?);
}

test "post-apply seed rejects an unreachable owner without a clone mapping" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const historical_owner = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = clone } } },
        .{ .id = historical_owner, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = clone, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, historical_owner, clone },
        .entry_block = entry,
    };
    const program = ir.Program{
        .program_id = "post-apply-unmapped-owner",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    const context = structure.CollisionContext{
        .start = historical_owner,
        .stop = null,
        .loop_exit = null,
        .continue_target = null,
    };
    const seed = try collisionSeedForAppliedArmAfterApply(
        std.testing.allocator,
        &program,
        0,
        clone,
        .{
            .source = entry,
            .kind = .jump,
            .target = historical_owner,
            .context = context,
        },
        historical_owner,
        &.{},
        3,
    );
    try std.testing.expect(seed == null);
}

test "fallback collision context requires the exact live edge tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const other_target = ir.BlockId.fromIndex(2);
    const first_argument = ir.ValueId.fromIndex(0);
    const second_argument = ir.ValueId.fromIndex(1);
    const edge_arguments = [_]ir.ValueId{ first_argument, second_argument };
    const mismatched_arguments = [_]ir.ValueId{ first_argument, ir.ValueId.fromIndex(2) };
    const blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = edge_arguments[0..],
        } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = other_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ source, target, other_target },
        .entry_block = source,
    }};
    const program = ir.Program{
        .program_id = "fallback-context-edge-tuple",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    const reference = ir.CfgEdgeRef{ .source = source, .kind = .jump, .target = target };
    const matching: structure.CollisionContext = .{
        .start = target,
        .stop = null,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = edge_arguments[0..],
    };

    const retained = fallbackCollisionContextForArm(&program, reference, matching);
    try std.testing.expect(retained != null);
    try std.testing.expectEqual(target, retained.?.start);

    var wrong_target = matching;
    wrong_target.start = other_target;
    try std.testing.expect(
        fallbackCollisionContextForArm(&program, reference, wrong_target) == null,
    );

    var wrong_tuple = matching;
    wrong_tuple.parameter_arguments = mismatched_arguments[0..];
    try std.testing.expect(
        fallbackCollisionContextForArm(&program, reference, wrong_tuple) == null,
    );

    var missing_tuple = matching;
    missing_tuple.parameter_arguments = null;
    try std.testing.expect(
        fallbackCollisionContextForArm(&program, reference, missing_tuple) == null,
    );
}

test "fresh collision alternatives remain tuple-sensitive" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const first_argument = ir.ValueId.fromIndex(0);
    const second_argument = ir.ValueId.fromIndex(1);
    const edge_arguments = [_]ir.ValueId{first_argument};
    const distinct_arguments = [_]ir.ValueId{second_argument};
    const blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = edge_arguments[0..],
        } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ source, target },
        .entry_block = source,
    };
    const program = ir.Program{
        .program_id = "tuple-sensitive-freshness",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    const matching: structure.CollisionContext = .{
        .start = target,
        .stop = null,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = edge_arguments[0..],
    };
    const distinct: structure.CollisionContext = .{
        .start = target,
        .stop = null,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = distinct_arguments[0..],
    };
    const prior = [_]CollisionArm{.{
        .source = source,
        .kind = .jump,
        .target = target,
        .context = matching,
    }};

    const repeated = structural_overlap.Split{
        .allocator = std.testing.allocator,
        .function_index = 0,
        .branch = source,
        .entry = source,
        .join = target,
        .incoming = try std.testing.allocator.dupe(ir.CfgEdgeRef, &.{.{
            .source = source,
            .kind = .jump,
            .target = target,
        }}),
        .closure = try std.testing.allocator.dupe(ir.BlockId, &.{source}),
    };
    try std.testing.expect((try freshCollisionAlternative(
        &program,
        repeated,
        &prior,
        null,
        matching,
    )) == null);

    const distinct_candidate = structural_overlap.Split{
        .allocator = std.testing.allocator,
        .function_index = 0,
        .branch = source,
        .entry = source,
        .join = target,
        .incoming = try std.testing.allocator.dupe(ir.CfgEdgeRef, &.{.{
            .source = source,
            .kind = .jump,
            .target = target,
        }}),
        .closure = try std.testing.allocator.dupe(ir.BlockId, &.{source}),
    };
    var fresh = (try freshCollisionAlternative(
        &program,
        distinct_candidate,
        &prior,
        null,
        distinct,
    )).?;
    defer fresh.deinit();
    try std.testing.expectEqual(source, fresh.incoming[0].source);
}

const DeferredCollisionAlternative = struct {
    split: structural_overlap.Split,
};

const Scan = struct {
    plan: ?SplitPlan = null,
    entry_measure: usize = 0,

    fn deinit(self: *Scan) void {
        if (self.plan) |*plan| plan.deinit();
        self.* = undefined;
    }
};

pub fn normalizeInArena(allocator: std.mem.Allocator, source: *const ir.Program) NormalizeError!Result {
    return normalizeWithScratchInArena(allocator, allocator, source);
}

pub fn normalizeControlInArena(allocator: std.mem.Allocator, source: *const ir.Program) NormalizeError!Result {
    return normalizeControlWithScratchInArena(allocator, allocator, source);
}

pub fn normalizeWithScratchInArena(
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    source: *const ir.Program,
) NormalizeError!Result {
    return normalizeImpl(allocator, scratch_allocator, source, true, null, .{});
}

pub fn normalizeFunctionWithScratchInArena(
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    source: *const ir.Program,
    function_index: usize,
) NormalizeError!Result {
    return normalizeImpl(allocator, scratch_allocator, source, true, function_index, .{});
}

pub fn normalizeFunctionWithScratchInArenaBudget(
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    source: *const ir.Program,
    function_index: usize,
    feedback_iteration_limit: usize,
) NormalizeError!Result {
    return normalizeImpl(
        allocator,
        scratch_allocator,
        source,
        true,
        function_index,
        .{ .feedback_iteration_limit = feedback_iteration_limit },
    );
}

pub fn normalizeFunctionWithScratchInArenaResumeBudget(
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    source: *const ir.Program,
    function_index: usize,
    feedback_iteration_limit: usize,
) NormalizeError!Result {
    return normalizeFunctionWithScratchInArenaResumeSeedBudget(
        allocator,
        scratch_allocator,
        source,
        function_index,
        feedback_iteration_limit,
        null,
    );
}

pub fn normalizeFunctionWithScratchInArenaResumeSeedBudget(
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    source: *const ir.Program,
    function_index: usize,
    feedback_iteration_limit: usize,
    initial_resume_seed: ?ResumeSeed,
) NormalizeError!Result {
    return normalizeImpl(
        allocator,
        scratch_allocator,
        source,
        true,
        function_index,
        .{
            .feedback_iteration_limit = feedback_iteration_limit,
            .skip_initial_phases = true,
            .initial_resume_seed = initial_resume_seed,
        },
    );
}

pub fn normalizeControlWithScratchInArena(
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    source: *const ir.Program,
) NormalizeError!Result {
    return normalizeImpl(allocator, scratch_allocator, source, false, null, .{});
}

// Remove only semantically transparent forwarding blocks before control
// restructuring.  Keep the blocks and record each edge substitution so the
// admitted history remains replayable and auditable.
fn collapseTransparentForwardingBlocks(
    allocator: std.mem.Allocator,
    program: *ir.Program,
    blocks: *std.ArrayList(ir.Block),
    rewrites: *std.ArrayList(ir.CfgEdgeRewrite),
    only_function: ?usize,
) NormalizeError!usize {
    const selected_function = if (only_function) |function_index|
        if (function_index < program.functions.len) program.functions[function_index].id else return 0
    else
        null;
    var collapsed: usize = 0;
    var pass: usize = 0;
    const pass_limit = @max(blocks.items.len, 1);
    while (pass < pass_limit) : (pass += 1) {
        program.blocks = blocks.items;
        program.edge_rewrites = rewrites.items;

        const reachable = try allocator.alloc(bool, blocks.items.len);
        defer allocator.free(reachable);
        @memset(reachable, false);
        for (program.functions, 0..) |function, function_index| {
            if (only_function) |selected_index| if (function_index != selected_index) continue;
            var analysis = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
                error.InvalidCfg => continue,
                error.OutOfMemory => return error.OutOfMemory,
            };
            defer analysis.deinit();
            for (function.blocks) |block_id| {
                if (block_id.index() < reachable.len and analysis.isReachable(block_id)) {
                    reachable[block_id.index()] = true;
                }
            }
        }

        var changed = false;
        for (blocks.items, 0..) |candidate, candidate_index| {
            if (selected_function) |function_id| if (candidate.function != function_id) continue;
            if (!reachable[candidate_index] or candidate.parameters.len != 0 or
                candidate.instructions.len != 0)
            {
                continue;
            }
            var is_function_entry = false;
            for (program.functions, 0..) |function, function_index| {
                if (only_function) |selected_index| if (function_index != selected_index) continue;
                if (function.id == candidate.function and function.entry_block == candidate.id) {
                    is_function_entry = true;
                    break;
                }
            }
            if (is_function_entry) continue;

            const outgoing = switch (candidate.terminator) {
                .jump => |edge| edge,
                .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => continue,
            };
            if (outgoing.target == candidate.id or outgoing.target.index() >= blocks.items.len) {
                continue;
            }
            const target_block = blocks.items[outgoing.target.index()];
            if (target_block.id != outgoing.target or target_block.function != candidate.function or
                outgoing.arguments.len != target_block.parameters.len or
                (target_block.parameters.len != 0 and
                    !node_split.parametersAreCanonical(program.values, target_block)))
            {
                continue;
            }
            // The rewrite history is replayed through the generic forwarding
            // contract. An empty block cannot lend an unrelated block
            // parameter to its successor tuple.
            if (!try forwardingJumpIsReplayable(allocator, program, candidate.id, outgoing)) continue;

            for (blocks.items, 0..) |*source_block, source_index| {
                if (source_index >= reachable.len or !reachable[source_index] or
                    source_block.id == candidate.id or source_block.function != candidate.function or
                    (selected_function != null and source_block.function != selected_function.?) or
                    isHistoricalForwardingTarget(rewrites.items, source_block.id))
                {
                    continue;
                }
                var kind: ?ir.CfgEdgeKind = null;
                var current: ?ir.Edge = null;
                switch (source_block.terminator) {
                    .jump => |edge| {
                        if (edge.target == candidate.id and edge.arguments.len == 0) {
                            kind = .jump;
                            current = edge;
                        }
                    },
                    .branch => |branch| {
                        if (branch.then_edge.target == candidate.id and branch.then_edge.arguments.len == 0) {
                            kind = .branch_then;
                            current = branch.then_edge;
                        } else if (branch.else_edge.target == candidate.id and branch.else_edge.arguments.len == 0) {
                            kind = .branch_else;
                            current = branch.else_edge;
                        }
                    },
                    .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
                }
                const edge_kind = kind orelse continue;
                const from = current.?;
                const replacement = ir.Edge{ .target = outgoing.target, .arguments = outgoing.arguments };
                switch (source_block.terminator) {
                    .jump => source_block.terminator = .{ .jump = replacement },
                    .branch => |branch| source_block.terminator = .{ .branch = if (edge_kind == .branch_then)
                        .{ .condition = branch.condition, .then_edge = replacement, .else_edge = branch.else_edge }
                    else
                        .{ .condition = branch.condition, .then_edge = branch.then_edge, .else_edge = replacement } },
                    .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => unreachable,
                }
                try rewrites.append(allocator, .{
                    .id = ir.EdgeRewriteId.fromIndex(rewrites.items.len),
                    .source = source_block.id,
                    .kind = edge_kind,
                    .from = .{ .target = from.target },
                    .to = replacement,
                    .rule = .forwarding_jump,
                });
                collapsed += 1;
                changed = true;
                program.blocks = blocks.items;
                program.edge_rewrites = rewrites.items;
            }
        }
        if (!changed) break;
    }
    return collapsed;
}

fn forwardingJumpIsReplayable(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    forwarding: ir.BlockId,
    outgoing: ir.Edge,
) NormalizeError!bool {
    const replayed = try control_flow.replayForwardingJump(
        allocator,
        program,
        .{ .target = forwarding },
    ) orelse return false;
    defer if (replayed.arguments.len != 0) allocator.free(replayed.arguments);
    return replayed.target == outgoing.target and
        std.mem.eql(ir.ValueId, replayed.arguments, outgoing.arguments);
}

fn isHistoricalForwardingTarget(
    rewrites: []const ir.CfgEdgeRewrite,
    block: ir.BlockId,
) bool {
    for (rewrites) |rewrite| {
        if (rewrite.rule == .forwarding_jump and rewrite.from.target == block) return true;
    }
    return false;
}

/// The disassembly short-circuit `or` block.  When the collision's
/// `previous` block E is a pure two-instruction `or` block (a constant and a
/// place_write of that result, no parameters, a parameterless jump to the
/// collided block) whose only two predecessors are branches that reach E on
/// their else edge with no arguments and leave on their then edge, one
/// dominating the other, return the inner (dominated) branch's else edge so
/// the feedback phase clones E for it.  Null when the shape does not hold.
fn shortCircuitElseCloneEdge(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    previous: ir.BlockId,
    collision: ir.BlockId,
) ?ir.CfgEdgeRef {
    if (previous.index() >= program.blocks.len) return null;
    const or_block = program.blocks[previous.index()];
    if (or_block.parameters.len != 0 or or_block.instructions.len != 2) return null;
    const jump = switch (or_block.terminator) {
        .jump => |edge| edge,
        else => return null,
    };
    if (jump.target != collision or jump.arguments.len != 0) return null;
    const constant_id = or_block.instructions[0];
    const write_id = or_block.instructions[1];
    if (constant_id.index() >= program.instructions.len or
        write_id.index() >= program.instructions.len) return null;
    const constant_instruction = program.instructions[constant_id.index()];
    switch (constant_instruction.operation) {
        .constant => {},
        else => return null,
    }
    if (constant_instruction.results.len != 1) return null;
    const constant_value = constant_instruction.results[0];
    const write_instruction = program.instructions[write_id.index()];
    switch (write_instruction.operation) {
        .place_write => |write| if (write.value != constant_value) return null,
        else => return null,
    }
    if (analysis.predecessorCount(previous) != 2) return null;
    const first_predecessor = analysis.predecessorAt(previous, 0) orelse return null;
    const second_predecessor = analysis.predecessorAt(previous, 1) orelse return null;
    if (!branchReachesElseWithoutArguments(program, first_predecessor, previous)) return null;
    if (!branchReachesElseWithoutArguments(program, second_predecessor, previous)) return null;
    const inner = if (analysis.dominates(first_predecessor, second_predecessor))
        second_predecessor
    else if (analysis.dominates(second_predecessor, first_predecessor))
        first_predecessor
    else
        return null;
    return .{ .source = inner, .kind = .branch_else, .target = previous };
}

/// The outgoing edges of a block whose
/// terminator is a `jump` (one edge) or a `branch` (then and else).  Null for a
/// `return`, `throw` or `unreachable` block, which never flows to the join.
const CompoundOrArmEdges = struct {
    edges: [2]ir.Edge,
    count: usize,

    fn slice(self: *const CompoundOrArmEdges) []const ir.Edge {
        return self.edges[0..self.count];
    }
};

fn compoundOrArmOutgoingEdges(terminator: ir.Terminator) ?CompoundOrArmEdges {
    return switch (terminator) {
        .jump => |edge| .{ .edges = .{ edge, undefined }, .count = 1 },
        .branch => |branch| .{ .edges = .{ branch.then_edge, branch.else_edge }, .count = 2 },
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => null,
    };
}

/// The generalization of the one-block
/// short-circuit `or` block to a multi-block compound `or` arm.  For an
/// `already_owned` collision at the statement join `join` whose owner context
/// stop is the `or`-arm entry `entry`: `entry` has exactly two predecessors,
/// both `branch` blocks reaching `entry` on their else edge without arguments
/// (`branchReachesElseWithoutArguments`), one dominating the other, and the
/// inner (dominated) branch's then edge targets `join`.  R is the blocks reached
/// from `entry` without entering `join`, each dominated by `entry` (reflexive,
/// so `entry` qualifies), each ending in a `jump` or `branch`, every edge
/// leaving R targeting `join` without arguments.  R is ordered by a Kahn pass
/// over its internal edges (a dominator before every block it dominates, `entry`
/// first); a region that does not fully order holds a cycle and is refused.
/// Returns the ordered closure R and the inner branch's else edge to `entry`.
/// The one-block shape is the case R = {entry}.
const CompoundOrArm = struct {
    closure: []ir.BlockId,
    clone_edge: ir.CfgEdgeRef,
};

fn compoundShortCircuitOrArmAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    join: ir.BlockId,
    entry: ir.BlockId,
) std.mem.Allocator.Error!?CompoundOrArm {
    if (entry.index() >= program.blocks.len) return null;
    if (analysis.predecessorCount(entry) != 2) return null;
    const first_predecessor = analysis.predecessorAt(entry, 0) orelse return null;
    const second_predecessor = analysis.predecessorAt(entry, 1) orelse return null;
    if (!branchReachesElseWithoutArguments(program, first_predecessor, entry)) return null;
    if (!branchReachesElseWithoutArguments(program, second_predecessor, entry)) return null;
    const inner = if (analysis.dominates(first_predecessor, second_predecessor))
        second_predecessor
    else if (analysis.dominates(second_predecessor, first_predecessor))
        first_predecessor
    else
        return null;
    switch (program.blocks[inner.index()].terminator) {
        .branch => |branch| if (branch.then_edge.target != join) return null,
        else => return null,
    }

    var region: std.ArrayList(ir.BlockId) = .empty;
    defer region.deinit(allocator);
    const in_region = try allocator.alloc(bool, program.blocks.len);
    defer allocator.free(in_region);
    @memset(in_region, false);
    try region.append(allocator, entry);
    in_region[entry.index()] = true;
    var cursor: usize = 0;
    while (cursor < region.items.len) : (cursor += 1) {
        const block_id = region.items[cursor];
        const outgoing = compoundOrArmOutgoingEdges(program.blocks[block_id.index()].terminator) orelse return null;
        for (outgoing.slice()) |edge| {
            if (edge.target == join) {
                if (edge.arguments.len != 0) return null;
                continue;
            }
            if (edge.target.index() >= program.blocks.len) return null;
            if (!analysis.dominates(entry, edge.target)) return null;
            if (!in_region[edge.target.index()]) {
                in_region[edge.target.index()] = true;
                try region.append(allocator, edge.target);
            }
        }
    }

    const indegree = try allocator.alloc(usize, program.blocks.len);
    defer allocator.free(indegree);
    @memset(indegree, 0);
    for (region.items) |block_id| {
        const outgoing = compoundOrArmOutgoingEdges(program.blocks[block_id.index()].terminator).?;
        for (outgoing.slice()) |edge| {
            if (edge.target == join) continue;
            indegree[edge.target.index()] += 1;
        }
    }
    var ordered: std.ArrayList(ir.BlockId) = .empty;
    defer ordered.deinit(allocator);
    for (region.items) |block_id| {
        if (indegree[block_id.index()] == 0) try ordered.append(allocator, block_id);
    }
    var head: usize = 0;
    while (head < ordered.items.len) : (head += 1) {
        const block_id = ordered.items[head];
        const outgoing = compoundOrArmOutgoingEdges(program.blocks[block_id.index()].terminator).?;
        for (outgoing.slice()) |edge| {
            if (edge.target == join) continue;
            indegree[edge.target.index()] -= 1;
            if (indegree[edge.target.index()] == 0) try ordered.append(allocator, edge.target);
        }
    }
    if (ordered.items.len != region.items.len) return null;

    return .{
        .closure = try ordered.toOwnedSlice(allocator),
        .clone_edge = .{ .source = inner, .kind = .branch_else, .target = entry },
    };
}

/// A `branch` whose else edge targets `block` with no arguments and
/// whose then edge leaves it.
fn branchReachesElseWithoutArguments(
    program: *const ir.Program,
    predecessor: ir.BlockId,
    block: ir.BlockId,
) bool {
    if (predecessor.index() >= program.blocks.len) return false;
    switch (program.blocks[predecessor.index()].terminator) {
        .branch => |branch| return branch.else_edge.target == block and
            branch.else_edge.arguments.len == 0 and
            branch.then_edge.target != block,
        else => return false,
    }
}

/// The one-block split of a disassembly short-circuit `or` block,
/// constructed directly for the inner branch's else edge `clone_edge`: the
/// closure is exactly the `or` block and the incoming edge is that else edge.
/// The candidate passes the preparation every structural split passes
/// (`structural_overlap.prepareClosureWithReplayContext`, the admission of the
/// authenticated one-block boundary projection); applyPlan then clones the
/// block, keeps the clone's jump to the collided block, redirects the else
/// edge to the clone and records the authenticated node_split.  The collision
/// split finder is not used: its continuation extension pulls the collided
/// tail back into the closure.  Null when the preparation refuses the block.
fn shortCircuitElseSplitAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    function_index: usize,
    clone_edge: ir.CfgEdgeRef,
    replay_context: *structural_overlap.ReplayProjectionContext,
) std.mem.Allocator.Error!?structural_overlap.Split {
    const closure = try allocator.alloc(ir.BlockId, 1);
    errdefer allocator.free(closure);
    closure[0] = clone_edge.target;
    const incoming = [_]ir.CfgEdgeRef{clone_edge};
    if (!structural_overlap.prepareClosureWithReplayContext(
        allocator,
        program,
        analysis,
        closure,
        &incoming,
        replay_context,
    )) {
        allocator.free(closure);
        return null;
    }
    const owned_incoming = try allocator.dupe(ir.CfgEdgeRef, &incoming);
    return .{
        .allocator = allocator,
        .function_index = function_index,
        .branch = clone_edge.source,
        .entry = clone_edge.target,
        .join = clone_edge.target,
        .incoming = owned_incoming,
        .closure = closure,
    };
}

/// The split of a compound short-circuit `or`
/// arm, generalizing `shortCircuitElseSplitAlloc` from the one-block case.  The
/// closure is the ordered arm R, the incoming edge is the inner branch's else
/// edge, the branch is the inner branch, and the entry and join are the arm
/// entry (as the one-block split sets join = entry).  Admitted by
/// `structural_overlap.prepareClosureWithReplayContext` unseeded, exactly as
/// the one-block split.  Null (freeing the closure) when the preparation refuses the region, so
/// the feedback phase keeps its continuation-cloning path.
fn compoundShortCircuitSplitAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    function_index: usize,
    arm: CompoundOrArm,
    replay_context: *structural_overlap.ReplayProjectionContext,
) std.mem.Allocator.Error!?structural_overlap.Split {
    const closure = arm.closure;
    errdefer allocator.free(closure);
    const incoming = [_]ir.CfgEdgeRef{arm.clone_edge};
    if (!structural_overlap.prepareClosureWithReplayContext(
        allocator,
        program,
        analysis,
        closure,
        &incoming,
        replay_context,
    )) {
        allocator.free(closure);
        return null;
    }
    const owned_incoming = try allocator.dupe(ir.CfgEdgeRef, &incoming);
    return .{
        .allocator = allocator,
        .function_index = function_index,
        .branch = arm.clone_edge.source,
        .entry = arm.clone_edge.target,
        .join = arm.clone_edge.target,
        .incoming = owned_incoming,
        .closure = closure,
    };
}

fn normalizeImpl(
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    source: *const ir.Program,
    include_structure_feedback: bool,
    only_function: ?usize,
    options: NormalizeOptions,
) NormalizeError!Result {
    var blocks: std.ArrayList(ir.Block) = .empty;
    try blocks.appendSlice(allocator, source.blocks);
    var functions: std.ArrayList(ir.Function) = .empty;
    try functions.appendSlice(allocator, source.functions);
    var values: std.ArrayList(ir.Value) = .empty;
    try values.appendSlice(allocator, source.values);
    var packs: std.ArrayList(ir.ValuePack) = .empty;
    try packs.appendSlice(allocator, source.value_packs);
    var instructions: std.ArrayList(ir.Instruction) = .empty;
    try instructions.appendSlice(allocator, source.instructions);
    var rewrites: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    try rewrites.appendSlice(allocator, source.edge_rewrites);

    var result: Result = .{ .program = source.* };
    result.program.blocks = blocks.items;
    result.program.functions = functions.items;
    result.program.values = values.items;
    result.program.value_packs = packs.items;
    result.program.instructions = instructions.items;
    result.program.edge_rewrites = rewrites.items;
    if (!blockParametersAreCanonical(source)) return result;

    const iteration_limit = normalizationIterationLimit(source, only_function);
    const structural_clone_limit = std.math.mul(
        usize,
        iteration_limit,
        max_structural_clone_expansion,
    ) catch return error.NormalizationInvariantFailed;
    var iteration: usize = 0;
    var split_identities: std.ArrayList(OverlapIdentity) = .empty;
    defer split_identities.deinit(scratch_allocator);
    var structural_cloned_blocks: usize = 0;

    if (!options.skip_initial_phases) {
        // Phase 0, the transparent forwarding collapse, runs only for a targeted invocation
        // (`only_function != null`). Whole-program and control normalization leave
        // rewrite-free inputs history-free here and collapse forwarders only after a
        // feedback split (the feedback-collision `collapseTransparentForwardingBlocks`
        // call). The rationale for this targeted-only gate is unconfirmed: nothing in
        // the tree states it.
        if (only_function != null) {
            _ = try collapseTransparentForwardingBlocks(allocator, &result.program, &blocks, &rewrites, only_function);
        }

        while (iteration < iteration_limit) : (iteration += 1) {
            result.program.blocks = blocks.items;
            result.program.functions = functions.items;
            result.program.values = values.items;
            result.program.value_packs = packs.items;
            result.program.instructions = instructions.items;
            result.program.edge_rewrites = rewrites.items;
            var scan = try scanProgram(scratch_allocator, &result.program, only_function);
            defer scan.deinit();
            const plan = if (scan.plan) |*value| value else break;
            const before = scan.entry_measure;
            const prior_split = result;
            try applyPlan(allocator, &result.program, &blocks, &functions, &instructions, &values, &packs, &rewrites, plan, &result);
            traceAppliedSplit("irreducible", plan.function_index, prior_split, result);
            result.program.blocks = blocks.items;
            result.program.functions = functions.items;
            result.program.values = values.items;
            result.program.value_packs = packs.items;
            result.program.instructions = instructions.items;
            result.program.edge_rewrites = rewrites.items;
            const after = try irreducibleEntryMeasure(scratch_allocator, &result.program, only_function);
            if (after >= before) {
                std.debug.print("normalize failure phase=irreducible-progress iteration={} before={} after={} blocks={} rewrites={}\n", .{ iteration, before, after, blocks.items.len, rewrites.items.len });
                return error.NormalizationInvariantFailed;
            }
        } else {
            std.debug.print("normalize failure phase=irreducible-iteration-limit iterations={} blocks={} rewrites={}\n", .{ iteration, blocks.items.len, rewrites.items.len });
            return error.NormalizationInvariantFailed;
        }

        iteration = 0;
        while (iteration < iteration_limit) : (iteration += 1) {
            result.program.blocks = blocks.items;
            result.program.functions = functions.items;
            result.program.values = values.items;
            result.program.value_packs = packs.items;
            result.program.instructions = instructions.items;
            result.program.edge_rewrites = rewrites.items;
            var overlap = (try structural_overlap.findSplitAllocForFunction(
                scratch_allocator,
                &result.program,
                only_function,
            )) orelse break;
            defer overlap.deinit();
            for (split_identities.items) |identity| {
                if (identity.branch == overlap.branch and
                    identity.entry == overlap.entry and
                    identity.join == overlap.join and
                    identity.entry_measure_kind == overlap.entry_measure_kind)
                {
                    std.debug.print("normalize failure phase=overlap-repeat iteration={} branch={} entry={} join={} kind={s} blocks={} structural_clones={} rewrites={}\n", .{
                        iteration,
                        overlap.branch.index(),
                        overlap.entry.index(),
                        overlap.join.index(),
                        @tagName(overlap.entry_measure_kind),
                        blocks.items.len,
                        structural_cloned_blocks,
                        rewrites.items.len,
                    });
                    return error.NormalizationInvariantFailed;
                }
            }
            try split_identities.append(scratch_allocator, .{
                .branch = overlap.branch,
                .entry = overlap.entry,
                .join = overlap.join,
                .entry_measure_kind = overlap.entry_measure_kind,
            });
            const batch_count = if (overlap.entry_measure_kind == .conditional)
                overlap.incoming.len
            else
                1;
            const batch_cloned_blocks = std.math.mul(usize, overlap.closure.len, batch_count) catch
                return error.NormalizationInvariantFailed;
            structural_cloned_blocks = std.math.add(usize, structural_cloned_blocks, batch_cloned_blocks) catch
                return error.NormalizationInvariantFailed;
            if (structural_cloned_blocks > structural_clone_limit) {
                std.debug.print("normalize failure phase=overlap-clone-limit iteration={} blocks={} structural_clones={} limit={} rewrites={}\n", .{ iteration, blocks.items.len, structural_cloned_blocks, structural_clone_limit, rewrites.items.len });
                return error.NormalizationInvariantFailed;
            }

            const secondaries = try scratch_allocator.alloc(Secondary, batch_count);
            var initialized_secondaries: usize = 0;
            var plan_owned = false;
            errdefer if (!plan_owned) {
                for (secondaries[0..initialized_secondaries]) |secondary| {
                    scratch_allocator.free(secondary.incoming);
                    scratch_allocator.free(secondary.closure);
                }
                scratch_allocator.free(secondaries);
            };
            if (batch_count == 1 and overlap.entry_measure_kind != .conditional) {
                const incoming = try scratch_allocator.dupe(ir.CfgEdgeRef, overlap.incoming);
                errdefer scratch_allocator.free(incoming);
                const closure = try scratch_allocator.dupe(ir.BlockId, overlap.closure);
                errdefer scratch_allocator.free(closure);
                secondaries[0] = .{ .block = overlap.entry, .incoming = incoming, .closure = closure };
                initialized_secondaries = 1;
            } else {
                for (overlap.incoming) |reference| {
                    const incoming = try scratch_allocator.dupe(ir.CfgEdgeRef, &.{reference});
                    const closure = try scratch_allocator.dupe(ir.BlockId, overlap.closure);
                    secondaries[initialized_secondaries] = .{ .block = overlap.entry, .incoming = incoming, .closure = closure };
                    initialized_secondaries += 1;
                }
            }
            var plan: SplitPlan = .{
                .allocator = scratch_allocator,
                .function_index = overlap.function_index,
                .secondaries = secondaries,
                .secondary_count = batch_count,
            };
            plan_owned = true;
            defer plan.deinit();
            const prior_split = result;
            try applyPlan(allocator, &result.program, &blocks, &functions, &instructions, &values, &packs, &rewrites, &plan, &result);
            traceAppliedSplit("overlap", plan.function_index, prior_split, result);
            // The scalar entry count is not monotonic: splitting one authenticated
            // edge can expose another edge while preserving the count. Exact
            // overlap identity replay protection and the structural clone budget
            // provide the bounded termination proof for this phase.
        } else {
            std.debug.print("normalize failure phase=overlap-iteration-limit iterations={} blocks={} structural_clones={} rewrites={}\n", .{ iteration, blocks.items.len, structural_cloned_blocks, rewrites.items.len });
            return error.NormalizationInvariantFailed;
        }
    }

    if (include_structure_feedback) feedback: {
        var collision_arms: std.ArrayList(CollisionArm) = .empty;
        defer collision_arms.deinit(scratch_allocator);
        var collision_seed: ?CollisionSeed = if (options.initial_resume_seed) |seed|
            collisionSeedFromResumeSeed(seed)
        else
            null;
        var feedback_arena = std.heap.ArenaAllocator.init(scratch_allocator);
        defer feedback_arena.deinit();
        const feedback_allocator = feedback_arena.allocator();
        iteration = 0;
        const feedback_iteration_limit = options.feedback_iteration_limit orelse iteration_limit;
        while (iteration < feedback_iteration_limit) : (iteration += 1) {
            // A failed structure probe owns substantial temporary CFG and
            // replay state. Reclaim it at the iteration boundary instead of
            // retaining every failed plan until the whole function exits.
            _ = feedback_arena.reset(.retain_capacity);

            result.program.blocks = blocks.items;
            result.program.functions = functions.items;
            result.program.values = values.items;
            result.program.value_packs = packs.items;
            result.program.instructions = instructions.items;
            result.program.edge_rewrites = rewrites.items;

            var selected: ?structural_overlap.Split = null;
            var selected_context: ?structure.CollisionContext = null;
            var unvisited_plan: ?SplitPlan = null;
            var found_collision = false;
            var seeded_fallback = false;

            // A targeted feedback iteration does not mutate the program
            // until after the selected split is authenticated. Reuse the
            // immutable replay index across a full scan and its collision
            // fallback instead of rebuilding it for the same pre-apply graph.
            // A resumed seed builds its own index below; delaying this shared
            // index until a scan is needed avoids retaining two copies of the
            // same targeted projection on the seed fast path.
            var shared_feedback_replay: ?structural_overlap.ReplayProjectionContext = null;
            if (collision_seed == null) {
                if (only_function) |selected_function| {
                    if (selected_function < result.program.functions.len) {
                        shared_feedback_replay = try structural_overlap.ReplayProjectionContext.initForFunction(
                            feedback_allocator,
                            &result.program,
                            result.program.functions[selected_function].id,
                        );
                    }
                }
            }
            defer if (shared_feedback_replay) |*context| context.deinit();

            // A prior full structuring pass already authenticated this target
            // as an owned-context collision.  Try another incoming arm
            // directly before rebuilding the entire function plan.  The
            // overlap proof remains authoritative; failure falls through to
            // the complete collision-aware structurer.
            if (collision_seed) |*seed| {
                if (seed.function_index < result.program.functions.len) {
                    var seed_graph = cfg.Analysis.init(
                        feedback_allocator,
                        &result.program,
                        result.program.functions[seed.function_index],
                    ) catch |err| switch (err) {
                        error.InvalidCfg => null,
                        error.OutOfMemory => return error.OutOfMemory,
                    };
                    if (seed_graph) |*graph| {
                        defer graph.deinit();
                        var seed_replay = try structural_overlap.ReplayProjectionContext.initForFunction(
                            feedback_allocator,
                            &result.program,
                            result.program.functions[seed.function_index].id,
                        );
                        defer seed_replay.deinit();
                        const rebased = try rebaseUnreachableNodeSplitSeedOwner(
                            &result.program,
                            graph,
                            seed,
                            &seed_replay,
                        );
                        if (rebased) traceNormalize("normalize_phase collision_seed_rebased iteration={} target={} previous={}\n", .{
                            iteration,
                            seed.target.index(),
                            seed.previous.?.index(),
                        });
                        // The overlap splitter can construct a valid clone
                        // for an ordinary loop even when the structurer no
                        // longer reports a collision.  A seed is only a
                        // scheduling hint from the previous pass, not proof
                        // that the newly cloned target still needs a split.
                        // Revalidate the collision before using the fast path
                        // or this loop can grow one clone per iteration.
                        const seed_status = try seededCollisionStatus(
                            &result.program,
                            graph,
                            seed.*,
                            &seed_replay,
                        );
                        traceNormalize("normalize_phase collision_seed_attempt iteration={} function={} proof={s} source={?} target={} previous={?} status={s}\n", .{
                            iteration,
                            seed.function_index,
                            @tagName(seed.proof),
                            seed.source,
                            seed.target.index(),
                            seed.previous,
                            @tagName(seed_status),
                        });
                        const seed_is_collision = seed_status == .live;
                        if (seed_is_collision) {
                            try reserveCloneFoldResumeArm(
                                scratch_allocator,
                                &collision_arms,
                                seed.*,
                            );
                        }
                        // A contextual split may clone both the collision
                        // target and the prior owner.  Folding that target
                        // back immediately would erase the ownership boundary
                        // and rediscover the same collision on the next scan.
                        // The direct fold is safe only when the seed still
                        // names the exact historical owner; otherwise the
                        // authenticated clone is the live continuation.
                        const direct_fold_has_historical_owner =
                            seed.previous != null and seed.original_target != null and
                            seed.previous.? == seed.original_target.?;
                        if (seed_is_collision and seed.proof == .node_split and direct_fold_has_historical_owner) {
                            const owner = CollisionArm{
                                .source = seed.source.?,
                                .kind = seed.kind.?,
                                .target = seed.original_target.?,
                                .context = seed.context,
                            };
                            const candidate = CollisionArm{
                                .source = seed.source.?,
                                .kind = seed.kind.?,
                                .target = seed.target,
                                .context = seed.context,
                            };
                            if (try collapseAuthenticatedDirectTargetCollisionEdge(
                                allocator,
                                &result.program,
                                &blocks,
                                &rewrites,
                                graph,
                                owner,
                                candidate,
                                &seed_replay,
                            )) {
                                traceNormalize("normalize_phase collision_seed_direct_target_fold iteration={} source={} from={} to={}\n", .{
                                    iteration,
                                    candidate.source.index(),
                                    candidate.target.index(),
                                    owner.target.index(),
                                });
                                collision_seed = null;
                                continue;
                            }
                        }
                        const seeded = if (seed_is_collision)
                            try findPredecessorCollisionSplitAllocWithAnalysisAndReplayContext(
                                feedback_allocator,
                                &result.program,
                                graph,
                                seed.function_index,
                                seed.target,
                                seed.source,
                                collision_arms.items,
                                false,
                                seed.context,
                                &seed_replay,
                            )
                        else
                            null;
                        const split = seeded orelse if (seed_is_collision and seed.source != null)
                            try findPredecessorCollisionSplitAllocWithAnalysisAndReplayContext(
                                feedback_allocator,
                                &result.program,
                                graph,
                                seed.function_index,
                                seed.target,
                                null,
                                collision_arms.items,
                                false,
                                seed.context,
                                &seed_replay,
                            )
                        else
                            null;
                        if (split) |value| {
                            selected = value;
                            if (seeded != null) {
                                selected_context = seed.context;
                            } else {
                                // A predecessor fallback is only a fresh
                                // structural candidate. It did not inherit a
                                // live structurer visit context, so do not
                                // publish a resume seed that would replay the
                                // same fallback edge on the next process.
                                selected_context = null;
                                collision_seed = null;
                                seeded_fallback = true;
                                traceNormalize("normalize_phase collision_seed_fallback iteration={} function={} entry={} branch={}\n", .{
                                    iteration,
                                    seed.function_index,
                                    value.entry.index(),
                                    value.branch.index(),
                                });
                            }
                            found_collision = true;
                            traceNormalize("normalize_phase collision_seed_selected iteration={} entry={} branch={} join={} closure={} incoming={}\n", .{
                                iteration,
                                value.entry.index(),
                                value.branch.index(),
                                value.join.index(),
                                value.closure.len,
                                value.incoming.len,
                            });
                        } else {
                            traceNormalize("normalize_phase collision_seed_no_split iteration={} status={s}\n", .{
                                iteration,
                                @tagName(seed_status),
                            });
                            collision_seed = null;
                        }
                    } else {
                        collision_seed = null;
                    }
                } else {
                    collision_seed = null;
                }
            }
            const feedback_scan_start = normalizePhaseNow();
            if (selected == null) {
                for (result.program.functions, 0..) |function, function_index| {
                    if (only_function) |selected_function| if (function_index != selected_function) continue;
                    const graph_start = normalizePhaseNow();
                    var graph = cfg.Analysis.init(feedback_allocator, &result.program, function) catch |err| switch (err) {
                        error.InvalidCfg => continue,
                        error.OutOfMemory => return error.OutOfMemory,
                    };
                    defer graph.deinit();
                    const graph_ms = normalizePhaseMillis(graph_start);
                    const replay_start = normalizePhaseNow();
                    var replay_context_owned: ?structural_overlap.ReplayProjectionContext = null;
                    const replay_context: *structural_overlap.ReplayProjectionContext = if (shared_feedback_replay) |*context|
                        context
                    else blk: {
                        replay_context_owned = try structural_overlap.ReplayProjectionContext.initForFunction(
                            feedback_allocator,
                            &result.program,
                            function.id,
                        );
                        break :blk &replay_context_owned.?;
                    };
                    defer if (replay_context_owned) |*context| context.deinit();
                    const replay_ms = normalizePhaseMillis(replay_start);
                    var collision: ?structure.Collision = null;
                    defer {
                        if (collision) |*value| value.deinit(scratch_allocator);
                    }
                    const collision_start = normalizePhaseNow();
                    // A structure probe owns many speculative regions.  Keep
                    // those allocations on the reclaiming scratch allocator:
                    // failed recursive probes must release their regions
                    // before the next candidate, rather than retaining every
                    // abandoned allocation in the feedback arena.
                    const collision_plan = structure.Plan.initWithCollisionAndReplayContext(
                        scratch_allocator,
                        &graph,
                        &collision,
                        replay_context,
                    );
                    const collision_ms = normalizePhaseMillis(collision_start);
                    traceNormalize("normalize_phase feedback_parts iteration={} function={} graph_ms={} replay_ms={} collision_ms={} blocks={} rewrites={}\\n", .{
                        iteration,
                        function_index,
                        graph_ms,
                        replay_ms,
                        collision_ms,
                        blocks.items.len,
                        rewrites.items.len,
                    });
                    if (collision_plan) |plan_value| {
                        var plan = plan_value;
                        plan.deinit();
                    } else |err| switch (err) {
                        error.OutOfMemory => return error.OutOfMemory,
                        error.UnsupportedShape => {
                            const obstruction = if (collision) |*value| value else continue;
                            traceNormalize("feedback_collision_candidate iteration={} function={} block={} previous={any} reason={s} incoming={any} incoming_group={} frontiers={}\n", .{
                                iteration,
                                function_index,
                                obstruction.block.index(),
                                obstruction.previous,
                                @tagName(obstruction.reason),
                                obstruction.incoming,
                                obstruction.incoming_group.len,
                                obstruction.unvisited_frontiers.len,
                            });
                            if (obstruction.block.index() < result.program.blocks.len) {
                                const candidate_block = result.program.blocks[obstruction.block.index()];
                                traceNormalize("feedback_collision_shape block={} parameters={} instructions={} terminator={s}\n", .{
                                    candidate_block.id.index(),
                                    candidate_block.parameters.len,
                                    candidate_block.instructions.len,
                                    @tagName(std.meta.activeTag(candidate_block.terminator)),
                                });
                                // Keep the forwarding decision grounded in the live edge.
                                // Context stops are provenance, not a substitute for the
                                // candidate's actual outgoing target and tuple.
                                if (candidate_block.parameters.len == 0 and
                                    candidate_block.instructions.len == 0)
                                {
                                    switch (candidate_block.terminator) {
                                        .jump => |outgoing| {
                                            const successor = if (outgoing.target.index() < result.program.blocks.len)
                                                result.program.blocks[outgoing.target.index()]
                                            else
                                                null;
                                            traceNormalize("feedback_empty_candidate block={} outgoing_target={} outgoing_args={any} successor_parameters={} successor_canonical={}\n", .{
                                                candidate_block.id.index(),
                                                outgoing.target.index(),
                                                outgoing.arguments,
                                                if (successor) |block| block.parameters.len else 0,
                                                if (successor) |block| node_split.parametersAreCanonical(result.program.values, block) else false,
                                            });
                                        },
                                        else => {},
                                    }
                                }
                            }
                            if (obstruction.previous) |previous| {
                                if (previous.index() < result.program.blocks.len) {
                                    const previous_block = result.program.blocks[previous.index()];
                                    traceNormalize("feedback_collision_previous_shape block={} parameters={} instructions={} terminator={s}\n", .{
                                        previous_block.id.index(),
                                        previous_block.parameters.len,
                                        previous_block.instructions.len,
                                        @tagName(std.meta.activeTag(previous_block.terminator)),
                                    });
                                }
                            }
                            if (!collisionCanSplit(obstruction.reason)) continue;
                            found_collision = true;
                            if (obstruction.owner_context) |owner| {
                                traceNormalize("feedback_collision_owner_context start={} stop={?} loop_exit={?} continue_target={?} parameter_arguments={any}\n", .{
                                    owner.start.index(),
                                    if (owner.stop) |block| block.index() else null,
                                    if (owner.loop_exit) |block| block.index() else null,
                                    if (owner.continue_target) |block| block.index() else null,
                                    owner.parameter_arguments,
                                });
                            }
                            if (obstruction.incoming_context) |incoming_context| {
                                traceNormalize("feedback_collision_incoming_context start={} stop={?} loop_exit={?} continue_target={?} parameter_arguments={any}\n", .{
                                    incoming_context.start.index(),
                                    if (incoming_context.stop) |block| block.index() else null,
                                    if (incoming_context.loop_exit) |block| block.index() else null,
                                    if (incoming_context.continue_target) |block| block.index() else null,
                                    incoming_context.parameter_arguments,
                                });
                            }
                            if (obstruction.reason == .unvisited_reachable and obstruction.unvisited_frontiers.len != 0) {
                                unvisited_plan = try planUnvisitedFrontiersAllocWithAnalysis(
                                    feedback_allocator,
                                    &result.program,
                                    function_index,
                                    &graph,
                                    replay_context,
                                    obstruction.unvisited_frontiers,
                                    collision_arms.items,
                                );
                                if (unvisited_plan != null) break;
                            }
                            var single: [1]ir.CfgEdgeRef = undefined;
                            const incoming = if (collisionGroupContainsPreviousOwner(obstruction)) incoming: {
                                single[0] = obstruction.incoming.?;
                                break :incoming single[0..];
                            } else if (obstruction.incoming_group.len != 0)
                                obstruction.incoming_group
                            else if (obstruction.incoming) |reference| incoming: {
                                single[0] = reference;
                                break :incoming single[0..];
                            } else incoming: {
                                selected = try findPredecessorCollisionSplitAllocWithAnalysisAndReplayContext(
                                    feedback_allocator,
                                    &result.program,
                                    &graph,
                                    function_index,
                                    obstruction.block,
                                    null,
                                    collision_arms.items,
                                    true,
                                    obstruction.incoming_context,
                                    replay_context,
                                );
                                break :incoming &.{};
                            };
                            if (incoming.len != 0) {
                                // An already-owned continuation can carry a value
                                // whose identity is authenticated only on this
                                // incoming context. Split that edge first so the
                                // generic collision splitter does not clone the
                                // entire shared continuation and manufacture new
                                // sibling collisions.
                                if (obstruction.reason == .already_owned) {
                                    // A disassembly short-circuit `or`
                                    // block taken as the outer branch's join leaves
                                    // its tail an already-owned collision whose
                                    // pack-returning terminator the node splitter
                                    // cannot clone.  Clone the pure `or` block for
                                    // the inner branch's else edge instead (a
                                    // one-block split constructed directly), so the
                                    // outer branch's arms converge at the collided
                                    // block and no tail is cloned.  The structurer
                                    // gave no visit context for that edge, so the
                                    // split stays unseeded, as the predecessor
                                    // fallback below.
                                    if (obstruction.previous) |previous_block| {
                                        if (shortCircuitElseCloneEdge(&result.program, &graph, previous_block, obstruction.block)) |clone_edge| {
                                            if (try shortCircuitElseSplitAlloc(
                                                feedback_allocator,
                                                &result.program,
                                                &graph,
                                                function_index,
                                                clone_edge,
                                                replay_context,
                                            )) |candidate| {
                                                traceNormalize("feedback_short_circuit_split function={} or_block={} inner={} closure={}\n", .{
                                                    function_index,
                                                    previous_block.index(),
                                                    clone_edge.source.index(),
                                                    candidate.closure.len,
                                                });
                                                selected = candidate;
                                                selected_context = null;
                                                collision_seed = null;
                                                seeded_fallback = true;
                                            }
                                        }
                                    }
                                    if (selected == null) {
                                        if (obstruction.owner_context) |owner| {
                                            if (owner.stop) |arm_entry| {
                                                if (try compoundShortCircuitOrArmAlloc(
                                                    feedback_allocator,
                                                    &result.program,
                                                    &graph,
                                                    obstruction.block,
                                                    arm_entry,
                                                )) |arm| {
                                                    if (try compoundShortCircuitSplitAlloc(
                                                        feedback_allocator,
                                                        &result.program,
                                                        &graph,
                                                        function_index,
                                                        arm,
                                                        replay_context,
                                                    )) |candidate| {
                                                        traceNormalize("feedback_compound_or_arm_split function={} entry={} inner={} closure={}\n", .{
                                                            function_index,
                                                            arm_entry.index(),
                                                            candidate.branch.index(),
                                                            candidate.closure.len,
                                                        });
                                                        selected = candidate;
                                                        selected_context = null;
                                                        collision_seed = null;
                                                        seeded_fallback = true;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    const contextual = if (selected == null) try structural_overlap.findContextualValueSplitForIncomingAllocWithReplayContext(
                                        feedback_allocator,
                                        &result.program,
                                        &graph,
                                        function_index,
                                        obstruction.block,
                                        incoming,
                                        if (obstruction.owner_context) |owner|
                                            owner.parameter_arguments
                                        else
                                            null,
                                        replay_context,
                                    ) else null;
                                    if (contextual) |candidate| {
                                        traceNormalize("feedback_contextual_split function={} entry={} branch={} closure={} incoming={}\n", .{
                                            candidate.function_index,
                                            candidate.entry.index(),
                                            candidate.branch.index(),
                                            candidate.closure.len,
                                            candidate.incoming.len,
                                        });
                                        selected = candidate;
                                    }
                                }
                                if (selected == null) {
                                    selected = try structural_overlap.findCollisionSplitAllocWithAnalysisAndReplayContext(
                                        feedback_allocator,
                                        &result.program,
                                        &graph,
                                        function_index,
                                        obstruction.block,
                                        incoming,
                                        replay_context,
                                    );
                                }
                                if (selected == null) {
                                    // An internal backedge may identify the
                                    // collision while its SCC cannot be
                                    // cloned from that edge.  Try a fresh
                                    // predecessor-owned entry instead; the
                                    // splitter still authenticates the whole
                                    // closure and the fallback remains
                                    // unseeded for the next scan.
                                    if (try findPredecessorCollisionSplitAllocWithAnalysisAndReplayContext(
                                        feedback_allocator,
                                        &result.program,
                                        &graph,
                                        function_index,
                                        obstruction.block,
                                        null,
                                        collision_arms.items,
                                        true,
                                        obstruction.incoming_context,
                                        replay_context,
                                    )) |candidate| {
                                        selected = candidate;
                                        selected_context = null;
                                        collision_seed = null;
                                        seeded_fallback = true;
                                        traceNormalize("normalize_phase feedback_predecessor_fallback iteration={} function={} entry={} branch={} closure={}\n", .{
                                            iteration,
                                            function_index,
                                            candidate.entry.index(),
                                            candidate.branch.index(),
                                            candidate.closure.len,
                                        });
                                    }
                                }
                            }
                            if (selected != null) {
                                const seed_reference: ?ir.CfgEdgeRef = if (selected) |candidate|
                                    if (candidate.incoming.len != 0) candidate.incoming[0] else null
                                else
                                    null;
                                if (!seeded_fallback) {
                                    collision_seed = .{
                                        .function_index = function_index,
                                        .target = obstruction.block,
                                        .source = if (seed_reference) |reference| reference.source else null,
                                        .kind = if (seed_reference) |reference| reference.kind else null,
                                        .original_target = if (seed_reference) |reference| reference.target else null,
                                        .previous = obstruction.previous,
                                        .context = obstruction.incoming_context,
                                    };
                                    selected_context = obstruction.incoming_context;
                                }
                                break;
                            }
                        },
                    }
                }
            }
            traceNormalize("normalize_phase feedback_scan iteration={} selected={} unvisited={} found_collision={} ms={} blocks={} rewrites={}\\n", .{
                iteration,
                selected != null,
                unvisited_plan != null,
                found_collision,
                normalizePhaseMillis(feedback_scan_start),
                blocks.items.len,
                rewrites.items.len,
            });
            if (unvisited_plan) |*plan| {
                defer plan.deinit();
                collision_seed = null;
                var clone_count: usize = 0;
                for (plan.secondaries[0..plan.secondary_count]) |secondary| {
                    clone_count = std.math.add(usize, clone_count, secondary.closure.len) catch
                        return error.NormalizationInvariantFailed;
                    for (secondary.incoming, 0..) |reference, incoming_index| {
                        try collision_arms.append(scratch_allocator, .{
                            .source = reference.source,
                            .kind = reference.kind,
                            .target = reference.target,
                            .context = if (incoming_index < secondary.incoming_contexts.len)
                                secondary.incoming_contexts[incoming_index]
                            else
                                null,
                        });
                    }
                }
                structural_cloned_blocks = std.math.add(usize, structural_cloned_blocks, clone_count) catch
                    return error.NormalizationInvariantFailed;
                if (structural_cloned_blocks > structural_clone_limit) {
                    traceUnvisitedPlanCloneLimit(&result.program, plan, structural_cloned_blocks, structural_clone_limit, rewrites.items.len, collision_arms.items.len);
                    std.debug.print("normalize failure phase=feedback-batch-clone-limit iteration={} blocks={} structural_clones={} limit={} rewrites={} arms={}\n", .{ iteration, blocks.items.len, structural_cloned_blocks, structural_clone_limit, rewrites.items.len, collision_arms.items.len });
                    return error.NormalizationInvariantFailed;
                }
                const apply_start = normalizePhaseNow();
                const prior_split = result;
                try applyPlan(allocator, &result.program, &blocks, &functions, &instructions, &values, &packs, &rewrites, plan, &result);
                traceAppliedSplit("feedback-unvisited", plan.function_index, prior_split, result);
                traceNormalize("normalize_phase feedback_apply iteration={} mode=unvisited ms={} blocks={} rewrites={}\\n", .{
                    iteration,
                    normalizePhaseMillis(apply_start),
                    blocks.items.len,
                    rewrites.items.len,
                });
                continue;
            }
            var overlap = if (selected) |value| value else {
                if (found_collision) {
                    std.debug.print("normalize failure phase=feedback-unsplittable-collision iteration={} blocks={} structural_clones={} rewrites={} arms={}\n", .{ iteration, blocks.items.len, structural_cloned_blocks, rewrites.items.len, collision_arms.items.len });
                    return error.NormalizationInvariantFailed;
                }
                break;
            };
            defer overlap.deinit();
            traceNormalize("feedback_selected function={} entry={} branch={} join={} closure={any} incoming={any}\n", .{
                overlap.function_index,
                overlap.entry.index(),
                overlap.branch.index(),
                overlap.join.index(),
                overlap.closure,
                overlap.incoming,
            });
            if (cfg_edge.value(&result.program, overlap.incoming[0])) |edge| {
                traceNormalize("feedback_selected_edge_args={any}\n", .{edge.arguments});
            }
            selected_context = collisionContextWithCurrentEdgeArguments(
                &result.program,
                selected_context,
                overlap.incoming[0],
            );
            var collision_projection_context_owned: ?structural_overlap.ReplayProjectionContext = null;
            const collision_projection_context: *structural_overlap.ReplayProjectionContext = if (shared_feedback_replay) |*context|
                context
            else blk: {
                collision_projection_context_owned = try structural_overlap.ReplayProjectionContext.initForFunction(
                    feedback_allocator,
                    &result.program,
                    result.program.functions[overlap.function_index].id,
                );
                break :blk &collision_projection_context_owned.?;
            };
            defer if (collision_projection_context_owned) |*context| context.deinit();
            var collision_analysis = cfg.Analysis.init(
                feedback_allocator,
                &result.program,
                result.program.functions[overlap.function_index],
            ) catch |err| switch (err) {
                error.InvalidCfg => return error.NormalizationInvariantFailed,
                error.OutOfMemory => return error.OutOfMemory,
            };
            defer collision_analysis.deinit();
            var collision_edge = overlap.incoming[0];
            var collision_arm: CollisionArm = .{
                .source = collision_edge.source,
                .kind = collision_edge.kind,
                .target = collision_edge.target,
                .context = selected_context,
            };
            var collision_seedable = !seeded_fallback;
            const previous_collision_arm = try findPreviouslyTriedCollisionArmWithAnalysis(
                &result.program,
                &collision_analysis,
                collision_arms.items,
                collision_arm,
                collision_projection_context,
            );
            // Collision arms are scratch-local, but authenticated clone
            // ownership persists in the rewrite history.  Recover an
            // independently composed owner before selecting another split;
            // otherwise a resumed invocation can clone the same source/target
            // composition forever after its in-memory arm set is reset.
            if (previous_collision_arm == null) {
                // A target clone can be the only historical evidence needed
                // for a safe fold.  Use the candidate's own incoming source
                // as the owner edge; directTargetBridgeIsAuthenticated still
                // requires the exact node-split arm, continuation bridge, and
                // replayed tuple before redirecting it.
                if (collision_projection_context.cloneLineageParent(collision_arm.target)) |target_parent| {
                    const target_owner: CollisionArm = .{
                        .source = collision_arm.source,
                        .kind = collision_arm.kind,
                        .target = target_parent.block,
                        .context = null,
                    };
                    const rewrite_start = rewrites.items.len;
                    const folded = try collapseAuthenticatedTargetLineageChain(
                        allocator,
                        feedback_allocator,
                        &result.program,
                        &blocks,
                        &rewrites,
                        overlap.function_index,
                        target_owner,
                        collision_arm,
                        collision_projection_context,
                    );
                    if (folded != 0) {
                        traceNormalize("normalize_phase direct_target_parent_chain_fold iteration={} function={} folds={}\n", .{
                            iteration,
                            overlap.function_index,
                            folded,
                        });
                        collision_seed = try collisionSeedForLatestCloneFold(
                            feedback_allocator,
                            &result.program,
                            overlap.function_index,
                            rewrite_start,
                            collision_arm.context,
                            collision_projection_context,
                        );
                        continue;
                    }
                }
                if (historicalOwnerComposedArmForCandidate(
                    &result.program,
                    collision_arm,
                    collision_projection_context,
                )) |historical_owner| {
                    const rewrite_start = rewrites.items.len;
                    const folded = try collapseAuthenticatedTargetLineageChain(
                        allocator,
                        feedback_allocator,
                        &result.program,
                        &blocks,
                        &rewrites,
                        overlap.function_index,
                        historical_owner,
                        collision_arm,
                        collision_projection_context,
                    );
                    if (folded != 0) {
                        traceNormalize("normalize_phase target_lineage_chain_fold iteration={} function={} folds={}\n", .{
                            iteration,
                            overlap.function_index,
                            folded,
                        });
                        collision_seed = try collisionSeedForLatestCloneFold(
                            feedback_allocator,
                            &result.program,
                            overlap.function_index,
                            rewrite_start,
                            collision_arm.context,
                            collision_projection_context,
                        );
                        continue;
                    }
                }
            }
            if (previous_collision_arm) |previous| {
                if (try collapseAuthenticatedTransparentCollisionEdge(
                    allocator,
                    &result.program,
                    &blocks,
                    &rewrites,
                    &collision_analysis,
                    overlap.function_index,
                    previous,
                    collision_arm,
                    collision_projection_context,
                )) {
                    collision_seed = null;
                    continue;
                }
                if (try collapsePairedCollisionEdge(
                    allocator,
                    &result.program,
                    &blocks,
                    &rewrites,
                    previous,
                    collision_arm,
                    collision_projection_context,
                )) {
                    collision_seed = collisionSeedForPairedForwarding(
                        overlap.function_index,
                        previous,
                        collision_arm,
                    );
                    continue;
                }
                if (try collapseOwnerComposedCollisionEdge(
                    allocator,
                    &result.program,
                    &blocks,
                    &rewrites,
                    &collision_analysis,
                    previous,
                    collision_arm,
                    collision_projection_context,
                )) {
                    collision_seed = null;
                    continue;
                }
                var alternative: ?structural_overlap.Split = null;
                var alternative_context = selected_context;
                var alternative_seedable = true;
                var authenticated_boundary_alternative = false;
                if (alternative == null) {
                    if (try findPredecessorCollisionSplitAllocWithAnalysisAndReplayContext(
                        feedback_allocator,
                        &result.program,
                        &collision_analysis,
                        overlap.function_index,
                        collision_arm.target,
                        null,
                        collision_arms.items,
                        false,
                        selected_context,
                        collision_projection_context,
                    )) |target_alternative| {
                        alternative = try freshCollisionAlternativeWithAnalysis(
                            &result.program,
                            &collision_analysis,
                            target_alternative,
                            collision_arms.items,
                            collision_projection_context,
                            fallbackCollisionContextForArm(
                                &result.program,
                                target_alternative.incoming[0],
                                selected_context,
                            ),
                        );
                    }
                    // A predecessor split is anchored at the live collision
                    // target. Its edge still carries no structured visit
                    // proof, so rebuild that context on the next scan.
                    if (alternative != null) {
                        alternative_context = fallbackCollisionContextForSplit(
                            &result.program,
                            alternative.?,
                            selected_context,
                        );
                        alternative_seedable = false;
                    }
                }
                if (alternative == null) {
                    if (try findSiblingCollisionSplitAllocWithAnalysis(
                        feedback_allocator,
                        &result.program,
                        &collision_analysis,
                        overlap.function_index,
                        previous.target,
                        collision_arm.source,
                        collision_arms.items,
                        selected_context,
                        collision_projection_context,
                        collision_arm.target,
                    )) |sibling_alternative| {
                        alternative = try freshCollisionAlternativeWithAnalysis(
                            &result.program,
                            &collision_analysis,
                            sibling_alternative,
                            collision_arms.items,
                            collision_projection_context,
                            fallbackCollisionContextForSplit(
                                &result.program,
                                sibling_alternative,
                                selected_context,
                            ),
                        );
                    }
                    // The sibling helper is now target-anchored as well as
                    // lineage-authenticated. Its edge still carries no visit
                    // context for the alternate incoming edge.
                    if (alternative != null) {
                        alternative_context = fallbackCollisionContextForSplit(
                            &result.program,
                            alternative.?,
                            selected_context,
                        );
                        alternative_seedable = false;
                    }
                }
                if (alternative == null) {
                    if (try findPredecessorCollisionSplitAllocWithAnalysisAndReplayContext(
                        feedback_allocator,
                        &result.program,
                        &collision_analysis,
                        overlap.function_index,
                        collision_arm.source,
                        null,
                        collision_arms.items,
                        false,
                        selected_context,
                        collision_projection_context,
                    )) |source_alternative| {
                        alternative = try freshCollisionAlternativeWithAnalysis(
                            &result.program,
                            &collision_analysis,
                            source_alternative,
                            collision_arms.items,
                            collision_projection_context,
                            fallbackCollisionContextForArm(
                                &result.program,
                                source_alternative.incoming[0],
                                selected_context,
                            ),
                        );
                    }
                    // This source-side predecessor fallback also returns only
                    // the split edge. Its context must be rebuilt by the next
                    // full scan rather than inherited from the repeated arm.
                    if (alternative != null) {
                        alternative_context = fallbackCollisionContextForSplit(
                            &result.program,
                            alternative.?,
                            selected_context,
                        );
                        alternative_seedable = false;
                    }
                }
                // Independently cloned endpoints can authenticate the same
                // continuation without leaving a fresh arm at the current
                // destination. In that case, split from the durable owner's
                // boundary instead of cloning the composed edge again. The
                // fallback is deliberately unseeded: its context belongs to
                // the newly selected edge and must be rebuilt by the next
                // full scan.
                if (alternative == null) {
                    if (try findDirectTargetBridgeAlternativeWithAnalysis(
                        feedback_allocator,
                        &result.program,
                        &collision_analysis,
                        overlap.function_index,
                        previous,
                        collision_arm,
                        collision_arms.items,
                        collision_projection_context,
                    )) |direct_target_alternative| {
                        alternative = direct_target_alternative;
                        alternative_context = null;
                        alternative_seedable = false;
                        authenticated_boundary_alternative = true;
                    }
                }
                if (alternative == null) {
                    if (try findOwnerComposedDirectBridgeAlternativeWithAnalysis(
                        feedback_allocator,
                        &result.program,
                        &collision_analysis,
                        overlap.function_index,
                        previous,
                        collision_arm,
                        collision_arms.items,
                        collision_projection_context,
                    )) |direct_boundary_alternative| {
                        alternative = direct_boundary_alternative;
                        alternative_context = null;
                        alternative_seedable = false;
                        authenticated_boundary_alternative = true;
                    }
                }
                if (alternative == null) {
                    if (try findOwnerComposedBoundaryAlternativeWithAnalysis(
                        feedback_allocator,
                        &result.program,
                        &collision_analysis,
                        overlap.function_index,
                        previous,
                        collision_arm,
                        collision_arms.items,
                        collision_projection_context,
                    )) |boundary_alternative| {
                        alternative = boundary_alternative;
                        alternative_context = null;
                        alternative_seedable = false;
                    }
                }
                // A paired source/target clone is already an authenticated
                // continuation step.  Do not enter the whole-program
                // deferred planner to rediscover that chain, and do not let
                // an unrelated deferred collision starve the local proof
                // searches above.  Deferred scheduling is a last resort for
                // a genuinely different arm after same-family alternatives
                // have been exhausted.
                if (alternative == null and
                    !sameNodeSplitAdjacentArmLineageWithReplay(
                        collision_projection_context,
                        previous,
                        collision_arm,
                    ) and !sameNodeSplitPairedArmLineageWithReplay(
                    &result.program,
                    collision_projection_context,
                    previous,
                    collision_arm,
                )) {
                    if (try findDeferredCollisionSplitAlloc(
                        feedback_allocator,
                        &result.program,
                        collision_arm,
                        collision_arms.items,
                        only_function,
                        collision_projection_context,
                    )) |deferred_alternative| {
                        alternative = try freshCollisionAlternativeWithAnalysis(
                            &result.program,
                            &collision_analysis,
                            deferred_alternative.split,
                            collision_arms.items,
                            collision_projection_context,
                            fallbackCollisionContextForSplit(
                                &result.program,
                                deferred_alternative.split,
                                selected_context,
                            ),
                        );
                        if (alternative != null) {
                            // Deferred planning runs on a masked copy of the
                            // graph. Its visit context is not proof for the
                            // live edge that will receive this split; rebuild
                            // it in the next full scan instead of seeding a
                            // retry.
                            alternative_context = fallbackCollisionContextForSplit(
                                &result.program,
                                alternative.?,
                                selected_context,
                            );
                            alternative_seedable = false;
                        }
                    }
                }
                collision_seedable = alternative_seedable;
                const chosen_alternative = alternative orelse {
                    std.debug.print("normalize failure phase=feedback-no-alternative iteration={} source={} target={} blocks={} structural_clones={} rewrites={} arms={}\n", .{ iteration, collision_arm.source.index(), collision_arm.target.index(), blocks.items.len, structural_cloned_blocks, rewrites.items.len, collision_arms.items.len });
                    if (stage_trace.enabled) {
                        if (previous_collision_arm) |owner_arm| {
                            const exact_position = owner_arm.source == collision_arm.source and
                                owner_arm.kind == collision_arm.kind and
                                owner_arm.target == collision_arm.target;
                            const direct_position = sameNodeSplitDirectArmLineage(
                                result.program.edge_rewrites,
                                owner_arm,
                                collision_arm,
                            );
                            const adjacent_lineage = sameNodeSplitAdjacentArmLineageWithReplay(
                                collision_projection_context,
                                owner_arm,
                                collision_arm,
                            );
                            const paired_lineage = sameNodeSplitPairedArmLineageWithReplay(
                                &result.program,
                                collision_projection_context,
                                owner_arm,
                                collision_arm,
                            );
                            const owner_composed = try sameNodeSplitOwnerComposedArmLineageWithReplay(
                                &result.program,
                                &collision_analysis,
                                collision_projection_context,
                                owner_arm,
                                collision_arm,
                            );
                            const source_lineage = sameNodeSplitLineage(
                                result.program.edge_rewrites,
                                owner_arm.source,
                                collision_arm.source,
                            );
                            const target_lineage = sameNodeSplitLineage(
                                result.program.edge_rewrites,
                                owner_arm.target,
                                collision_arm.target,
                            );
                            const continuation_bridge = try collision_projection_context.hasAuthenticatedContinuationBridgeForEdge(
                                &collision_analysis,
                                .{
                                    .source = collision_arm.source,
                                    .kind = collision_arm.kind,
                                    .target = collision_arm.target,
                                },
                            );
                            std.debug.print("feedback_repeated_owner previous_source={} previous_target={} exact={} direct={} adjacent={} paired={} owner_composed={} source_lineage={} target_lineage={} bridge={}\n", .{
                                owner_arm.source.index(),
                                owner_arm.target.index(),
                                exact_position,
                                direct_position,
                                adjacent_lineage,
                                paired_lineage,
                                owner_composed,
                                source_lineage,
                                target_lineage,
                                continuation_bridge,
                            });
                        }
                        for (collision_arms.items) |arm| {
                            const source_root = if (nodeSplitRoot(result.program.edge_rewrites, arm.source)) |root| root.index() else null;
                            const target_root = if (nodeSplitRoot(result.program.edge_rewrites, arm.target)) |root| root.index() else null;
                            std.debug.print("feedback_tried_arm source={} kind={s} target={} source_root={?d} target_root={?d}\n", .{
                                arm.source.index(),
                                @tagName(arm.kind),
                                arm.target.index(),
                                source_root,
                                target_root,
                            });
                        }
                        const current_source_root = if (nodeSplitRoot(result.program.edge_rewrites, collision_arm.source)) |root| root.index() else null;
                        const current_target_root = if (nodeSplitRoot(result.program.edge_rewrites, collision_arm.target)) |root| root.index() else null;
                        std.debug.print("feedback_current_arm source={} target={} source_root={?d} target_root={?d} args=", .{
                            collision_arm.source.index(),
                            collision_arm.target.index(),
                            current_source_root,
                            current_target_root,
                        });
                        if (cfg_edge.value(&result.program, .{
                            .source = collision_arm.source,
                            .kind = collision_arm.kind,
                            .target = collision_arm.target,
                        })) |edge| {
                            for (edge.arguments) |value_id| std.debug.print(" {}", .{value_id.index()});
                        }
                        std.debug.print("\n", .{});
                        for (result.program.edge_rewrites) |rewrite| {
                            if (rewrite.rule != .node_split or
                                (rewrite.from.target != collision_arm.source and rewrite.to.target != collision_arm.source and
                                    rewrite.from.target != collision_arm.target and rewrite.to.target != collision_arm.target)) continue;
                            std.debug.print("feedback_current_rewrite id={} source={} from={} to={} group={?} from_args={any} to_args={any}\n", .{
                                rewrite.id.index(),
                                rewrite.source.index(),
                                rewrite.from.target.index(),
                                rewrite.to.target.index(),
                                rewrite.node_split_group,
                                rewrite.from.arguments,
                                rewrite.to.arguments,
                            });
                        }
                    }
                    return error.NormalizationInvariantFailed;
                };
                if (alternative != null) {
                    traceNormalize("normalize_phase feedback_alternative iteration={} original_source={} original_kind={s} original_target={} alternative_branch={} alternative_entry={} alternative_join={} alternative_incoming={any} authenticated_boundary={} seedable={}\n", .{
                        iteration,
                        collision_arm.source.index(),
                        @tagName(collision_arm.kind),
                        collision_arm.target.index(),
                        alternative.?.branch.index(),
                        alternative.?.entry.index(),
                        alternative.?.join.index(),
                        alternative.?.incoming,
                        authenticated_boundary_alternative,
                        alternative_seedable,
                    });
                }
                overlap.deinit();
                overlap = chosen_alternative;
                collision_edge = overlap.incoming[0];
                collision_arm = .{
                    .source = collision_edge.source,
                    .kind = collision_edge.kind,
                    .target = collision_edge.target,
                    .context = alternative_context,
                };
                if (!authenticated_boundary_alternative and try findPreviouslyTriedCollisionArmWithAnalysis(
                    &result.program,
                    &collision_analysis,
                    collision_arms.items,
                    collision_arm,
                    collision_projection_context,
                ) != null) {
                    const source_root = if (nodeSplitRoot(result.program.edge_rewrites, collision_arm.source)) |root| root.index() else null;
                    const target_root = if (nodeSplitRoot(result.program.edge_rewrites, collision_arm.target)) |root| root.index() else null;
                    const previous_source_root = if (nodeSplitRoot(result.program.edge_rewrites, previous.source)) |root| root.index() else null;
                    const previous_target_root = if (nodeSplitRoot(result.program.edge_rewrites, previous.target)) |root| root.index() else null;
                    std.debug.print("normalize failure phase=feedback-repeated-alternative iteration={} source={} target={} previous_source={} previous_target={} source_root={?d} target_root={?d} previous_source_root={?d} previous_target_root={?d} blocks={} structural_clones={} rewrites={} arms={}\n", .{
                        iteration,
                        collision_arm.source.index(),
                        collision_arm.target.index(),
                        previous.source.index(),
                        previous.target.index(),
                        source_root,
                        target_root,
                        previous_source_root,
                        previous_target_root,
                        blocks.items.len,
                        structural_cloned_blocks,
                        rewrites.items.len,
                        collision_arms.items.len,
                    });
                    return error.NormalizationInvariantFailed;
                }
            }
            try collision_arms.append(scratch_allocator, collision_arm);
            structural_cloned_blocks = std.math.add(usize, structural_cloned_blocks, overlap.closure.len) catch
                return error.NormalizationInvariantFailed;
            if (structural_cloned_blocks > structural_clone_limit) {
                std.debug.print("normalize failure phase=feedback-clone-limit iteration={} blocks={} structural_clones={} limit={} rewrites={} arms={}\n", .{ iteration, blocks.items.len, structural_cloned_blocks, structural_clone_limit, rewrites.items.len, collision_arms.items.len });
                return error.NormalizationInvariantFailed;
            }

            const incoming = try feedback_allocator.dupe(ir.CfgEdgeRef, overlap.incoming);
            errdefer feedback_allocator.free(incoming);
            const closure = try feedback_allocator.dupe(ir.BlockId, overlap.closure);
            errdefer feedback_allocator.free(closure);
            const secondaries = try feedback_allocator.alloc(Secondary, 1);
            errdefer feedback_allocator.free(secondaries);
            secondaries[0] = .{ .block = overlap.entry, .incoming = incoming, .closure = closure };
            var entry_offset: ?usize = null;
            for (overlap.closure, 0..) |source_id, closure_index| {
                if (source_id == overlap.entry) {
                    entry_offset = closure_index;
                    break;
                }
            }
            const entry_clone_offset = entry_offset orelse return error.NormalizationInvariantFailed;
            const entry_clone_base = blocks.items.len;
            var plan: SplitPlan = .{
                .allocator = feedback_allocator,
                .function_index = overlap.function_index,
                .secondaries = secondaries,
                .secondary_count = 1,
            };
            defer plan.deinit();
            const apply_start = normalizePhaseNow();
            const prior_split = result;
            try applyPlan(allocator, &result.program, &blocks, &functions, &instructions, &values, &packs, &rewrites, &plan, &result);
            traceAppliedSplit("feedback-collision", plan.function_index, prior_split, result);
            traceNormalize("normalize_phase feedback_post_apply iteration={} source={} kind={s} old_target={} old_edge_present={} entry_clone={} blocks={} rewrites={}\n", .{
                iteration,
                collision_edge.source.index(),
                @tagName(collision_edge.kind),
                collision_edge.target.index(),
                cfg_edge.value(&result.program, collision_edge) != null,
                ir.BlockId.fromIndex(entry_clone_base + entry_clone_offset).index(),
                blocks.items.len,
                rewrites.items.len,
            });
            const forwarded = try collapseTransparentForwardingBlocks(
                allocator,
                &result.program,
                &blocks,
                &rewrites,
                only_function,
            );
            if (forwarded != 0) traceNormalize("normalize_phase transparent_forwarding_after_apply iteration={} blocks={} rewrites={} collapsed={}\\n", .{
                iteration,
                blocks.items.len,
                rewrites.items.len,
                forwarded,
            });
            traceNormalize("normalize_phase feedback_apply iteration={} mode=collision ms={} blocks={} rewrites={}\\n", .{
                iteration,
                normalizePhaseMillis(apply_start),
                blocks.items.len,
                rewrites.items.len,
            });
            // The selected arm may have been replaced by a bounded
            // alternative. Preserve the context authenticated for the arm
            // that was actually applied; carrying the pre-alternative context
            // makes the next live edge look like a new collision.
            const applied_previous = if (collision_seed) |seed| seed.previous else null;
            collision_seed = if (collision_seedable)
                try collisionSeedForAppliedArmAfterApply(
                    feedback_allocator,
                    &result.program,
                    overlap.function_index,
                    ir.BlockId.fromIndex(entry_clone_base + entry_clone_offset),
                    collision_arm,
                    applied_previous,
                    overlap.closure,
                    entry_clone_base,
                )
            else
                null;
        } else {
            if (options.feedback_iteration_limit != null) {
                result.program.blocks = blocks.items;
                result.program.functions = functions.items;
                result.program.values = values.items;
                result.program.value_packs = packs.items;
                result.program.instructions = instructions.items;
                result.program.edge_rewrites = rewrites.items;
                result.resume_seed = if (collision_seed) |seed|
                    resumeSeedFromCollisionSeed(seed)
                else
                    null;
                return result;
            }
            std.debug.print("normalize failure phase=feedback-iteration-limit iterations={} blocks={} structural_clones={} rewrites={} arms={}\n", .{ iteration, blocks.items.len, structural_cloned_blocks, rewrites.items.len, collision_arms.items.len });
            return error.NormalizationInvariantFailed;
        }
        result.program.blocks = blocks.items;
        result.program.functions = functions.items;
        result.program.values = values.items;
        result.program.value_packs = packs.items;
        result.program.instructions = instructions.items;
        result.program.edge_rewrites = rewrites.items;
        if (options.feedback_iteration_limit != null) {
            result.resume_seed = if (collision_seed) |seed|
                resumeSeedFromCollisionSeed(seed)
            else
                null;
        }
        break :feedback;
    }

    return result;
}

fn traceUnvisitedPlanCloneLimit(
    program: *const ir.Program,
    plan: *const SplitPlan,
    structural_clones: usize,
    limit: usize,
    rewrites: usize,
    arms: usize,
) void {
    if (!stage_trace.enabled) return;
    const secondaries = plan.secondaries[0..plan.secondary_count];
    var total_closure: usize = 0;
    for (secondaries) |secondary| total_closure += secondary.closure.len;
    std.debug.print("normalize diagnostic phase=feedback-batch-clone-limit secondaries={} total_closure={} structural_clones={} limit={} rewrites={} arms={}\n", .{
        secondaries.len,
        total_closure,
        structural_clones,
        limit,
        rewrites,
        arms,
    });
    for (secondaries, 0..) |secondary, index| {
        if (index >= 64) {
            std.debug.print("normalize diagnostic secondary-truncated remaining={}\n", .{secondaries.len - index});
            break;
        }
        std.debug.print("normalize diagnostic secondary index={} block={} closure={} incoming={}\n", .{
            index,
            secondary.block.index(),
            secondary.closure.len,
            secondary.incoming.len,
        });
        for (secondary.incoming) |reference| {
            std.debug.print("normalize diagnostic incoming source={} kind={s} target={}\n", .{
                reference.source.index(),
                @tagName(reference.kind),
                reference.target.index(),
            });
        }
        for (secondary.closure) |block_id| {
            const root = nodeSplitRoot(program.edge_rewrites, block_id);
            if (block_id.index() >= program.blocks.len) {
                std.debug.print("normalize diagnostic closure-block id={} invalid\n", .{block_id.index()});
                continue;
            }
            const block = program.blocks[block_id.index()];
            std.debug.print("normalize diagnostic closure-block id={} root={?d} parameters={} instructions={} terminator={s}\n", .{
                block_id.index(),
                if (root) |value| value.index() else null,
                block.parameters.len,
                block.instructions.len,
                @tagName(std.meta.activeTag(block.terminator)),
            });
        }
        if (plan.function_index < program.functions.len) {
            for (secondary.closure) |closure_block| {
                const root = nodeSplitRoot(program.edge_rewrites, closure_block) orelse continue;
                var root_count: usize = 0;
                for (program.functions[plan.function_index].blocks) |candidate| {
                    if (nodeSplitRoot(program.edge_rewrites, candidate) == root) root_count += 1;
                }
                std.debug.print("normalize diagnostic lineage-root root={} existing_blocks={} current_block={}\n", .{
                    root.index(),
                    root_count,
                    closure_block.index(),
                });
            }
        }
        for (program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.source != secondary.incoming[0].source) continue;
            std.debug.print("normalize diagnostic source-rewrite source={} kind={s} from={} to={} arguments={any}\n", .{
                rewrite.source.index(),
                @tagName(rewrite.kind),
                rewrite.from.target.index(),
                rewrite.to.target.index(),
                rewrite.to.arguments,
            });
        }
        if (plan.function_index < program.functions.len) {
            const function = program.functions[plan.function_index];
            for (function.blocks) |source_id| {
                if (source_id.index() >= program.blocks.len) continue;
                const block = program.blocks[source_id.index()];
                switch (block.terminator) {
                    .jump => |edge| if (edge.target == secondary.block) {
                        std.debug.print("normalize diagnostic live-incoming source={} kind=jump target={} arguments={any}\n", .{
                            source_id.index(),
                            edge.target.index(),
                            edge.arguments,
                        });
                    },
                    .branch => |branch| {
                        if (branch.then_edge.target == secondary.block) {
                            std.debug.print("normalize diagnostic live-incoming source={} kind=branch_then target={} arguments={any}\n", .{
                                source_id.index(),
                                branch.then_edge.target.index(),
                                branch.then_edge.arguments,
                            });
                        }
                        if (branch.else_edge.target == secondary.block) {
                            std.debug.print("normalize diagnostic live-incoming source={} kind=branch_else target={} arguments={any}\n", .{
                                source_id.index(),
                                branch.else_edge.target.index(),
                                branch.else_edge.arguments,
                            });
                        }
                    },
                    .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
                }
            }
        }
        var closure_members: std.AutoHashMapUnmanaged(ir.BlockId, void) = .empty;
        defer closure_members.deinit(std.heap.page_allocator);
        for (secondary.closure) |block_id| closure_members.put(std.heap.page_allocator, block_id, {}) catch {};
        for (secondary.closure) |block_id| {
            if (block_id.index() >= program.blocks.len) continue;
            const block = program.blocks[block_id.index()];
            switch (block.terminator) {
                .jump => |edge| if (!closure_members.contains(edge.target)) {
                    std.debug.print("normalize diagnostic closure-exit source={} kind=jump target={} arguments={any}\n", .{
                        block_id.index(),
                        edge.target.index(),
                        edge.arguments,
                    });
                },
                .branch => |branch| {
                    if (!closure_members.contains(branch.then_edge.target)) {
                        std.debug.print("normalize diagnostic closure-exit source={} kind=branch_then target={} arguments={any}\n", .{
                            block_id.index(),
                            branch.then_edge.target.index(),
                            branch.then_edge.arguments,
                        });
                    }
                    if (!closure_members.contains(branch.else_edge.target)) {
                        std.debug.print("normalize diagnostic closure-exit source={} kind=branch_else target={} arguments={any}\n", .{
                            block_id.index(),
                            branch.else_edge.target.index(),
                            branch.else_edge.arguments,
                        });
                    }
                },
                .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
            }
        }
    }
    var overlap_records: usize = 0;
    for (secondaries, 0..) |left, left_index| {
        for (secondaries[left_index + 1 ..], left_index + 1..) |right, right_index| {
            var overlap: usize = 0;
            var first_overlap: ?ir.BlockId = null;
            for (left.closure) |left_block| {
                for (right.closure) |right_block| {
                    if (left_block != right_block) continue;
                    overlap += 1;
                    if (first_overlap == null) first_overlap = left_block;
                }
            }
            if (overlap == 0) continue;
            if (overlap_records < 128) {
                std.debug.print("normalize diagnostic closure-overlap left={} right={} count={} first={}\n", .{
                    left_index,
                    right_index,
                    overlap,
                    first_overlap.?.index(),
                });
            }
            overlap_records += 1;
        }
    }
    if (overlap_records > 128) {
        std.debug.print("normalize diagnostic closure-overlap-truncated remaining={}\n", .{overlap_records - 128});
    }
}

fn findCollisionArm(arms: []const CollisionArm, candidate: CollisionArm) ?CollisionArm {
    for (arms) |arm| {
        if (arm.source == candidate.source and arm.kind == candidate.kind and arm.target == candidate.target and
            sameCollisionContext(arm.context, candidate.context)) return arm;
    }
    return null;
}

/// A missing context is not evidence that two arms are distinct. Once both
/// sides carry an authenticated context, however, the context is part of the
/// continuation identity even when block lineage and edge kind agree.
fn sameCollisionContext(
    left: ?structure.CollisionContext,
    right: ?structure.CollisionContext,
) bool {
    if (left == null or right == null) return true;
    return std.meta.eql(left.?, right.?);
}

// A seeded collision retry preserves the control boundary from the previous
// visit, but the edge may now enter a clone with a remapped loop-carried tuple.
// Keep the structural context and refresh only the tuple from the live edge;
// replay authentication still decides whether the two tuples are equivalent.
fn collisionContextWithCurrentEdgeArguments(
    program: *const ir.Program,
    context: ?structure.CollisionContext,
    reference: ir.CfgEdgeRef,
) ?structure.CollisionContext {
    var refreshed = context orelse return null;
    const edge = cfg_edge.value(program, reference) orelse return context;
    refreshed.parameter_arguments = edge.arguments;
    return refreshed;
}

fn findLineageCollisionArm(
    rewrites: []const ir.CfgEdgeRewrite,
    arms: []const CollisionArm,
    candidate: CollisionArm,
) ?CollisionArm {
    for (arms) |arm| {
        if (arm.kind != candidate.kind) continue;
        if (!sameCollisionContext(arm.context, candidate.context)) continue;
        if (sameNodeSplitLineage(rewrites, arm.source, candidate.source) and
            sameNodeSplitLineage(rewrites, arm.target, candidate.target)) return arm;
    }
    return null;
}

fn sameCollisionBoundary(
    rewrites: []const ir.CfgEdgeRewrite,
    left: ir.BlockId,
    right: ir.BlockId,
) bool {
    return left == right or
        sameNodeSplitLineage(rewrites, left, right) or
        sameNodeSplitDirectTargetLineage(rewrites, left, right);
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

fn sameNodeSplitDirectArmLineage(
    rewrites: []const ir.CfgEdgeRewrite,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    if (left.kind != right.kind) return false;
    for (rewrites) |rewrite| {
        if (rewrite.rule == .node_split and
            rewrite.source == left.source and
            rewrite.kind == left.kind and
            left.source == right.source and
            rewrite.from.target == left.target and
            rewrite.to.target == right.target)
        {
            return true;
        }
        if (rewrite.rule == .node_split and
            rewrite.source == right.source and
            rewrite.kind == right.kind and
            left.source == right.source and
            rewrite.from.target == right.target and
            rewrite.to.target == left.target)
        {
            return true;
        }
    }
    return false;
}

// A repeated parameterized continuation can acquire a fresh stop block on
// every sibling split. The stop is a structural context boundary, so a shared
// split root remains admissible there when the tuple proof below succeeds.
// Continuation endpoints use the stricter helper below: a shared root alone
// must never merge two nested feedback continuations.
fn sameCollisionContextStop(
    rewrites: []const ir.CfgEdgeRewrite,
    left: ?ir.BlockId,
    right: ?ir.BlockId,
) bool {
    if (left == null or right == null) return left == right;
    if (sameCollisionBoundary(rewrites, left.?, right.?)) return true;
    const left_root = nodeSplitRoot(rewrites, left.?) orelse return false;
    const right_root = nodeSplitRoot(rewrites, right.?) orelse return false;
    return left_root == right_root;
}

fn sameCollisionContextContinue(
    rewrites: []const ir.CfgEdgeRewrite,
    left: ?ir.BlockId,
    right: ?ir.BlockId,
) bool {
    if (left == null or right == null) return left == right;
    return sameCollisionBoundary(rewrites, left.?, right.?);
}

fn sameCollisionArmPosition(
    rewrites: []const ir.CfgEdgeRewrite,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    if (left.kind != right.kind) return false;

    // Prefer the exact incoming arm rewrite.  The destination may be a join
    // with multiple cloned predecessors, for which whole-node lineage is
    // intentionally ambiguous.
    if (sameNodeSplitDirectArmLineage(rewrites, left, right)) return true;

    // A cloned continuation rewrites the outgoing edge from the cloned
    // source as well as the cloned target.  That authenticated edge step is
    // sufficient to recognize the next arm in the same continuation chain;
    // require it before the stricter source-lineage comparison below.
    if (sameNodeSplitAdjacentArmLineage(rewrites, left, right)) return true;

    // The source edge is the owner of the incoming transition. Permit an
    // exact source or a complete authenticated source lineage only. Target
    // identity follows the same rule: a shared split root is not a complete
    // lineage, because nested continuation groups can share that root.
    const source_matches = left.source == right.source or
        sameNodeSplitLineage(rewrites, left.source, right.source);
    if (!source_matches) return false;
    return left.target == right.target or
        sameNodeSplitAncestorArmLineage(rewrites, left, right) or
        sameNodeSplitAncestorArmLineage(rewrites, right, left) or
        sameNodeSplitLineage(rewrites, left.target, right.target) or
        sameNodeSplitRootBoundary(rewrites, left.target, right.target);
}

// A root and its direct split clone are one authenticated destination
// boundary. Once both targets are descendants, root equality is insufficient:
// nested continuation groups can share that root while representing different
// feedback arms.
fn sameNodeSplitRootBoundary(
    rewrites: []const ir.CfgEdgeRewrite,
    left: ir.BlockId,
    right: ir.BlockId,
) bool {
    const left_root = nodeSplitRoot(rewrites, left) orelse return false;
    const right_root = nodeSplitRoot(rewrites, right) orelse return false;
    if (left_root != right_root) return false;
    if (left == left_root) {
        return switch (nodeSplitLineageParent(rewrites, right)) {
            .parent => |parent| parent.block == left_root,
            else => false,
        };
    }
    if (right == right_root) {
        return switch (nodeSplitLineageParent(rewrites, left)) {
            .parent => |parent| parent.block == right_root,
            else => false,
        };
    }
    return false;
}

fn hasDirectNodeSplitArmEdge(
    rewrites: []const ir.CfgEdgeRewrite,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    from: ir.BlockId,
    to: ir.BlockId,
) bool {
    for (rewrites) |rewrite| {
        if (rewrite.rule == .node_split and
            rewrite.source == source and
            rewrite.kind == kind and
            rewrite.from.target == from and
            rewrite.to.target == to)
        {
            return true;
        }
    }
    return false;
}

// A repeated edge can walk through a chain of clones that were each created
// by that same edge. Treat adjacent targets in that chain as one arm only
// when exact rewrite records authenticate both steps. This does not merge a
// nested target created by another incoming edge merely because the roots
// happen to agree.
fn sameNodeSplitAdjacentArmLineage(
    rewrites: []const ir.CfgEdgeRewrite,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    if (left.kind != right.kind) return false;

    const left_parent = nodeSplitLineageParent(rewrites, left.target);
    const right_parent = nodeSplitLineageParent(rewrites, right.target);
    const left_to_right = switch (left_parent) {
        .parent => |parent| parent.block == right.target,
        else => false,
    };
    const right_to_left = switch (right_parent) {
        .parent => |parent| parent.block == left.target,
        else => false,
    };
    const left_direct = left_to_right and hasDirectNodeSplitArmEdge(
        rewrites,
        left.source,
        left.kind,
        right.target,
        left.target,
    );
    const right_direct = right_to_left and hasDirectNodeSplitArmEdge(
        rewrites,
        right.source,
        right.kind,
        left.target,
        right.target,
    );
    return left_direct or right_direct;
}

// A continuation can clone both endpoints of an edge more than once.  A
// shared split root is not enough to identify that chain: each step must carry
// the same authenticated group on the source and target parents, and the
// cloned source must still own the recorded target edge.  Check the current
// edge arguments on the first step so a stale or tampered rewrite cannot skip
// the deferred planner.
fn sameNodeSplitPairedArmLineageForward(
    program: *const ir.Program,
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
        if (steps >= program.edge_rewrites.len) return false;
        const source_parent: ?NodeSplitLineageParent = switch (nodeSplitLineageParent(
            program.edge_rewrites,
            current_source,
        )) {
            .parent => |parent| parent,
            .none => null,
            .invalid => return false,
        };
        const target_parent: ?NodeSplitLineageParent = switch (nodeSplitLineageParent(
            program.edge_rewrites,
            current_target,
        )) {
            .parent => |parent| parent,
            .none => null,
            .invalid => return false,
        };

        if (source_parent) |source_step| {
            if (target_parent) |target_step| {
                const group = source_step.group orelse return false;
                if (target_step.group == group) {
                    if (findNodeSplitArmEdgeInGroup(
                        program.edge_rewrites,
                        current_source,
                        right.kind,
                        target_step.block,
                        current_target,
                        group,
                    )) |target_rewrite| {
                        if (steps == 0) {
                            const live = cfg_edge.value(program, .{
                                .source = current_source,
                                .kind = right.kind,
                                .target = current_target,
                            }) orelse return false;
                            if (live.target != current_target or
                                !std.mem.eql(ir.ValueId, live.arguments, target_rewrite.to.arguments)) return false;
                        }
                        current_source = source_step.block;
                        current_target = target_step.block;
                        paired_steps += 1;
                        continue;
                    }
                }
            }
        }

        // A target may pass through an authenticated nested clone between two
        // paired endpoint steps. Keep the source fixed for that transition;
        // the next paired step must still authenticate the shared group.
        const target_step = target_parent orelse return false;
        const target_rewrite = findNodeSplitArmEdge(
            program.edge_rewrites,
            current_source,
            right.kind,
            target_step.block,
            current_target,
        ) orelse return false;
        if (steps == 0) {
            const live = cfg_edge.value(program, .{
                .source = current_source,
                .kind = right.kind,
                .target = current_target,
            }) orelse return false;
            if (live.target != current_target or
                !std.mem.eql(ir.ValueId, live.arguments, target_rewrite.to.arguments)) return false;
        }
        current_target = target_step.block;
    }
    return steps != 0 and paired_steps != 0;
}

fn sameNodeSplitPairedArmLineage(
    program: *const ir.Program,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    return sameNodeSplitPairedArmLineageForward(program, left, right) or
        sameNodeSplitPairedArmLineageForward(program, right, left);
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

fn hasNodeSplitTargetArmEdgeInGroup(
    projection: *const structural_overlap.ReplayProjectionContext,
    kind: ir.CfgEdgeKind,
    from: ir.BlockId,
    to: ir.BlockId,
    group: ir.NodeSplitGroupId,
) ?ir.CfgEdgeRewrite {
    for (projection.nodeSplitRewriteIndicesForGroup(group)) |rewrite_index| {
        const rewrite = projection.program.edge_rewrites[rewrite_index];
        if (rewrite.rule == .node_split and
            rewrite.kind == kind and
            rewrite.from.target == from and
            rewrite.to.target == to) return rewrite;
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

// A repeated continuation split can advance the destination through more
// than one authenticated clone while the incoming edge owner stays fixed.
// Compare the complete target chain and require every step to be owned by the
// same edge source. This is deliberately separate from root equality: a
// shared clone root does not authenticate nested continuation groups.
fn sameNodeSplitAncestorArmLineage(
    rewrites: []const ir.CfgEdgeRewrite,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    if (left.kind != right.kind or left.source != right.source or left.target == right.target) return false;

    var current = right.target;
    var depth: usize = 0;
    while (current != left.target) : (depth += 1) {
        if (depth > rewrites.len) return false;
        const parent = switch (nodeSplitLineageParent(rewrites, current)) {
            .parent => |value| value,
            else => return false,
        };
        if (!hasDirectNodeSplitArmEdge(
            rewrites,
            right.source,
            right.kind,
            parent.block,
            current,
        )) return false;
        current = parent.block;
    }
    return true;
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

// Reconstruct the durable owner of an independently composed source/target
// clone pair.  The owner is not scratch history: both parent blocks and their
// split groups are authenticated by the persisted node-split lineage.  Keep
// the helper conservative and let the full bridge proof validate the live
// edge, tuple, and continuation before any rewrite is applied.
fn historicalOwnerComposedArmForCandidate(
    program: *const ir.Program,
    candidate: CollisionArm,
    projection: *const structural_overlap.ReplayProjectionContext,
) ?CollisionArm {
    if (candidate.source.index() >= program.blocks.len or
        candidate.target.index() >= program.blocks.len)
    {
        return null;
    }
    const source_parent = projection.cloneLineageParent(candidate.source) orelse return null;
    const target_parent = projection.cloneLineageParent(candidate.target) orelse return null;
    if (source_parent.block == candidate.source or
        target_parent.block == candidate.target or
        source_parent.group == target_parent.group)
    {
        return null;
    }
    return .{
        .source = source_parent.block,
        .kind = candidate.kind,
        .target = target_parent.block,
        .context = null,
    };
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

fn collisionArmWasTried(
    program: *const ir.Program,
    arms: []const CollisionArm,
    candidate: CollisionArm,
    projection_context: ?*structural_overlap.ReplayProjectionContext,
) NormalizeError!bool {
    return collisionArmWasTriedWithAnalysis(
        program,
        null,
        arms,
        candidate,
        projection_context,
    );
}

fn collisionArmWasTriedWithAnalysis(
    program: *const ir.Program,
    analysis: ?*const cfg.Analysis,
    arms: []const CollisionArm,
    candidate: CollisionArm,
    projection_context: ?*structural_overlap.ReplayProjectionContext,
) NormalizeError!bool {
    if (projection_context) |context| {
        return (try findPreviouslyTriedCollisionArmWithAnalysis(
            program,
            analysis,
            arms,
            candidate,
            context,
        )) != null;
    }
    return findCollisionArm(arms, candidate) != null or
        findLineageCollisionArm(program.edge_rewrites, arms, candidate) != null;
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

/// Return the authenticated parent of a split clone. A clone target may have
/// several incoming rewrites from one split group, but those rewrites must
/// agree on the parent and group before the lineage is usable for feedback.
fn nodeSplitLineageParent(
    rewrites: []const ir.CfgEdgeRewrite,
    current: ir.BlockId,
) NodeSplitLineageStep {
    var parent: ?NodeSplitLineageParent = null;
    for (rewrites) |rewrite| {
        if (rewrite.rule != .node_split or rewrite.to.target != current) continue;
        const candidate = NodeSplitLineageParent{
            .block = rewrite.from.target,
            .group = rewrite.node_split_group,
        };
        if (parent) |existing| {
            if (existing.block != candidate.block or existing.group != candidate.group) return .invalid;
        } else {
            parent = candidate;
        }
    }
    return if (parent) |value| .{ .parent = value } else .none;
}

/// Compare the complete authenticated split lineage, not just its root.
/// Distinct nested continuations intentionally share roots while carrying an
/// additional split group; treating them as the same feedback arm prevents
/// the normalizer from selecting the valid continuation.
fn sameNodeSplitLineage(
    rewrites: []const ir.CfgEdgeRewrite,
    left: ir.BlockId,
    right: ir.BlockId,
) bool {
    const left_root = nodeSplitRoot(rewrites, left) orelse return false;
    const right_root = nodeSplitRoot(rewrites, right) orelse return false;
    if (left_root != right_root) return false;

    var left_current = left;
    var right_current = right;
    var depth: usize = 0;
    while (depth <= rewrites.len) : (depth += 1) {
        const left_parent = nodeSplitLineageParent(rewrites, left_current);
        const right_parent = nodeSplitLineageParent(rewrites, right_current);
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

fn sameNodeSplitRootBoundaryWithIndex(
    index: *const FeedbackLineageIndex,
    left: ir.BlockId,
    right: ir.BlockId,
) bool {
    const left_root = index.root(left) orelse return false;
    const right_root = index.root(right) orelse return false;
    if (left_root != right_root) return false;
    if (left == left_root) {
        return switch (index.lineageParent(right)) {
            .parent => |parent| parent.block == left_root,
            else => false,
        };
    }
    if (right == right_root) {
        return switch (index.lineageParent(left)) {
            .parent => |parent| parent.block == right_root,
            else => false,
        };
    }
    return false;
}

fn sameNodeSplitAdjacentArmLineageWithIndex(
    index: *const FeedbackLineageIndex,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    if (left.kind != right.kind) return false;

    const left_parent = index.lineageParent(left.target);
    const right_parent = index.lineageParent(right.target);
    const left_to_right = switch (left_parent) {
        .parent => |parent| parent.block == right.target,
        else => false,
    };
    const right_to_left = switch (right_parent) {
        .parent => |parent| parent.block == left.target,
        else => false,
    };
    const left_direct = left_to_right and index.hasDirectEdge(
        left.source,
        left.kind,
        right.target,
        left.target,
    );
    const right_direct = right_to_left and index.hasDirectEdge(
        right.source,
        right.kind,
        left.target,
        right.target,
    );
    return left_direct or right_direct;
}

fn sameNodeSplitAncestorArmLineageWithIndex(
    index: *const FeedbackLineageIndex,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    if (left.kind != right.kind or left.source != right.source or left.target == right.target) return false;

    var current = right.target;
    var depth: usize = 0;
    while (current != left.target) : (depth += 1) {
        if (depth > index.lineage_parents.len) return false;
        const parent = switch (index.lineageParent(current)) {
            .parent => |value| value,
            else => return false,
        };
        if (!index.hasDirectEdge(right.source, right.kind, parent.block, current)) return false;
        current = parent.block;
    }
    return true;
}

fn sameNodeSplitPairedArmLineageForwardWithIndex(
    program: *const ir.Program,
    index: *const FeedbackLineageIndex,
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
        if (steps >= index.lineage_parents.len) return false;
        const source_parent: ?NodeSplitLineageParent = switch (index.lineageParent(current_source)) {
            .parent => |parent| parent,
            .none => null,
            .invalid => return false,
        };
        const target_parent: ?NodeSplitLineageParent = switch (index.lineageParent(current_target)) {
            .parent => |parent| parent,
            .none => null,
            .invalid => return false,
        };

        if (source_parent) |source_step| {
            if (target_parent) |target_step| {
                const group = source_step.group orelse return false;
                if (target_step.group == group and index.hasGroupedEdge(
                    current_source,
                    right.kind,
                    target_step.block,
                    current_target,
                    group,
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
                            group,
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
        if (!index.hasDirectEdge(
            current_source,
            right.kind,
            target_step.block,
            current_target,
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

fn sameNodeSplitPairedArmLineageWithIndex(
    program: *const ir.Program,
    index: *const FeedbackLineageIndex,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    return sameNodeSplitPairedArmLineageForwardWithIndex(program, index, left, right) or
        sameNodeSplitPairedArmLineageForwardWithIndex(program, index, right, left);
}

fn sameCollisionArmPositionWithIndex(
    index: *const FeedbackLineageIndex,
    left: CollisionArm,
    right: CollisionArm,
) bool {
    if (left.kind != right.kind) return false;
    if ((left.source == right.source and
        index.hasDirectEdge(left.source, left.kind, left.target, right.target)) or
        (left.source == right.source and
            index.hasDirectEdge(right.source, right.kind, right.target, left.target))) return true;
    if (sameNodeSplitAdjacentArmLineageWithIndex(index, left, right)) return true;

    const source_matches = left.source == right.source or index.sameLineage(left.source, right.source);
    if (!source_matches) return false;
    return left.target == right.target or
        sameNodeSplitAncestorArmLineageWithIndex(index, left, right) or
        sameNodeSplitAncestorArmLineageWithIndex(index, right, left) or
        index.sameLineage(left.target, right.target) or
        sameNodeSplitRootBoundaryWithIndex(index, left.target, right.target);
}

fn sameCollisionBoundaryWithIndex(
    index: *const FeedbackLineageIndex,
    rewrites: []const ir.CfgEdgeRewrite,
    left: ir.BlockId,
    right: ir.BlockId,
) bool {
    return left == right or index.sameLineage(left, right) or
        sameNodeSplitDirectTargetLineage(rewrites, left, right);
}

fn sameCollisionContextStopWithIndex(
    index: *const FeedbackLineageIndex,
    rewrites: []const ir.CfgEdgeRewrite,
    left: ?ir.BlockId,
    right: ?ir.BlockId,
) bool {
    if (left == null or right == null) return left == right;
    if (sameCollisionBoundaryWithIndex(index, rewrites, left.?, right.?)) return true;
    const left_root = index.root(left.?) orelse return false;
    const right_root = index.root(right.?) orelse return false;
    return left_root == right_root;
}

fn sameCollisionContextContinueWithIndex(
    index: *const FeedbackLineageIndex,
    rewrites: []const ir.CfgEdgeRewrite,
    left: ?ir.BlockId,
    right: ?ir.BlockId,
) bool {
    if (left == null or right == null) return left == right;
    return sameCollisionBoundaryWithIndex(index, rewrites, left.?, right.?);
}

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

fn mapEdgeArgumentsBackwardThroughClone(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source: ir.BlockId,
    clone: ir.BlockId,
    group: ir.NodeSplitGroupId,
    arguments: []const ir.ValueId,
) NormalizeError!?[]ir.ValueId {
    var replay = (try node_split.replayMappingsForCloneAlloc(
        allocator,
        program,
        source,
        clone,
        group,
    )) orelse return null;
    defer replay.deinit();

    const mapped = try allocator.alloc(ir.ValueId, arguments.len);
    errdefer allocator.free(mapped);
    for (arguments, 0..) |argument, argument_index| {
        switch (node_split.reverseReplayValue(replay, argument)) {
            .mapped => |source_value| {
                mapped[argument_index] = source_value;
                continue;
            },
            .ambiguous => return null,
            .missing => {},
        }
        if (argument.index() >= program.values.len) return null;
        const value = program.values[argument.index()];
        if (value.id != argument) return null;
        switch (value.origin) {
            .parameter, .capture => {},
            .block_parameter => |origin| if (origin.block == clone) return null,
            .instruction_result => |origin| {
                if (origin.instruction.index() >= program.instructions.len) return null;
                if (program.instructions[origin.instruction.index()].block == clone) return null;
            },
        }
        mapped[argument_index] = argument;
    }
    return mapped;
}

// A paired clone can reproduce a collision edge inside the very closure that
// was cloned to resolve it.  Splitting that edge again is self-replicating:
// the next clone contains the same edge with fresh block/value ids.  Replay
// the edge back to its authenticated owner boundary instead.  The source
// lineage maps the complete argument tuple; target-only lineage steps use
// the original rewrite tuple.  No reachability or root equality is enough
// to enter this path.
fn collapsePairedCollisionEdge(
    allocator: std.mem.Allocator,
    program: *ir.Program,
    blocks: *std.ArrayList(ir.Block),
    rewrites: *std.ArrayList(ir.CfgEdgeRewrite),
    owner: CollisionArm,
    candidate: CollisionArm,
    projection: *const structural_overlap.ReplayProjectionContext,
) NormalizeError!bool {
    if (!sameNodeSplitPairedArmLineageForwardWithReplay(
        program,
        projection,
        owner,
        candidate,
    )) return false;
    if (candidate.source.index() >= blocks.items.len or
        candidate.target.index() >= blocks.items.len or
        owner.target.index() >= blocks.items.len or
        blocks.items[candidate.source.index()].id != candidate.source or
        blocks.items[candidate.target.index()].id != candidate.target or
        blocks.items[owner.target.index()].id != owner.target or
        blocks.items[candidate.source.index()].function != blocks.items[owner.target.index()].function)
    {
        return false;
    }
    if (isHistoricalForwardingTarget(rewrites.items, owner.target)) return false;

    const reference: ir.CfgEdgeRef = .{
        .source = candidate.source,
        .kind = candidate.kind,
        .target = candidate.target,
    };
    const live = cfg_edge.value(program, reference) orelse return false;
    if (live.target != candidate.target or
        live.arguments.len != blocks.items[candidate.target.index()].parameters.len)
    {
        return false;
    }

    // Keep the candidate-local tuple used by the live edge. A second tuple is
    // replayed back into the owner source to authenticate that this edge is
    // the same semantic arm; that historical tuple may not dominate the
    // cloned source and must not be written back into the live CFG.
    const projected = try allocator.dupe(ir.ValueId, live.arguments);
    var projected_owned = true;
    defer if (projected_owned) allocator.free(projected);
    var owner_projected = try allocator.dupe(ir.ValueId, live.arguments);
    defer allocator.free(owner_projected);

    var current_source = candidate.source;
    var current_target = candidate.target;
    var steps: usize = 0;
    var paired_steps: usize = 0;
    while (current_source != owner.source or current_target != owner.target) : (steps += 1) {
        if (steps >= blocks.items.len) return false;

        const source_parent = projection.cloneLineageParent(current_source);
        const target_parent = projection.cloneLineageParent(current_target);
        if (source_parent) |source_step| {
            if (target_parent) |target_step| {
                if (source_step.group == target_step.group) {
                    const rewrite = findNodeSplitArmEdgeInGroup(
                        rewrites.items,
                        current_source,
                        candidate.kind,
                        target_step.block,
                        current_target,
                        source_step.group,
                    ) orelse return false;
                    if (steps == 0 and !std.mem.eql(ir.ValueId, live.arguments, rewrite.to.arguments)) {
                        return false;
                    }
                    const next_projected = (try mapEdgeArgumentsBackwardThroughClone(
                        allocator,
                        program,
                        source_step.block,
                        current_source,
                        source_step.group,
                        owner_projected,
                    )) orelse return false;
                    allocator.free(owner_projected);
                    owner_projected = next_projected;
                    current_source = source_step.block;
                    current_target = target_step.block;
                    paired_steps += 1;
                    continue;
                }
            }
        }

        const target_step = target_parent orelse return false;
        const rewrite = findNodeSplitArmEdge(
            rewrites.items,
            current_source,
            candidate.kind,
            target_step.block,
            current_target,
        ) orelse return false;
        if (steps == 0 and !std.mem.eql(ir.ValueId, live.arguments, rewrite.to.arguments)) {
            return false;
        }
        const next_projected = try allocator.dupe(ir.ValueId, rewrite.from.arguments);
        allocator.free(owner_projected);
        owner_projected = next_projected;
        current_target = target_step.block;
    }
    if (paired_steps == 0 or
        projected.len != blocks.items[owner.target.index()].parameters.len or
        owner_projected.len != blocks.items[owner.target.index()].parameters.len)
    {
        return false;
    }
    for (owner_projected) |value_id| {
        if (value_id.index() >= program.values.len or program.values[value_id.index()].id != value_id) {
            return false;
        }
    }
    const owner_edge = cfg_edge.value(program, .{
        .source = owner.source,
        .kind = owner.kind,
        .target = owner.target,
    }) orelse return false;
    if (owner_edge.target != owner.target or
        !std.mem.eql(ir.ValueId, owner_projected, owner_edge.arguments)) return false;

    const from_arguments = try allocator.dupe(ir.ValueId, live.arguments);
    errdefer allocator.free(from_arguments);
    if (!(try redirectEdgeWithDominancePreflight(
        allocator,
        program,
        blocks.items,
        blocks.items[candidate.source.index()].function,
        &blocks.items[candidate.source.index()],
        reference,
        owner.target,
        projected,
    ))) {
        return false;
    }
    try rewrites.append(allocator, .{
        .id = ir.EdgeRewriteId.fromIndex(rewrites.items.len),
        .source = candidate.source,
        .kind = candidate.kind,
        .from = .{ .target = candidate.target, .arguments = from_arguments },
        .to = .{ .target = owner.target, .arguments = projected },
        .rule = .forwarding_jump,
    });
    projected_owned = false;
    program.blocks = blocks.items;
    program.edge_rewrites = rewrites.items;
    traceNormalize("normalize_phase paired_replay_fold source={} from={} to={} paired_steps={} arguments={any}\n", .{
        candidate.source.index(),
        candidate.target.index(),
        owner.target.index(),
        paired_steps,
        projected,
    });
    return true;
}

// Independently composed source and target clones can reproduce an owner arm
// without sharing a node-split group.  When the owner-composed bridge proves
// the complete external tuple, fold the live edge back to the durable owner
// target instead of cloning the same continuation again.  The bridge proof
// authenticates both endpoint lineages, the target rewrite, and the mapped
// value/formal tuple; this fold only records that already-proven projection.
fn collapseOwnerComposedCollisionEdge(
    allocator: std.mem.Allocator,
    program: *ir.Program,
    blocks: *std.ArrayList(ir.Block),
    rewrites: *std.ArrayList(ir.CfgEdgeRewrite),
    analysis: *const cfg.Analysis,
    owner: CollisionArm,
    candidate: CollisionArm,
    projection: *structural_overlap.ReplayProjectionContext,
) NormalizeError!bool {
    if (!try sameNodeSplitOwnerComposedArmLineageWithReplay(
        program,
        analysis,
        projection,
        owner,
        candidate,
    )) return false;

    const source_parent = projection.cloneLineageParent(candidate.source) orelse return false;
    const target_parent = projection.cloneLineageParent(candidate.target) orelse return false;
    if (source_parent.block != owner.source or target_parent.block != owner.target or
        source_parent.group == target_parent.group)
    {
        return false;
    }
    if (owner.target.index() >= blocks.items.len or
        candidate.source.index() >= blocks.items.len or
        candidate.target.index() >= blocks.items.len or
        blocks.items[owner.target.index()].id != owner.target or
        blocks.items[candidate.source.index()].id != candidate.source or
        blocks.items[candidate.target.index()].id != candidate.target or
        blocks.items[candidate.source.index()].function != blocks.items[owner.target.index()].function or
        blocks.items[candidate.target.index()].function != blocks.items[owner.target.index()].function)
    {
        return false;
    }
    if (isHistoricalForwardingTarget(rewrites.items, owner.target)) return false;

    const reference: ir.CfgEdgeRef = .{
        .source = candidate.source,
        .kind = candidate.kind,
        .target = candidate.target,
    };
    const live = cfg_edge.value(program, reference) orelse return false;
    if (live.target != candidate.target or
        live.arguments.len != blocks.items[candidate.target.index()].parameters.len)
    {
        return false;
    }

    // The target-side rewrite is the durable owner boundary. Require the
    // exact group and edge tuple rather than reconstructing it from roots.
    const target_rewrite = findNodeSplitArmEdgeInGroup(
        rewrites.items,
        candidate.source,
        candidate.kind,
        owner.target,
        candidate.target,
        target_parent.group,
    ) orelse findNodeSplitArmEdgeInGroup(
        rewrites.items,
        owner.source,
        candidate.kind,
        owner.target,
        candidate.target,
        target_parent.group,
    ) orelse return false;
    if (!std.mem.eql(ir.ValueId, live.arguments, target_rewrite.to.arguments) or
        target_rewrite.from.arguments.len != blocks.items[owner.target.index()].parameters.len)
    {
        return false;
    }

    const from_arguments = try allocator.dupe(ir.ValueId, live.arguments);
    errdefer allocator.free(from_arguments);
    const to_arguments = try allocator.dupe(ir.ValueId, target_rewrite.from.arguments);
    errdefer allocator.free(to_arguments);
    if (!(try redirectEdgeWithDominancePreflight(
        allocator,
        program,
        blocks.items,
        analysis.function.id,
        &blocks.items[candidate.source.index()],
        reference,
        owner.target,
        to_arguments,
    ))) {
        allocator.free(from_arguments);
        allocator.free(to_arguments);
        return false;
    }
    try rewrites.append(allocator, .{
        .id = ir.EdgeRewriteId.fromIndex(rewrites.items.len),
        .source = candidate.source,
        .kind = candidate.kind,
        .from = .{ .target = candidate.target, .arguments = from_arguments },
        .to = .{ .target = owner.target, .arguments = to_arguments },
        .rule = .clone_fold,
        .node_split_group = target_parent.group,
    });
    program.blocks = blocks.items;
    program.edge_rewrites = rewrites.items;
    traceNormalize("normalize_phase owner_composed_replay_fold source={} from={} to={} arguments={any}\n", .{
        candidate.source.index(),
        candidate.target.index(),
        owner.target.index(),
        to_arguments,
    });
    return true;
}

test "paired collision replay fold preserves an available owner-equivalent tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source_root = ir.BlockId.fromIndex(1);
    const target_root = ir.BlockId.fromIndex(2);
    const source_clone = ir.BlockId.fromIndex(3);
    const target_clone = ir.BlockId.fromIndex(4);
    const input = ir.ValueId.fromIndex(0);
    const source_parameter = ir.ValueId.fromIndex(1);
    const target_parameter = ir.ValueId.fromIndex(2);
    const clone_parameter = ir.ValueId.fromIndex(3);
    const clone_target_parameter = ir.ValueId.fromIndex(4);
    const group = ir.NodeSplitGroupId.fromIndex(7);
    const entry_arguments = [_]ir.ValueId{input};
    const source_arguments = [_]ir.ValueId{source_parameter};
    const clone_arguments = [_]ir.ValueId{clone_parameter};
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{
            .target = source_clone,
            .arguments = entry_arguments[0..],
        } } },
        .{ .id = source_root, .function = function_id, .parameters = &.{source_parameter}, .terminator = .{ .jump = .{
            .target = target_root,
            .arguments = source_arguments[0..],
        } } },
        .{ .id = target_root, .function = function_id, .parameters = &.{target_parameter}, .terminator = .{ .return_values = &.{} } },
        .{ .id = source_clone, .function = function_id, .parameters = &.{clone_parameter}, .terminator = .{ .jump = .{
            .target = target_clone,
            .arguments = clone_arguments[0..],
        } } },
        .{ .id = target_clone, .function = function_id, .parameters = &.{clone_target_parameter}, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{input},
        .blocks = &.{ entry, source_root, target_root, source_clone, target_clone },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = input, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = source_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_root, .index = 0 } } },
        .{ .id = target_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_root, .index = 0 } } },
        .{ .id = clone_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_clone, .index = 0 } } },
        .{ .id = clone_target_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_clone, .index = 0 } } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .jump,
            .from = .{ .target = source_root, .arguments = entry_arguments[0..] },
            .to = .{ .target = source_clone, .arguments = entry_arguments[0..] },
            .rule = .node_split,
            .node_split_group = group,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = source_clone,
            .kind = .jump,
            .from = .{ .target = target_root, .arguments = clone_arguments[0..] },
            .to = .{ .target = target_clone, .arguments = clone_arguments[0..] },
            .rule = .node_split,
            .node_split_group = group,
        },
    };
    var blocks_owned: std.ArrayList(ir.Block) = .empty;
    defer blocks_owned.deinit(std.testing.allocator);
    try blocks_owned.appendSlice(std.testing.allocator, &blocks);
    var rewrites_owned: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    defer rewrites_owned.deinit(std.testing.allocator);
    try rewrites_owned.appendSlice(std.testing.allocator, &rewrites);
    var program = ir.Program{
        .program_id = "paired-collision-replay-fold",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = blocks_owned.items,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = rewrites_owned.items,
    };
    var projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer projection.deinit();

    const owner: CollisionArm = .{ .source = source_root, .kind = .jump, .target = target_root };
    const candidate: CollisionArm = .{ .source = source_clone, .kind = .jump, .target = target_clone };
    try std.testing.expect(sameNodeSplitPairedArmLineageForwardWithReplay(
        &program,
        &projection,
        owner,
        candidate,
    ));
    try std.testing.expect(try collapsePairedCollisionEdge(
        std.testing.allocator,
        &program,
        &blocks_owned,
        &rewrites_owned,
        owner,
        candidate,
        &projection,
    ));
    defer std.testing.allocator.free(program.edge_rewrites[2].from.arguments);
    defer std.testing.allocator.free(program.edge_rewrites[2].to.arguments);
    try std.testing.expectEqual(target_root, program.blocks[source_clone.index()].terminator.jump.target);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        clone_arguments[0..],
        program.blocks[source_clone.index()].terminator.jump.arguments,
    );
    try std.testing.expectEqual(@as(usize, 3), program.edge_rewrites.len);
    try std.testing.expectEqual(ir.EdgeRewriteRule.forwarding_jump, program.edge_rewrites[2].rule);
    try std.testing.expectEqual(target_clone, program.edge_rewrites[2].from.target);
    try std.testing.expectEqual(target_root, program.edge_rewrites[2].to.target);
    try std.testing.expectEqualSlices(ir.ValueId, clone_arguments[0..], program.edge_rewrites[2].to.arguments);
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

test "owner-composed collision arm replays a complete external tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source_root = ir.BlockId.fromIndex(1);
    const target_root = ir.BlockId.fromIndex(2);
    const source_clone = ir.BlockId.fromIndex(3);
    const target_clone = ir.BlockId.fromIndex(4);
    const exit = ir.BlockId.fromIndex(5);
    const foreign = ir.BlockId.fromIndex(6);
    const edge_arguments = [_]ir.ValueId{
        ir.ValueId.fromIndex(1),
        ir.ValueId.fromIndex(2),
        ir.ValueId.fromIndex(3),
        ir.ValueId.fromIndex(4),
        ir.ValueId.fromIndex(5),
        ir.ValueId.fromIndex(6),
        ir.ValueId.fromIndex(7),
        ir.ValueId.fromIndex(8),
    };
    const target_parameters = [_]ir.ValueId{
        ir.ValueId.fromIndex(9),
        ir.ValueId.fromIndex(10),
        ir.ValueId.fromIndex(11),
        ir.ValueId.fromIndex(12),
        ir.ValueId.fromIndex(13),
        ir.ValueId.fromIndex(14),
        ir.ValueId.fromIndex(15),
        ir.ValueId.fromIndex(16),
    };
    const target_clone_parameters = [_]ir.ValueId{
        ir.ValueId.fromIndex(17),
        ir.ValueId.fromIndex(18),
        ir.ValueId.fromIndex(19),
        ir.ValueId.fromIndex(20),
        ir.ValueId.fromIndex(21),
        ir.ValueId.fromIndex(22),
        ir.ValueId.fromIndex(23),
        ir.ValueId.fromIndex(24),
    };
    const source_group = ir.NodeSplitGroupId.fromIndex(10);
    const target_group = ir.NodeSplitGroupId.fromIndex(20);
    const forged_group = ir.NodeSplitGroupId.fromIndex(30);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = source_root },
            .else_edge = .{ .target = source_clone },
        } } },
        .{ .id = source_root, .function = function_id, .terminator = .{ .jump = .{ .target = target_clone, .arguments = edge_arguments[0..] } } },
        .{ .id = target_root, .function = function_id, .parameters = target_parameters[0..], .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = source_clone, .function = function_id, .terminator = .{ .jump = .{ .target = target_clone, .arguments = edge_arguments[0..] } } },
        .{ .id = target_clone, .function = function_id, .parameters = target_clone_parameters[0..], .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = foreign, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const condition = ir.ValueId.fromIndex(0);
    const function_parameters = [_]ir.ValueId{
        condition,
        edge_arguments[0],
        edge_arguments[1],
        edge_arguments[2],
        edge_arguments[3],
        edge_arguments[4],
        edge_arguments[5],
        edge_arguments[6],
        edge_arguments[7],
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }} ++ [_]ir.Value{
        .{ .id = edge_arguments[0], .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = edge_arguments[1], .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = edge_arguments[2], .function = function_id, .type = .integer, .origin = .{ .parameter = 3 } },
        .{ .id = edge_arguments[3], .function = function_id, .type = .integer, .origin = .{ .parameter = 4 } },
        .{ .id = edge_arguments[4], .function = function_id, .type = .integer, .origin = .{ .parameter = 5 } },
        .{ .id = edge_arguments[5], .function = function_id, .type = .integer, .origin = .{ .parameter = 6 } },
        .{ .id = edge_arguments[6], .function = function_id, .type = .integer, .origin = .{ .parameter = 7 } },
        .{ .id = edge_arguments[7], .function = function_id, .type = .integer, .origin = .{ .parameter = 8 } },
        .{ .id = target_parameters[0], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_root, .index = 0 } } },
        .{ .id = target_parameters[1], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_root, .index = 1 } } },
        .{ .id = target_parameters[2], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_root, .index = 2 } } },
        .{ .id = target_parameters[3], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_root, .index = 3 } } },
        .{ .id = target_parameters[4], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_root, .index = 4 } } },
        .{ .id = target_parameters[5], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_root, .index = 5 } } },
        .{ .id = target_parameters[6], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_root, .index = 6 } } },
        .{ .id = target_parameters[7], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_root, .index = 7 } } },
        .{ .id = target_clone_parameters[0], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_clone, .index = 0 } } },
        .{ .id = target_clone_parameters[1], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_clone, .index = 1 } } },
        .{ .id = target_clone_parameters[2], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_clone, .index = 2 } } },
        .{ .id = target_clone_parameters[3], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_clone, .index = 3 } } },
        .{ .id = target_clone_parameters[4], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_clone, .index = 4 } } },
        .{ .id = target_clone_parameters[5], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_clone, .index = 5 } } },
        .{ .id = target_clone_parameters[6], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_clone, .index = 6 } } },
        .{ .id = target_clone_parameters[7], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_clone, .index = 7 } } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = function_parameters[0..],
        .blocks = &.{ entry, source_root, target_root, source_clone, target_clone, exit, foreign },
        .entry_block = entry,
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .branch_else,
            .from = .{ .target = source_root },
            .to = .{ .target = source_clone },
            .rule = .node_split,
            .node_split_group = source_group,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = source_root,
            .kind = .jump,
            .from = .{ .target = target_root, .arguments = edge_arguments[0..] },
            .to = .{ .target = target_clone, .arguments = edge_arguments[0..] },
            .rule = .node_split,
            .node_split_group = target_group,
        },
    };
    const program = ir.Program{
        .program_id = "owner-composed-collision-arm",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer projection.deinit();

    const owner: CollisionArm = .{ .source = source_root, .kind = .jump, .target = target_root };
    const candidate: CollisionArm = .{ .source = source_clone, .kind = .jump, .target = target_clone };
    const historical_owner = historicalOwnerComposedArmForCandidate(
        &program,
        candidate,
        &projection,
    ).?;
    try std.testing.expectEqual(owner.source, historical_owner.source);
    try std.testing.expectEqual(owner.kind, historical_owner.kind);
    try std.testing.expectEqual(owner.target, historical_owner.target);
    try std.testing.expect(!sameCollisionArmPositionWithReplay(&projection, owner, candidate));
    try std.testing.expect(try sameNodeSplitOwnerComposedArmLineageWithReplay(
        &program,
        &analysis,
        &projection,
        owner,
        candidate,
    ));

    var collapsed_blocks: std.ArrayList(ir.Block) = .empty;
    defer collapsed_blocks.deinit(std.testing.allocator);
    try collapsed_blocks.appendSlice(std.testing.allocator, &blocks);
    var collapsed_rewrites: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    defer collapsed_rewrites.deinit(std.testing.allocator);
    try collapsed_rewrites.appendSlice(std.testing.allocator, &rewrites);
    var collapsed_program = program;
    collapsed_program.blocks = collapsed_blocks.items;
    collapsed_program.edge_rewrites = collapsed_rewrites.items;
    var collapsed_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &collapsed_program,
        function,
    );
    defer collapsed_analysis.deinit();
    var collapsed_projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &collapsed_program,
    );
    defer collapsed_projection.deinit();
    try std.testing.expect(try collapseOwnerComposedCollisionEdge(
        std.testing.allocator,
        &collapsed_program,
        &collapsed_blocks,
        &collapsed_rewrites,
        &collapsed_analysis,
        owner,
        candidate,
        &collapsed_projection,
    ));
    defer std.testing.allocator.free(collapsed_program.edge_rewrites[2].from.arguments);
    defer std.testing.allocator.free(collapsed_program.edge_rewrites[2].to.arguments);
    try std.testing.expectEqual(target_root, collapsed_program.blocks[source_clone.index()].terminator.jump.target);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        edge_arguments[0..],
        collapsed_program.blocks[source_clone.index()].terminator.jump.arguments,
    );
    try std.testing.expectEqual(@as(usize, 3), collapsed_program.edge_rewrites.len);
    try std.testing.expectEqual(target_clone, collapsed_program.edge_rewrites[2].from.target);
    try std.testing.expectEqual(target_root, collapsed_program.edge_rewrites[2].to.target);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        edge_arguments[0..],
        collapsed_program.edge_rewrites[2].to.arguments,
    );

    var direct_boundary = (try findOwnerComposedDirectBridgeAlternativeWithAnalysis(
        std.testing.allocator,
        &program,
        &analysis,
        0,
        owner,
        candidate,
        &.{},
        &projection,
    )).?;
    defer direct_boundary.deinit();
    try std.testing.expectEqual(@as(usize, 1), direct_boundary.incoming.len);
    try std.testing.expectEqual(source_root, direct_boundary.incoming[0].source);
    try std.testing.expectEqual(target_clone, direct_boundary.incoming[0].target);

    const direct_owner: CollisionArm = .{
        .source = source_root,
        .kind = .jump,
        .target = target_root,
    };
    const direct_candidate: CollisionArm = .{
        .source = source_root,
        .kind = .jump,
        .target = target_clone,
    };
    var direct_target_boundary = (try findDirectTargetBridgeAlternativeWithAnalysis(
        std.testing.allocator,
        &program,
        &analysis,
        0,
        direct_owner,
        direct_candidate,
        &.{},
        &projection,
    )).?;
    defer direct_target_boundary.deinit();
    try std.testing.expectEqual(@as(usize, 1), direct_target_boundary.incoming.len);
    try std.testing.expectEqual(source_root, direct_target_boundary.incoming[0].source);
    try std.testing.expectEqual(target_clone, direct_target_boundary.incoming[0].target);
    try std.testing.expect((try findDirectTargetBridgeAlternativeWithAnalysis(
        std.testing.allocator,
        &program,
        &analysis,
        0,
        direct_owner,
        direct_candidate,
        &.{ direct_owner, direct_candidate },
        &projection,
    )) == null);

    const direct_boundary_arm: CollisionArm = .{
        .source = source_root,
        .kind = .jump,
        .target = target_clone,
    };
    try std.testing.expect((try findOwnerComposedDirectBridgeAlternativeWithAnalysis(
        std.testing.allocator,
        &program,
        &analysis,
        0,
        owner,
        candidate,
        &.{ owner, direct_boundary_arm },
        &projection,
    )) == null);

    var paired_rewrites = [_]ir.CfgEdgeRewrite{
        rewrites[0],
        rewrites[1],
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = source_clone,
            .kind = .jump,
            .from = .{ .target = target_root, .arguments = edge_arguments[0..] },
            .to = .{ .target = target_clone, .arguments = edge_arguments[0..] },
            .rule = .node_split,
            .node_split_group = source_group,
        },
    };
    paired_rewrites[1].node_split_group = source_group;
    var paired_program = program;
    paired_program.edge_rewrites = &paired_rewrites;
    var paired_analysis = try cfg.Analysis.init(std.testing.allocator, &paired_program, function);
    defer paired_analysis.deinit();
    var paired_projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &paired_program,
    );
    defer paired_projection.deinit();
    try std.testing.expect(sameNodeSplitPairedArmLineageWithReplay(
        &paired_program,
        &paired_projection,
        owner,
        candidate,
    ));
    try std.testing.expect((try findOwnerComposedDirectBridgeAlternativeWithAnalysis(
        std.testing.allocator,
        &paired_program,
        &paired_analysis,
        0,
        owner,
        candidate,
        &.{},
        &paired_projection,
    )) == null);

    var tampered_blocks = blocks;
    var tampered_arguments = edge_arguments;
    tampered_arguments[7] = target_clone_parameters[7];
    tampered_blocks[source_clone.index()].terminator = .{ .jump = .{
        .target = target_clone,
        .arguments = tampered_arguments[0..],
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &tampered_program,
    );
    defer tampered_projection.deinit();
    try std.testing.expect(!(try sameNodeSplitOwnerComposedArmLineageWithReplay(
        &tampered_program,
        &analysis,
        &tampered_projection,
        owner,
        candidate,
    )));

    const prior = [_]CollisionArm{owner};
    try std.testing.expect((try findPreviouslyTriedCollisionArmWithAnalysis(
        &program,
        &analysis,
        &prior,
        candidate,
        &projection,
    )) != null);
    const repeated_split = structural_overlap.Split{
        .allocator = std.testing.allocator,
        .function_index = 0,
        .branch = source_clone,
        .entry = target_clone,
        .join = target_clone,
        .incoming = try std.testing.allocator.dupe(ir.CfgEdgeRef, &.{.{
            .source = candidate.source,
            .kind = candidate.kind,
            .target = candidate.target,
        }}),
        .closure = try std.testing.allocator.dupe(ir.BlockId, &.{target_clone}),
    };
    try std.testing.expect((try freshCollisionAlternativeWithAnalysis(
        &program,
        &analysis,
        repeated_split,
        &prior,
        &projection,
        null,
    )) == null);

    var wrong_parent_rewrites = rewrites;
    wrong_parent_rewrites[0].from.target = foreign;
    var wrong_parent_program = program;
    wrong_parent_program.edge_rewrites = &wrong_parent_rewrites;
    var wrong_parent_projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &wrong_parent_program,
    );
    defer wrong_parent_projection.deinit();
    try std.testing.expect(!(try sameNodeSplitOwnerComposedArmLineageWithReplay(
        &wrong_parent_program,
        &analysis,
        &wrong_parent_projection,
        owner,
        candidate,
    )));

    var forged_group_rewrites = [_]ir.CfgEdgeRewrite{
        rewrites[0],
        rewrites[1],
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = foreign,
            .kind = .jump,
            .from = .{ .target = foreign },
            .to = .{ .target = target_clone },
            .rule = .node_split,
            .node_split_group = forged_group,
        },
    };
    var forged_group_program = program;
    forged_group_program.edge_rewrites = &forged_group_rewrites;
    var forged_group_projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &forged_group_program,
    );
    defer forged_group_projection.deinit();
    try std.testing.expect(!(try sameNodeSplitOwnerComposedArmLineageWithReplay(
        &forged_group_program,
        &analysis,
        &forged_group_projection,
        owner,
        candidate,
    )));
}

test "authenticated transparent direct target forwards with history" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const target_clone = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = target_clone } } },
        .{ .id = target, .function = function_id, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = target_clone, .function = function_id, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, source, target, target_clone, exit },
        .entry_block = entry,
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = source,
            .kind = .jump,
            .from = .{ .target = target },
            .to = .{ .target = target_clone },
            .rule = .node_split,
            .node_split_group = group,
        },
    };
    var blocks_owned: std.ArrayList(ir.Block) = .empty;
    defer blocks_owned.deinit(std.testing.allocator);
    try blocks_owned.appendSlice(std.testing.allocator, &blocks);
    var rewrites_owned: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    defer rewrites_owned.deinit(std.testing.allocator);
    try rewrites_owned.appendSlice(std.testing.allocator, &rewrites);
    var program = ir.Program{
        .program_id = "authenticated-transparent-direct-target",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = blocks_owned.items,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = rewrites_owned.items,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer projection.deinit();

    const owner: CollisionArm = .{ .source = source, .kind = .jump, .target = target };
    const candidate: CollisionArm = .{ .source = source, .kind = .jump, .target = target_clone };
    try std.testing.expect(try directTargetBridgeIsAuthenticated(
        &analysis,
        owner,
        candidate,
        &projection,
    ));
    try std.testing.expect(try collapseAuthenticatedTransparentCollisionEdge(
        std.testing.allocator,
        &program,
        &blocks_owned,
        &rewrites_owned,
        &analysis,
        0,
        owner,
        candidate,
        &projection,
    ));
    try std.testing.expectEqual(exit, program.blocks[source.index()].terminator.jump.target);
    try std.testing.expectEqual(@as(usize, 2), program.edge_rewrites.len);
    try std.testing.expectEqual(ir.EdgeRewriteRule.forwarding_jump, program.edge_rewrites[1].rule);
    try std.testing.expectEqual(target_clone, program.edge_rewrites[1].from.target);
    try std.testing.expectEqual(exit, program.edge_rewrites[1].to.target);
}

test "authenticated transparent forwarding preserves parameterized successor tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const target_clone = ir.BlockId.fromIndex(3);
    const successor = ir.BlockId.fromIndex(4);
    const input = ir.ValueId.fromIndex(0);
    const formal = ir.ValueId.fromIndex(1);
    const group = ir.NodeSplitGroupId.fromIndex(0);
    var successor_arguments = [_]ir.ValueId{input};
    const values = [_]ir.Value{
        .{
            .id = input,
            .function = function_id,
            .type = .integer,
            .origin = .{ .parameter = 0 },
        },
        .{
            .id = formal,
            .function = function_id,
            .type = .integer,
            .origin = .{ .block_parameter = .{ .block = successor, .index = 0 } },
        },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = target_clone } } },
        .{ .id = target, .function = function_id, .terminator = .{ .jump = .{
            .target = successor,
            .arguments = successor_arguments[0..],
        } } },
        .{ .id = target_clone, .function = function_id, .terminator = .{ .jump = .{
            .target = successor,
            .arguments = successor_arguments[0..],
        } } },
        .{
            .id = successor,
            .function = function_id,
            .parameters = &.{formal},
            .terminator = .{ .return_values = &.{formal} },
        },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{input},
        .blocks = &.{ entry, source, target, target_clone, successor },
        .entry_block = entry,
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = source,
            .kind = .jump,
            .from = .{ .target = target },
            .to = .{ .target = target_clone },
            .rule = .node_split,
            .node_split_group = group,
        },
    };
    var blocks_owned: std.ArrayList(ir.Block) = .empty;
    defer blocks_owned.deinit(std.testing.allocator);
    try blocks_owned.appendSlice(std.testing.allocator, &blocks);
    var rewrites_owned: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    defer rewrites_owned.deinit(std.testing.allocator);
    try rewrites_owned.appendSlice(std.testing.allocator, &rewrites);
    var program = ir.Program{
        .program_id = "authenticated-transparent-parameterized-successor",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = blocks_owned.items,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = rewrites_owned.items,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer projection.deinit();

    const owner: CollisionArm = .{ .source = source, .kind = .jump, .target = target };
    const candidate: CollisionArm = .{ .source = source, .kind = .jump, .target = target_clone };
    try std.testing.expect(try collapseAuthenticatedTransparentCollisionEdge(
        std.testing.allocator,
        &program,
        &blocks_owned,
        &rewrites_owned,
        &analysis,
        0,
        owner,
        candidate,
        &projection,
    ));
    try std.testing.expectEqual(successor, program.blocks[source.index()].terminator.jump.target);
    try std.testing.expectEqual(@as(usize, 2), program.edge_rewrites.len);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        successor_arguments[0..],
        program.edge_rewrites[1].to.arguments,
    );
}

test "post-apply transparent collapse preserves canonical successor tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const forwarder = ir.BlockId.fromIndex(1);
    const successor = ir.BlockId.fromIndex(2);
    const input = ir.ValueId.fromIndex(0);
    const formal = ir.ValueId.fromIndex(1);
    const successor_arguments = [_]ir.ValueId{input};
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = forwarder } } },
        .{ .id = forwarder, .function = function_id, .terminator = .{ .jump = .{
            .target = successor,
            .arguments = successor_arguments[0..],
        } } },
        .{ .id = successor, .function = function_id, .parameters = &.{formal}, .terminator = .{ .return_values = &.{formal} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{input},
        .blocks = &.{ entry, forwarder, successor },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = input, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = formal, .function = function_id, .origin = .{ .block_parameter = .{ .block = successor, .index = 0 } } },
    };
    var blocks_owned: std.ArrayList(ir.Block) = .empty;
    defer blocks_owned.deinit(std.testing.allocator);
    try blocks_owned.appendSlice(std.testing.allocator, &blocks);
    var rewrites: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    defer rewrites.deinit(std.testing.allocator);
    var program = ir.Program{
        .program_id = "post-apply-transparent-collapse",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = blocks_owned.items,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = rewrites.items,
    };

    try std.testing.expectEqual(@as(usize, 1), try collapseTransparentForwardingBlocks(
        std.testing.allocator,
        &program,
        &blocks_owned,
        &rewrites,
        0,
    ));
    try std.testing.expectEqual(successor, program.blocks[entry.index()].terminator.jump.target);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        successor_arguments[0..],
        program.blocks[entry.index()].terminator.jump.arguments,
    );
    try std.testing.expectEqual(@as(usize, 1), rewrites.items.len);
    try std.testing.expectEqual(forwarder, rewrites.items[0].from.target);
    try std.testing.expectEqual(successor, rewrites.items[0].to.target);
    try std.testing.expectEqualSlices(ir.ValueId, successor_arguments[0..], rewrites.items[0].to.arguments);

    program.blocks = blocks_owned.items;
    program.edge_rewrites = rewrites.items;
    try std.testing.expectEqual(@as(usize, 0), try collapseTransparentForwardingBlocks(
        std.testing.allocator,
        &program,
        &blocks_owned,
        &rewrites,
        0,
    ));
}

test "transparent collapse refuses a non-local successor tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const foreign = ir.BlockId.fromIndex(2);
    const forwarder = ir.BlockId.fromIndex(3);
    const successor = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const foreign_value = ir.ValueId.fromIndex(1);
    const source_result = ir.ValueId.fromIndex(2);
    const successor_parameter = ir.ValueId.fromIndex(3);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const successor_arguments = [_]ir.ValueId{foreign_value};
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = source },
            .else_edge = .{ .target = foreign },
        } } },
        .{ .id = source, .function = function_id, .instructions = &.{instruction_id}, .terminator = .{ .jump = .{ .target = forwarder } } },
        .{ .id = foreign, .function = function_id, .parameters = &.{foreign_value}, .terminator = .{ .jump = .{
            .target = successor,
            .arguments = successor_arguments[0..],
        } } },
        .{ .id = forwarder, .function = function_id, .terminator = .{ .jump = .{
            .target = successor,
            .arguments = successor_arguments[0..],
        } } },
        .{ .id = successor, .function = function_id, .parameters = &.{successor_parameter}, .terminator = .{ .return_values = &.{successor_parameter} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, source, foreign, forwarder, successor },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = foreign_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = foreign, .index = 0 } } },
        .{ .id = source_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } } },
        .{ .id = successor_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = successor, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = instruction_id, .block = source, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{source_result}, .effects = .pure },
    };
    const program = ir.Program{
        .program_id = "non-local-forwarding-tuple",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var block_list: std.ArrayList(ir.Block) = .empty;
    defer block_list.deinit(std.testing.allocator);
    try block_list.appendSlice(std.testing.allocator, &blocks);
    var rewrite_list: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    defer rewrite_list.deinit(std.testing.allocator);
    var working_program = program;
    working_program.blocks = block_list.items;
    working_program.edge_rewrites = rewrite_list.items;

    try std.testing.expectEqual(@as(usize, 0), try collapseTransparentForwardingBlocks(
        std.testing.allocator,
        &working_program,
        &block_list,
        &rewrite_list,
        0,
    ));
    try std.testing.expectEqual(forwarder, block_list.items[source.index()].terminator.jump.target);
    try std.testing.expectEqual(@as(usize, 0), rewrite_list.items.len);
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

test "collision arm identity includes the rewritten destination" {
    const source = ir.BlockId.fromIndex(7);
    const first_target = ir.BlockId.fromIndex(11);
    const second_target = ir.BlockId.fromIndex(13);
    const arm: CollisionArm = .{ .source = source, .kind = .branch_then, .target = first_target };
    const arms = [_]CollisionArm{arm};

    try std.testing.expect(findCollisionArm(&arms, arm) != null);
    try std.testing.expect(findCollisionArm(&arms, .{
        .source = source,
        .kind = .branch_then,
        .target = second_target,
    }) == null);
}

test "lineage collision distinguishes nested continuation groups" {
    const source_root = ir.BlockId.fromIndex(0);
    const target_root = ir.BlockId.fromIndex(1);
    const source_clone = ir.BlockId.fromIndex(2);
    const first_target = ir.BlockId.fromIndex(3);
    const nested_target = ir.BlockId.fromIndex(4);
    const same_level_target = ir.BlockId.fromIndex(5);
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = source_root,
            .kind = .jump,
            .from = .{ .target = source_root },
            .to = .{ .target = source_clone },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(10),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = target_root,
            .kind = .jump,
            .from = .{ .target = target_root },
            .to = .{ .target = first_target },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(20),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = first_target,
            .kind = .jump,
            .from = .{ .target = first_target },
            .to = .{ .target = nested_target },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(30),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(3),
            .source = target_root,
            .kind = .jump,
            .from = .{ .target = target_root },
            .to = .{ .target = same_level_target },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(20),
        },
    };
    const prior = [_]CollisionArm{.{
        .source = source_clone,
        .kind = .jump,
        .target = first_target,
    }};

    try std.testing.expect(findLineageCollisionArm(
        &rewrites,
        &prior,
        .{ .source = source_clone, .kind = .jump, .target = nested_target },
    ) == null);
    try std.testing.expect(findLineageCollisionArm(
        &rewrites,
        &prior,
        .{ .source = source_clone, .kind = .jump, .target = same_level_target },
    ) != null);

    try std.testing.expect(!sameCollisionArmPosition(
        &rewrites,
        .{ .source = source_clone, .kind = .jump, .target = first_target },
        .{ .source = source_clone, .kind = .jump, .target = nested_target },
    ));
    try std.testing.expect(sameCollisionArmPosition(
        &rewrites,
        .{ .source = source_clone, .kind = .jump, .target = first_target },
        .{ .source = source_clone, .kind = .jump, .target = same_level_target },
    ));
}

test "same-source adjacent clone lineage is one collision arm" {
    const source = ir.BlockId.fromIndex(0);
    const root = ir.BlockId.fromIndex(1);
    const first = ir.BlockId.fromIndex(2);
    const second = ir.BlockId.fromIndex(3);
    const foreign = ir.BlockId.fromIndex(4);
    const foreign_nested = ir.BlockId.fromIndex(5);
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = source,
            .kind = .jump,
            .from = .{ .target = root },
            .to = .{ .target = first },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(10),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = source,
            .kind = .jump,
            .from = .{ .target = first },
            .to = .{ .target = second },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(11),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = foreign,
            .kind = .jump,
            .from = .{ .target = root },
            .to = .{ .target = foreign },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(12),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(3),
            .source = foreign,
            .kind = .jump,
            .from = .{ .target = foreign },
            .to = .{ .target = foreign_nested },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(13),
        },
        // Multiple incoming sources may share a node-split group. They must
        // not make the exact source-owned adjacent edge unverifiable.
        .{
            .id = ir.EdgeRewriteId.fromIndex(4),
            .source = foreign,
            .kind = .jump,
            .from = .{ .target = root },
            .to = .{ .target = first },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(10),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(5),
            .source = foreign,
            .kind = .jump,
            .from = .{ .target = first },
            .to = .{ .target = second },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(11),
        },
    };

    try std.testing.expect(sameCollisionArmPosition(
        &rewrites,
        .{ .source = source, .kind = .jump, .target = first },
        .{ .source = source, .kind = .jump, .target = second },
    ));
    try std.testing.expect(!sameCollisionArmPosition(
        &rewrites,
        .{ .source = foreign, .kind = .jump, .target = first },
        .{ .source = foreign, .kind = .jump, .target = foreign_nested },
    ));
}

test "cross-source adjacent lineage requires authenticated collision context" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const first = ir.BlockId.fromIndex(1);
    const second = ir.BlockId.fromIndex(2);
    const foreign = ir.BlockId.fromIndex(3);
    const blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = first } } },
        .{ .id = first, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = second, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = foreign, .function = function_id, .terminator = .{ .jump = .{ .target = second } } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ source, first, second, foreign },
        .entry_block = source,
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = foreign,
            .kind = .jump,
            .from = .{ .target = first },
            .to = .{ .target = second },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(10),
        },
    };
    const program = ir.Program{
        .program_id = "cross-source-adjacent-context",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };
    const prior = [_]CollisionArm{.{
        .source = source,
        .kind = .jump,
        .target = first,
    }};
    var projection = try structural_overlap.ReplayProjectionContext.init(std.testing.allocator, &program);
    defer projection.deinit();

    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &program,
        &prior,
        .{ .source = foreign, .kind = .jump, .target = second },
        &projection,
    )) == null);
}

test "exact arm rewrite survives ambiguous destination lineage" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const first_target = ir.BlockId.fromIndex(1);
    const selected_target = ir.BlockId.fromIndex(2);
    const alternate_target = ir.BlockId.fromIndex(3);
    const foreign_source = ir.BlockId.fromIndex(4);
    const foreign_target = ir.BlockId.fromIndex(5);
    const blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = selected_target } } },
        .{ .id = first_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = selected_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = alternate_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = foreign_source, .function = function_id, .terminator = .{ .jump = .{ .target = foreign_target } } },
        .{ .id = foreign_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ source, first_target, selected_target, alternate_target, foreign_source, foreign_target },
        .entry_block = source,
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = source,
            .kind = .jump,
            .from = .{ .target = first_target },
            .to = .{ .target = selected_target },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = foreign_source,
            .kind = .jump,
            .from = .{ .target = foreign_target },
            .to = .{ .target = selected_target },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(1),
        },
    };
    const program = ir.Program{
        .program_id = "ambiguous-destination-arm-lineage",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };
    const context: structure.CollisionContext = .{
        .start = source,
        .stop = null,
        .loop_exit = null,
        .continue_target = null,
    };
    const prior = [_]CollisionArm{.{
        .source = source,
        .kind = .jump,
        .target = first_target,
        .context = context,
    }};

    var projection = try structural_overlap.ReplayProjectionContext.init(std.testing.allocator, &program);
    defer projection.deinit();
    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &program,
        &prior,
        .{ .source = source, .kind = .jump, .target = selected_target, .context = context },
        &projection,
    )) != null);
    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &program,
        &prior,
        .{ .source = source, .kind = .jump, .target = alternate_target, .context = context },
        &projection,
    )) == null);
}

test "paired cloned source and target lineage is one collision arm" {
    const source = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const cloned_source = ir.BlockId.fromIndex(2);
    const cloned_target = ir.BlockId.fromIndex(3);
    const unrelated_source = ir.BlockId.fromIndex(4);
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = cloned_source,
            .kind = .jump,
            .from = .{ .target = target },
            .to = .{ .target = cloned_target },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(10),
        },
    };

    try std.testing.expect(sameCollisionArmPosition(
        &rewrites,
        .{ .source = source, .kind = .jump, .target = target },
        .{ .source = cloned_source, .kind = .jump, .target = cloned_target },
    ));
    try std.testing.expect(!sameCollisionArmPosition(
        &rewrites,
        .{ .source = source, .kind = .jump, .target = target },
        .{ .source = unrelated_source, .kind = .jump, .target = cloned_target },
    ));
}

test "unauthenticated live clone edge cannot consume a projected collision arm" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const first_clone = ir.BlockId.fromIndex(2);
    const second_clone = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first_clone },
            .else_edge = .{ .target = second_clone },
        } } },
        .{ .id = source, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = first_clone, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = second_clone, .function = function_id, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, source, first_clone, second_clone, exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .branch_then,
            .from = .{ .target = source },
            .to = .{ .target = first_clone },
            .rule = .node_split,
            .node_split_group = group,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = entry,
            .kind = .branch_else,
            .from = .{ .target = source },
            .to = .{ .target = second_clone },
            .rule = .node_split,
            .node_split_group = group,
        },
    };
    const program = ir.Program{
        .program_id = "unauthenticated-live-clone-edge",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    const prior = [_]CollisionArm{.{
        .source = first_clone,
        .kind = .jump,
        .target = exit,
    }};
    const candidate: CollisionArm = .{
        .source = second_clone,
        .kind = .jump,
        .target = exit,
    };
    try std.testing.expect(sameCollisionArmPosition(
        program.edge_rewrites,
        prior[0],
        candidate,
    ));

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var projection = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer projection.deinit();
    try std.testing.expect(!try projection.hasAuthenticatedContinuationBridgeForEdge(
        &analysis,
        .{ .source = second_clone, .kind = .jump, .target = exit },
    ));
    try std.testing.expect((try findPreviouslyTriedCollisionArmWithAnalysis(
        &program,
        &analysis,
        &prior,
        candidate,
        &projection,
    )) == null);
}

test "paired multi-step lineage requires shared groups and a live edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const left_source = ir.BlockId.fromIndex(0);
    const left_target = ir.BlockId.fromIndex(1);
    const first_source = ir.BlockId.fromIndex(2);
    const first_target = ir.BlockId.fromIndex(3);
    const final_source = ir.BlockId.fromIndex(4);
    const final_target = ir.BlockId.fromIndex(5);
    const first_predecessor = ir.BlockId.fromIndex(6);
    const final_predecessor = ir.BlockId.fromIndex(7);
    const unrelated_source = ir.BlockId.fromIndex(8);
    const unrelated_target = ir.BlockId.fromIndex(9);
    const foreign_target = ir.BlockId.fromIndex(10);
    const left_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(0)};
    const first_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(1)};
    const final_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(2)};
    const tampered_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(3)};
    const blocks = [_]ir.Block{
        .{ .id = left_source, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = left_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = first_source, .function = function_id, .terminator = .{ .jump = .{ .target = first_target, .arguments = first_arguments[0..] } } },
        .{ .id = first_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = final_source, .function = function_id, .terminator = .{ .jump = .{ .target = final_target, .arguments = final_arguments[0..] } } },
        .{ .id = final_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = first_predecessor, .function = function_id, .terminator = .{ .jump = .{ .target = first_source } } },
        .{ .id = final_predecessor, .function = function_id, .terminator = .{ .jump = .{ .target = final_source } } },
        .{ .id = unrelated_source, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = unrelated_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = foreign_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ left_source, left_target, first_source, first_target, final_source, final_target, first_predecessor, final_predecessor, unrelated_source, unrelated_target, foreign_target },
        .entry_block = first_predecessor,
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = first_predecessor,
            .kind = .jump,
            .from = .{ .target = left_source },
            .to = .{ .target = first_source },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(10),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = first_source,
            .kind = .jump,
            .from = .{ .target = left_target, .arguments = left_arguments[0..] },
            .to = .{ .target = first_target, .arguments = first_arguments[0..] },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(10),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = final_predecessor,
            .kind = .jump,
            .from = .{ .target = first_source },
            .to = .{ .target = final_source },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(20),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(3),
            .source = first_source,
            .kind = .jump,
            .from = .{ .target = first_target },
            .to = .{ .target = unrelated_target },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(15),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(4),
            .source = final_source,
            .kind = .jump,
            .from = .{ .target = unrelated_target, .arguments = first_arguments[0..] },
            .to = .{ .target = final_target, .arguments = final_arguments[0..] },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(20),
        },
    };
    const program = ir.Program{
        .program_id = "paired-multi-step-lineage",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };
    const prior: CollisionArm = .{ .source = left_source, .kind = .jump, .target = left_target };
    const candidate: CollisionArm = .{ .source = final_source, .kind = .jump, .target = final_target };
    var lineage_index = try FeedbackLineageIndex.init(std.testing.allocator, &program);
    defer lineage_index.deinit();
    try std.testing.expectEqual(
        sameNodeSplitPairedArmLineage(&program, prior, candidate),
        sameNodeSplitPairedArmLineageWithIndex(&program, &lineage_index, prior, candidate),
    );
    try std.testing.expectEqual(
        sameCollisionArmPosition(program.edge_rewrites, prior, candidate),
        sameCollisionArmPositionWithIndex(&lineage_index, prior, candidate),
    );
    try std.testing.expect(!sameNodeSplitPairedArmLineageWithIndex(
        &program,
        &lineage_index,
        prior,
        .{ .source = unrelated_source, .kind = .jump, .target = final_target },
    ));
    try std.testing.expect(sameNodeSplitPairedArmLineage(&program, prior, candidate));
    var projection = try structural_overlap.ReplayProjectionContext.init(std.testing.allocator, &program);
    defer projection.deinit();
    const prior_arms = [_]CollisionArm{prior};
    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &program,
        &prior_arms,
        candidate,
        &projection,
    )) != null);

    try std.testing.expect(!sameNodeSplitPairedArmLineage(&program, prior, .{
        .source = unrelated_source,
        .kind = .jump,
        .target = final_target,
    }));
    try std.testing.expect(!sameNodeSplitPairedArmLineage(&program, prior, .{
        .source = final_source,
        .kind = .jump,
        .target = unrelated_target,
    }));

    var tampered_groups = rewrites;
    tampered_groups[4].node_split_group = ir.NodeSplitGroupId.fromIndex(99);
    var tampered_group_program = program;
    tampered_group_program.edge_rewrites = &tampered_groups;
    try std.testing.expect(!sameNodeSplitPairedArmLineage(&tampered_group_program, prior, candidate));

    var tampered_source = rewrites;
    tampered_source[4].source = first_source;
    var tampered_source_program = program;
    tampered_source_program.edge_rewrites = &tampered_source;
    try std.testing.expect(!sameNodeSplitPairedArmLineage(&tampered_source_program, prior, candidate));

    var tampered_blocks = blocks;
    tampered_blocks[final_source.index()].terminator = .{ .jump = .{
        .target = final_target,
        .arguments = tampered_arguments[0..],
    } };
    var tampered_edge_program = program;
    tampered_edge_program.blocks = &tampered_blocks;
    try std.testing.expect(!sameNodeSplitPairedArmLineage(&tampered_edge_program, prior, candidate));
}

test "lineage collision distinguishes authenticated continuation contexts" {
    const source = ir.BlockId.fromIndex(7);
    const target = ir.BlockId.fromIndex(11);
    const first_context: structure.CollisionContext = .{
        .start = ir.BlockId.fromIndex(20),
        .stop = ir.BlockId.fromIndex(21),
        .loop_exit = null,
        .continue_target = ir.BlockId.fromIndex(22),
    };
    const second_context: structure.CollisionContext = .{
        .start = ir.BlockId.fromIndex(30),
        .stop = ir.BlockId.fromIndex(31),
        .loop_exit = null,
        .continue_target = ir.BlockId.fromIndex(32),
    };
    const prior = [_]CollisionArm{.{
        .source = source,
        .kind = .jump,
        .target = target,
        .context = first_context,
    }};

    try std.testing.expect(findLineageCollisionArm(
        &.{},
        &prior,
        .{ .source = source, .kind = .jump, .target = target, .context = first_context },
    ) != null);
    try std.testing.expect(findLineageCollisionArm(
        &.{},
        &prior,
        .{ .source = source, .kind = .jump, .target = target, .context = second_context },
    ) == null);
    try std.testing.expect(findLineageCollisionArm(
        &.{},
        &prior,
        .{ .source = source, .kind = .jump, .target = target },
    ) != null);
}

test "repeated collision arm requires authenticated tuple projection" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const source_first = ir.ValueId.fromIndex(0);
    const source_second = ir.ValueId.fromIndex(1);
    const clone_first = ir.ValueId.fromIndex(2);
    const clone_second = ir.ValueId.fromIndex(3);
    const unrelated_first = ir.ValueId.fromIndex(4);
    const unrelated_second = ir.ValueId.fromIndex(5);
    const source_arguments = [_]ir.ValueId{ source_first, source_second };
    const clone_arguments = [_]ir.ValueId{ clone_first, clone_second };
    const unrelated_arguments = [_]ir.ValueId{ unrelated_first, unrelated_second };
    const source_parameters = [_]ir.ValueId{ source_first, source_second };
    const clone_parameters = [_]ir.ValueId{ clone_first, clone_second };
    const values = [_]ir.Value{
        .{ .id = source_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source, .index = 0 } } },
        .{ .id = source_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source, .index = 1 } } },
        .{ .id = clone_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 0 } } },
        .{ .id = clone_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 1 } } },
        .{ .id = unrelated_first, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = unrelated_second, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source, .arguments = source_arguments[0..] } } },
        .{ .id = source, .function = function_id, .parameters = source_parameters[0..], .terminator = .{ .return_values = &.{} } },
        .{ .id = clone, .function = function_id, .parameters = clone_parameters[0..], .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{ .id = function_id, .blocks = &.{ entry, source, clone }, .entry_block = entry };
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = entry,
        .kind = .jump,
        .from = .{ .target = source, .arguments = source_arguments[0..] },
        .to = .{ .target = clone, .arguments = source_arguments[0..] },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const program = ir.Program{
        .program_id = "repeated-collision-arm-projection",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    const prior_context: structure.CollisionContext = .{
        .start = source,
        .stop = source,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = source_arguments[0..],
    };
    const candidate_context: structure.CollisionContext = .{
        .start = clone,
        .stop = clone,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = clone_arguments[0..],
    };
    const prior = [_]CollisionArm{.{
        .source = entry,
        .kind = .jump,
        .target = source,
        .context = prior_context,
    }};

    var projection = try structural_overlap.ReplayProjectionContext.init(std.testing.allocator, &program);
    defer projection.deinit();
    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &program,
        &prior,
        .{ .source = entry, .kind = .jump, .target = clone, .context = candidate_context },
        &projection,
    )) != null);

    const tampered_context: structure.CollisionContext = .{
        .start = clone,
        .stop = clone,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = unrelated_arguments[0..],
    };
    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &program,
        &prior,
        .{ .source = entry, .kind = .jump, .target = clone, .context = tampered_context },
        &projection,
    )) == null);

    var unknown_prior = prior;
    unknown_prior[0].context = null;
    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &program,
        &unknown_prior,
        .{ .source = entry, .kind = .jump, .target = clone, .context = candidate_context },
        &projection,
    )) == null);
}

test "repeated collision arm accepts an authenticated continuation clone" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const continuation = ir.BlockId.fromIndex(3);
    const continuation_clone = ir.BlockId.fromIndex(4);
    const unrelated_continuation = ir.BlockId.fromIndex(5);
    const source_first = ir.ValueId.fromIndex(0);
    const source_second = ir.ValueId.fromIndex(1);
    const clone_first = ir.ValueId.fromIndex(2);
    const clone_second = ir.ValueId.fromIndex(3);
    const source_arguments = [_]ir.ValueId{ source_first, source_second };
    const clone_arguments = [_]ir.ValueId{ clone_first, clone_second };
    const values = [_]ir.Value{
        .{ .id = source_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source, .index = 0 } } },
        .{ .id = source_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source, .index = 1 } } },
        .{ .id = clone_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 0 } } },
        .{ .id = clone_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 1 } } },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source, .arguments = source_arguments[0..] } } },
        .{ .id = source, .function = function_id, .parameters = source_arguments[0..], .terminator = .{ .return_values = &.{} } },
        .{ .id = clone, .function = function_id, .parameters = clone_arguments[0..], .terminator = .{ .return_values = &.{} } },
        .{ .id = continuation, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = continuation_clone, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = unrelated_continuation, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, source, clone, continuation, continuation_clone, unrelated_continuation },
        .entry_block = entry,
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .jump,
            .from = .{ .target = source, .arguments = source_arguments[0..] },
            .to = .{ .target = clone, .arguments = source_arguments[0..] },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = continuation,
            .kind = .jump,
            .from = .{ .target = continuation },
            .to = .{ .target = continuation_clone },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(1),
        },
    };
    const program = ir.Program{
        .program_id = "authenticated-continuation-boundary-clone",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    const prior_context: structure.CollisionContext = .{
        .start = source,
        .stop = source,
        .loop_exit = null,
        .continue_target = continuation,
        .parameter_arguments = source_arguments[0..],
    };
    const candidate_context: structure.CollisionContext = .{
        .start = clone,
        .stop = clone,
        .loop_exit = null,
        .continue_target = continuation_clone,
        .parameter_arguments = clone_arguments[0..],
    };
    const prior = [_]CollisionArm{.{
        .source = entry,
        .kind = .jump,
        .target = source,
        .context = prior_context,
    }};

    var projection = try structural_overlap.ReplayProjectionContext.init(std.testing.allocator, &program);
    defer projection.deinit();
    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &program,
        &prior,
        .{ .source = entry, .kind = .jump, .target = clone, .context = candidate_context },
        &projection,
    )) != null);

    var unrelated_context = candidate_context;
    unrelated_context.continue_target = unrelated_continuation;
    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &program,
        &prior,
        .{ .source = entry, .kind = .jump, .target = clone, .context = unrelated_context },
        &projection,
    )) == null);
}

test "same-root nested continuation endpoints remain distinct" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const root = ir.BlockId.fromIndex(2);
    const first = ir.BlockId.fromIndex(3);
    const first_nested = ir.BlockId.fromIndex(4);
    const second = ir.BlockId.fromIndex(5);
    const second_nested = ir.BlockId.fromIndex(6);
    const arguments = [_]ir.ValueId{
        ir.ValueId.fromIndex(0),
        ir.ValueId.fromIndex(1),
        ir.ValueId.fromIndex(2),
        ir.ValueId.fromIndex(3),
    };
    const values = [_]ir.Value{
        .{ .id = arguments[0], .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = arguments[1], .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = arguments[2], .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = arguments[3], .function = function_id, .type = .integer, .origin = .{ .parameter = 3 } },
    };
    const blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = target, .arguments = arguments[0..] } } },
        .{ .id = target, .function = function_id, .parameters = arguments[0..], .terminator = .{ .return_values = &.{} } },
        .{ .id = root, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = first, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = first_nested, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = second, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = second_nested, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ source, target, root, first, first_nested, second, second_nested },
        .entry_block = source,
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{ .id = ir.EdgeRewriteId.fromIndex(0), .source = root, .kind = .jump, .from = .{ .target = root }, .to = .{ .target = first }, .rule = .node_split, .node_split_group = ir.NodeSplitGroupId.fromIndex(10) },
        .{ .id = ir.EdgeRewriteId.fromIndex(1), .source = first, .kind = .jump, .from = .{ .target = first }, .to = .{ .target = first_nested }, .rule = .node_split, .node_split_group = ir.NodeSplitGroupId.fromIndex(11) },
        .{ .id = ir.EdgeRewriteId.fromIndex(2), .source = root, .kind = .jump, .from = .{ .target = root }, .to = .{ .target = second }, .rule = .node_split, .node_split_group = ir.NodeSplitGroupId.fromIndex(20) },
        .{ .id = ir.EdgeRewriteId.fromIndex(3), .source = second, .kind = .jump, .from = .{ .target = second }, .to = .{ .target = second_nested }, .rule = .node_split, .node_split_group = ir.NodeSplitGroupId.fromIndex(21) },
    };
    const program = ir.Program{
        .program_id = "same-root-nested-continuation-endpoints",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    const first_context: structure.CollisionContext = .{
        .start = target,
        .stop = target,
        .loop_exit = null,
        .continue_target = first_nested,
        .parameter_arguments = arguments[0..],
    };
    const second_context: structure.CollisionContext = .{
        .start = target,
        .stop = target,
        .loop_exit = null,
        .continue_target = second_nested,
        .parameter_arguments = arguments[0..],
    };
    const prior = [_]CollisionArm{.{
        .source = source,
        .kind = .jump,
        .target = target,
        .context = first_context,
    }};
    var projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer projection.deinit();
    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &program,
        &prior,
        .{ .source = source, .kind = .jump, .target = target, .context = second_context },
        &projection,
    )) == null);
}

test "repeated collision arm composes a multi-step parameterized continuation" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const first_clone = ir.BlockId.fromIndex(2);
    const final_clone = ir.BlockId.fromIndex(3);
    const source_parameters = [_]ir.ValueId{
        ir.ValueId.fromIndex(0),
        ir.ValueId.fromIndex(1),
        ir.ValueId.fromIndex(2),
        ir.ValueId.fromIndex(3),
    };
    const first_parameters = [_]ir.ValueId{
        ir.ValueId.fromIndex(4),
        ir.ValueId.fromIndex(5),
        ir.ValueId.fromIndex(6),
        ir.ValueId.fromIndex(7),
    };
    const final_parameters = [_]ir.ValueId{
        ir.ValueId.fromIndex(8),
        ir.ValueId.fromIndex(9),
        ir.ValueId.fromIndex(10),
        ir.ValueId.fromIndex(11),
    };
    const values = [_]ir.Value{
        .{ .id = source_parameters[0], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source, .index = 0 } } },
        .{ .id = source_parameters[1], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source, .index = 1 } } },
        .{ .id = source_parameters[2], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source, .index = 2 } } },
        .{ .id = source_parameters[3], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source, .index = 3 } } },
        .{ .id = first_parameters[0], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = first_clone, .index = 0 } } },
        .{ .id = first_parameters[1], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = first_clone, .index = 1 } } },
        .{ .id = first_parameters[2], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = first_clone, .index = 2 } } },
        .{ .id = first_parameters[3], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = first_clone, .index = 3 } } },
        .{ .id = final_parameters[0], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = final_clone, .index = 0 } } },
        .{ .id = final_parameters[1], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = final_clone, .index = 1 } } },
        .{ .id = final_parameters[2], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = final_clone, .index = 2 } } },
        .{ .id = final_parameters[3], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = final_clone, .index = 3 } } },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = final_clone, .arguments = &source_parameters } } },
        .{ .id = source, .function = function_id, .parameters = &source_parameters, .terminator = .{ .return_values = &.{} } },
        .{ .id = first_clone, .function = function_id, .parameters = &first_parameters, .terminator = .{ .return_values = &.{} } },
        .{ .id = final_clone, .function = function_id, .parameters = &final_parameters, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, source, first_clone, final_clone },
        .entry_block = entry,
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .jump,
            .from = .{ .target = source, .arguments = &source_parameters },
            .to = .{ .target = first_clone, .arguments = &source_parameters },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = entry,
            .kind = .jump,
            .from = .{ .target = first_clone, .arguments = &source_parameters },
            .to = .{ .target = final_clone, .arguments = &source_parameters },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(1),
        },
    };
    const program = ir.Program{
        .program_id = "authenticated-multi-step-continuation",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    const prior_context: structure.CollisionContext = .{
        .start = source,
        .stop = source,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &source_parameters,
    };
    const candidate_context: structure.CollisionContext = .{
        .start = final_clone,
        .stop = final_clone,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = &final_parameters,
    };
    const prior = [_]CollisionArm{.{
        .source = entry,
        .kind = .jump,
        .target = source,
        .context = prior_context,
    }};

    var projection = try structural_overlap.ReplayProjectionContext.init(std.testing.allocator, &program);
    defer projection.deinit();
    const candidate: CollisionArm = .{ .source = entry, .kind = .jump, .target = final_clone, .context = candidate_context };
    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &program,
        &prior,
        candidate,
        &projection,
    )) != null);

    var tampered_blocks = blocks;
    tampered_blocks[entry.index()].terminator = .{ .jump = .{
        .target = final_clone,
        .arguments = &.{ source_parameters[0], source_parameters[1], source_parameters[2], final_parameters[3] },
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_projection = try structural_overlap.ReplayProjectionContext.init(std.testing.allocator, &tampered_program);
    defer tampered_projection.deinit();
    try std.testing.expect((try findPreviouslyTriedCollisionArm(
        &tampered_program,
        &prior,
        candidate,
        &tampered_projection,
    )) == null);
}

fn collisionCanSplit(reason: structure.CollisionReason) bool {
    return switch (reason) {
        .already_owned, .unvisited_loop_member, .unvisited_reachable => true,
        .outside_region, .unowned_escape_target => false,
    };
}

// A stable incoming group may contain the edge that already owns the
// continuation plus a new edge that collided with it. Cloning both edges
// recreates the same shared owner on every pass; split only the new edge so
// the authenticated owner remains on its existing path.
fn collisionGroupContainsPreviousOwner(collision: *const structure.Collision) bool {
    const previous = collision.previous orelse return false;
    const incoming = collision.incoming orelse return false;
    if (incoming.source == previous) return false;
    for (collision.incoming_group) |reference| {
        if (reference.source == previous and reference.target == collision.block) return true;
    }
    return false;
}

test "collision group containing previous owner narrows to current edge" {
    const block = ir.BlockId.fromIndex(3);
    const current = ir.BlockId.fromIndex(7);
    const previous = ir.BlockId.fromIndex(11);
    var group = [_]ir.CfgEdgeRef{
        .{ .source = current, .kind = .branch_else, .target = block },
        .{ .source = previous, .kind = .branch_else, .target = block },
    };
    const collision = structure.Collision{
        .block = block,
        .previous = previous,
        .incoming = group[0],
        .reason = .already_owned,
        .incoming_group = group[0..],
    };
    try std.testing.expect(collisionGroupContainsPreviousOwner(&collision));
}

fn planUnvisitedFrontiersAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function_index: usize,
    frontiers: []const structure.UnvisitedFrontier,
    prior_arms: []const CollisionArm,
) NormalizeError!?SplitPlan {
    return planUnvisitedFrontiersAllocWithAnalysis(
        allocator,
        program,
        function_index,
        null,
        null,
        frontiers,
        prior_arms,
    );
}

fn planUnvisitedFrontiersAllocWithAnalysis(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function_index: usize,
    analysis: ?*const cfg.Analysis,
    projection_context: ?*structural_overlap.ReplayProjectionContext,
    frontiers: []const structure.UnvisitedFrontier,
    prior_arms: []const CollisionArm,
) NormalizeError!?SplitPlan {
    if (frontiers.len == 0) return null;
    const secondaries = try allocator.alloc(Secondary, frontiers.len);
    var secondary_count: usize = 0;
    errdefer deinitSecondaryPrefix(allocator, secondaries, secondary_count);
    for (frontiers) |frontier| {
        if (frontier.incoming_contexts.len != 0 and
            frontier.incoming_contexts.len != frontier.incoming.len)
        {
            deinitSecondaryPrefix(allocator, secondaries, secondary_count);
            return null;
        }
        const first_secondary = if (frontier.incoming.len > 1) @as(usize, 1) else 0;
        var selected: std.ArrayList(ir.CfgEdgeRef) = .empty;
        defer selected.deinit(allocator);
        var selected_contexts: std.ArrayList(?structure.CollisionContext) = .empty;
        defer selected_contexts.deinit(allocator);
        for (frontier.incoming[first_secondary..], first_secondary..) |reference, incoming_index| {
            const context = if (frontier.incoming_contexts.len == 0)
                null
            else
                frontier.incoming_contexts[incoming_index];
            const arm: CollisionArm = .{
                .source = reference.source,
                .kind = reference.kind,
                .target = reference.target,
                .context = context,
            };
            if (try collisionArmWasTriedWithAnalysis(
                program,
                analysis,
                prior_arms,
                arm,
                projection_context,
            )) continue;
            var duplicate = false;
            for (selected.items) |existing| {
                if (std.meta.eql(existing, reference)) {
                    duplicate = true;
                    break;
                }
            }
            if (duplicate) continue;
            try selected.append(allocator, reference);
            try selected_contexts.append(allocator, context);
        }
        if (selected.items.len == 0) {
            deinitSecondaryPrefix(allocator, secondaries, secondary_count);
            return null;
        }
        var split = (try structural_overlap.findCollisionClosureSplitAlloc(
            allocator,
            program,
            function_index,
            frontier.block,
            selected.items,
            frontier.closure,
        )) orelse {
            deinitSecondaryPrefix(allocator, secondaries, secondary_count);
            return null;
        };
        // Each secondary is prepared against the same immutable graph
        // snapshot.  If two frontier closures overlap, applying both would
        // clone one live continuation through two stale contexts.  Keep the
        // independent prefix and let the next feedback iteration recompute
        // the overlapping frontier after the first clone is published.
        var overlaps_previous = false;
        for (secondaries[0..secondary_count]) |previous| {
            if (closuresOverlap(previous.closure, split.closure)) {
                overlaps_previous = true;
                break;
            }
        }
        if (overlaps_previous) {
            split.deinit();
            break;
        }
        var incoming_contexts: []?structure.CollisionContext = &.{};
        errdefer {
            if (incoming_contexts.len != 0) allocator.free(incoming_contexts);
            split.deinit();
        }
        if (frontier.incoming_contexts.len != 0) {
            incoming_contexts = try allocator.alloc(?structure.CollisionContext, split.incoming.len);
            for (split.incoming, 0..) |reference, split_index| {
                var found_context = false;
                for (selected.items, 0..) |selected_reference, selected_index| {
                    if (!std.meta.eql(selected_reference, reference)) continue;
                    incoming_contexts[split_index] = selected_contexts.items[selected_index];
                    found_context = true;
                    break;
                }
                if (!found_context) {
                    return error.NormalizationInvariantFailed;
                }
            }
        }
        const split_incoming = split.incoming;
        const split_closure = split.closure;
        split.incoming = &.{};
        split.closure = &.{};
        split.deinit();
        secondaries[secondary_count] = .{
            .block = frontier.block,
            .incoming = split_incoming,
            .closure = split_closure,
            .incoming_contexts = incoming_contexts,
        };
        incoming_contexts = &.{};
        secondary_count += 1;
    }
    if (secondary_count == 0) {
        allocator.free(secondaries);
        return null;
    }
    return .{
        .allocator = allocator,
        .function_index = function_index,
        .secondaries = secondaries,
        .secondary_count = secondary_count,
    };
}

fn closuresOverlap(left: []const ir.BlockId, right: []const ir.BlockId) bool {
    for (left) |left_block| {
        for (right) |right_block| {
            if (left_block == right_block) return true;
        }
    }
    return false;
}

fn deinitSecondaryPrefix(
    allocator: std.mem.Allocator,
    secondaries: []Secondary,
    count: usize,
) void {
    for (secondaries[0..count]) |secondary| {
        allocator.free(secondary.incoming);
        if (secondary.incoming_contexts.len != 0) allocator.free(secondary.incoming_contexts);
        allocator.free(secondary.closure);
    }
    allocator.free(secondaries);
}

test "unvisited frontier planning batches independent components" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const first = ir.BlockId.fromIndex(1);
    const second = ir.BlockId.fromIndex(2);
    const router = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first },
            .else_edge = .{ .target = router },
        } } },
        .{ .id = first, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = second, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = router, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first },
            .else_edge = .{ .target = second },
        } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, first, second, router },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program: ir.Program = .{
        .program_id = "unvisited-frontier-batch",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var first_incoming = [_]ir.CfgEdgeRef{
        .{ .source = entry, .kind = .branch_then, .target = first },
        .{ .source = router, .kind = .branch_then, .target = first },
    };
    var second_incoming = [_]ir.CfgEdgeRef{.{
        .source = router,
        .kind = .branch_else,
        .target = second,
    }};
    var first_closure = [_]ir.BlockId{first};
    var second_closure = [_]ir.BlockId{second};
    const frontiers = [_]structure.UnvisitedFrontier{
        .{ .block = first, .incoming = &first_incoming, .closure = &first_closure },
        .{ .block = second, .incoming = &second_incoming, .closure = &second_closure },
    };

    var plan = (try planUnvisitedFrontiersAlloc(
        std.testing.allocator,
        &program,
        0,
        &frontiers,
        &.{},
    )).?;
    defer plan.deinit();
    try std.testing.expectEqual(@as(usize, 2), plan.secondary_count);
    try std.testing.expectEqual(first, plan.secondaries[0].block);
    try std.testing.expectEqual(second, plan.secondaries[1].block);
    try std.testing.expectEqual(@as(usize, 1), plan.secondaries[0].incoming.len);
    try std.testing.expectEqual(router, plan.secondaries[0].incoming[0].source);
}

test "unvisited frontier planning defers overlapping closures" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const first = ir.BlockId.fromIndex(1);
    const second = ir.BlockId.fromIndex(2);
    const shared = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first },
            .else_edge = .{ .target = second },
        } } },
        .{ .id = first, .function = function_id, .terminator = .{ .jump = .{ .target = shared } } },
        .{ .id = second, .function = function_id, .terminator = .{ .jump = .{ .target = shared } } },
        .{ .id = shared, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, first, second, shared },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program: ir.Program = .{
        .program_id = "overlapping-unvisited-frontier",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var first_incoming = [_]ir.CfgEdgeRef{.{
        .source = entry,
        .kind = .branch_then,
        .target = first,
    }};
    var second_incoming = [_]ir.CfgEdgeRef{.{
        .source = entry,
        .kind = .branch_else,
        .target = second,
    }};
    var first_closure = [_]ir.BlockId{ first, shared };
    var second_closure = [_]ir.BlockId{ second, shared };
    const frontiers = [_]structure.UnvisitedFrontier{
        .{ .block = first, .incoming = &first_incoming, .closure = &first_closure },
        .{ .block = second, .incoming = &second_incoming, .closure = &second_closure },
    };

    var plan = (try planUnvisitedFrontiersAlloc(
        std.testing.allocator,
        &program,
        0,
        &frontiers,
        &.{},
    )).?;
    defer plan.deinit();
    try std.testing.expectEqual(@as(usize, 1), plan.secondary_count);
    try std.testing.expectEqual(first, plan.secondaries[0].block);
}

/// Prove that a post-split collision seed still names the same owned
/// continuation without rebuilding the complete structure plan.  The seed is
/// accepted only when its exact node-split rewrite is still present, the live
/// edge still enters the seeded clone, and the prior structured tuple can be
/// replayed into the clone.  Any missing provenance returns false and forces
/// the ordinary full scan.
// A paired fold may retain a historical owner target while a later split has
// moved the live owner edge to an authenticated descendant.  Accept that
// transition only when the source-owned split chain reaches the historical
// target and its first step carries the live tuple.
fn ownerEdgeDescendsFromSeedTarget(
    program: *const ir.Program,
    projection: *const structural_overlap.ReplayProjectionContext,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    historical_target: ir.BlockId,
    live_target: ir.BlockId,
    live_arguments: []const ir.ValueId,
) bool {
    if (live_target == historical_target) return true;

    var current = live_target;
    var depth: usize = 0;
    var first_step = true;
    while (current != historical_target) : (depth += 1) {
        if (depth >= program.blocks.len) return false;
        const parent = projection.cloneLineageParent(current) orelse return false;
        const rewrite = findNodeSplitArmEdge(
            program.edge_rewrites,
            source,
            kind,
            parent.block,
            current,
        ) orelse return false;
        if (first_step and !std.mem.eql(ir.ValueId, rewrite.to.arguments, live_arguments)) return false;
        first_step = false;
        current = parent.block;
    }
    return true;
}

// Validate one source-owned historical split step.  The lineage index can
// reject a target with multiple incoming clone parents, but a repeated edge
// may legitimately have other owners for the same clone.  Restrict the proof
// to the seeded edge owner and replay each step's complete entry tuple.
fn authenticatedSourceOwnedNodeSplitStep(
    program: *const ir.Program,
    projection: *structural_overlap.ReplayProjectionContext,
    rewrite: ir.CfgEdgeRewrite,
    function: ir.Function,
) NormalizeError!bool {
    if (rewrite.rule != .node_split or rewrite.node_split_group == null or
        rewrite.from.target == rewrite.to.target or
        rewrite.source.index() >= program.blocks.len or
        rewrite.from.target.index() >= program.blocks.len or
        rewrite.to.target.index() >= program.blocks.len)
    {
        return false;
    }

    const edge_source = program.blocks[rewrite.source.index()];
    const from = program.blocks[rewrite.from.target.index()];
    const to = program.blocks[rewrite.to.target.index()];
    if (edge_source.id != rewrite.source or from.id != rewrite.from.target or
        to.id != rewrite.to.target or edge_source.function != function.id or
        from.function != function.id or to.function != function.id or
        rewrite.from.arguments.len != from.parameters.len or
        rewrite.to.arguments.len != to.parameters.len)
    {
        return false;
    }

    if (!projection.hasNodeSplitArmEdge(
        rewrite.source,
        rewrite.kind,
        rewrite.from.target,
        rewrite.to.target,
        rewrite.node_split_group,
    )) return false;

    return try projection.parametersEquivalent(
        rewrite.to.target,
        rewrite.from.arguments,
        rewrite.to.arguments,
    );
}

// A node-split clone may re-enter through a nested clone lineage instead of
// the historical owner block.  Reuse that path only when the seeded source
// owns a unique chain from the live clone through the recorded original
// target to the recorded owner, every step has a replayable tuple, and the
// live clone contains a nonempty CFG cycle.  This keeps clone-local reentry
// distinct from arbitrary graph reachability or unrelated clone history.
fn authenticatedClonedReentry(
    analysis: *const cfg.Analysis,
    projection: *structural_overlap.ReplayProjectionContext,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    target: ir.BlockId,
    owner: ir.BlockId,
    original_target: ir.BlockId,
    group: ir.NodeSplitGroupId,
) NormalizeError!bool {
    if (target == owner) return false;

    var current = target;
    var depth: usize = 0;
    while (current != owner) : (depth += 1) {
        if (depth >= projection.blockCount()) return false;

        var selected: ?ir.CfgEdgeRewrite = null;
        for (projection.program.edge_rewrites) |rewrite| {
            if (rewrite.source != source or rewrite.kind != kind or
                rewrite.to.target != current)
            {
                continue;
            }
            if (selected != null) return false;
            selected = rewrite;
        }
        const rewrite = selected orelse return false;
        if (depth == 0 and (rewrite.from.target != original_target or
            rewrite.node_split_group != group)) return false;
        if (!try authenticatedSourceOwnedNodeSplitStep(
            projection.program,
            projection,
            rewrite,
            analysis.function,
        )) return false;
        current = rewrite.from.target;
    }

    return try analysis.canReachNonEmptyPath(target, target);
}

fn seededCollisionStatus(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    seed: CollisionSeed,
    replay_context: *structural_overlap.ReplayProjectionContext,
) NormalizeError!CollisionSeedValidation {
    if (seed.function_index >= program.functions.len or
        analysis.function.id != program.functions[seed.function_index].id or
        seed.source == null or seed.kind == null or seed.original_target == null or
        seed.previous == null or seed.context == null)
    {
        return if (seed.function_index >= program.functions.len or
            analysis.function.id != program.functions[seed.function_index].id)
            CollisionSeedValidation.invalid_function
        else
            CollisionSeedValidation.missing_provenance;
    }

    const source = seed.source.?;
    const kind = seed.kind.?;
    const original_target = seed.original_target.?;
    const previous = seed.previous.?;
    const target = seed.target;
    if (source.index() >= program.blocks.len or
        original_target.index() >= program.blocks.len or
        target.index() >= program.blocks.len or
        previous.index() >= program.blocks.len or
        program.blocks[source.index()].function != analysis.function.id or
        program.blocks[original_target.index()].function != analysis.function.id or
        program.blocks[target.index()].function != analysis.function.id or
        program.blocks[previous.index()].function != analysis.function.id or
        !analysis.isReachable(source) or
        !analysis.isReachable(target) or
        !analysis.isReachable(previous))
    {
        return if (source.index() >= program.blocks.len or
            original_target.index() >= program.blocks.len or
            target.index() >= program.blocks.len or
            previous.index() >= program.blocks.len)
            CollisionSeedValidation.invalid_block
        else
            CollisionSeedValidation.unreachable_graph;
    }

    const reference = ir.CfgEdgeRef{ .source = source, .kind = kind, .target = target };
    const live = cfg_edge.value(program, reference) orelse return CollisionSeedValidation.missing_live_edge;
    if (live.target != target) return CollisionSeedValidation.live_target_mismatch;

    if (trace_normalize_phases and seed.proof == .paired_forwarding) {
        var printed: usize = 0;
        for (program.edge_rewrites) |rewrite| {
            if (rewrite.source != source or rewrite.kind != kind or printed >= 8) continue;
            traceNormalize("normalize_phase collision_seed_rewrite_candidate source={} kind={s} from={} to={} rule={s} from_args={any} to_args={any} live_args={any}\n", .{
                source.index(),
                @tagName(kind),
                rewrite.from.target.index(),
                rewrite.to.target.index(),
                @tagName(rewrite.rule),
                rewrite.from.arguments,
                rewrite.to.arguments,
                live.arguments,
            });
            printed += 1;
        }
    }

    var authenticated_rewrite = false;
    var authenticated_group: ?ir.NodeSplitGroupId = null;
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.source != source or rewrite.kind != kind or
            rewrite.from.target != original_target or rewrite.to.target != target or
            !std.mem.eql(ir.ValueId, rewrite.to.arguments, live.arguments)) continue;
        switch (seed.proof) {
            .node_split => {
                const group = rewrite.node_split_group orelse continue;
                if (rewrite.rule != .node_split) continue;
                if (seed.context.?.parameter_arguments) |expected| {
                    if (!std.mem.eql(ir.ValueId, rewrite.from.arguments, expected)) continue;
                } else if (rewrite.from.arguments.len != 0) {
                    continue;
                }
                authenticated_group = group;
            },
            .paired_forwarding => {
                if (rewrite.rule != .forwarding_jump or previous == source) continue;
                if (rewrite.from.arguments.len != program.blocks[original_target.index()].parameters.len or
                    rewrite.to.arguments.len != program.blocks[target.index()].parameters.len)
                {
                    return CollisionSeedValidation.forwarding_shape_mismatch;
                }
                // The fold's owner edge must still be live. This prevents a
                // stale forwarding record from turning an unrelated edge into
                // a directed retry after another graph mutation.
                const owner_reference: ir.CfgEdgeRef = .{
                    .source = previous,
                    .kind = kind,
                    .target = target,
                };
                const owner_edge = cfg_edge.value(program, owner_reference) orelse
                    return CollisionSeedValidation.owner_edge_missing;
                if (!ownerEdgeDescendsFromSeedTarget(
                    program,
                    replay_context,
                    previous,
                    kind,
                    target,
                    owner_edge.target,
                    owner_edge.arguments,
                ) or
                    owner_edge.arguments.len != program.blocks[target.index()].parameters.len or
                    !std.mem.eql(ir.ValueId, owner_edge.arguments, rewrite.to.arguments))
                {
                    traceNormalize("normalize_phase collision_seed_owner_mismatch previous={} owner_target={} owner_args={any} rewrite_to={} rewrite_args={any} expected={any}\n", .{
                        previous.index(),
                        owner_edge.target.index(),
                        owner_edge.arguments,
                        target.index(),
                        rewrite.to.arguments,
                        seed.context.?.parameter_arguments,
                    });
                    return CollisionSeedValidation.owner_edge_mismatch;
                }
                if (seed.context.?.parameter_arguments) |expected| {
                    if (!std.mem.eql(ir.ValueId, expected, owner_edge.arguments))
                        return CollisionSeedValidation.owner_tuple_mismatch;
                }
            },
            .clone_fold => {
                if (rewrite.rule != .clone_fold or previous != target) continue;
                const group = rewrite.node_split_group orelse continue;
                const parent = replay_context.cloneLineageParent(original_target) orelse continue;
                if (parent.block != target or parent.group != group) continue;
                if (rewrite.from.arguments.len != program.blocks[original_target.index()].parameters.len or
                    rewrite.to.arguments.len != program.blocks[target.index()].parameters.len)
                {
                    return CollisionSeedValidation.forwarding_shape_mismatch;
                }
                if (seed.context.?.parameter_arguments) |expected| {
                    if (!std.mem.eql(ir.ValueId, expected, live.arguments)) continue;
                } else if (live.arguments.len != 0) {
                    continue;
                }
            },
        }
        authenticated_rewrite = true;
        break;
    }
    if (!authenticated_rewrite) return CollisionSeedValidation.missing_rewrite;

    // The original obstruction was a structured re-entry, not merely an
    // edge into a clone.  Preserve the historical owner path when it remains
    // live, or accept the separately authenticated clone-local cycle.  An
    // acyclic clone entry still falls back to the full structurer.
    const reaches_previous = if (target == previous)
        try analysis.canReachNonEmptyPath(target, previous)
    else
        try analysis.canReach(target, previous);
    const reaches_cloned_owner = if (seed.proof == .node_split and authenticated_group != null)
        try authenticatedClonedReentry(
            analysis,
            replay_context,
            source,
            kind,
            target,
            previous,
            original_target,
            authenticated_group.?,
        )
    else
        false;
    if (!reaches_previous and !reaches_cloned_owner) return CollisionSeedValidation.no_reentry;

    if (!try replay_context.parametersEquivalent(
        target,
        seed.context.?.parameter_arguments,
        live.arguments,
    )) return CollisionSeedValidation.parameter_mismatch;
    return CollisionSeedValidation.live;
}

fn seededCollisionIsLive(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    seed: CollisionSeed,
    replay_context: *structural_overlap.ReplayProjectionContext,
) NormalizeError!bool {
    return (try seededCollisionStatus(program, analysis, seed, replay_context)) == .live;
}

test "seeded collision requires a fresh structuring obstruction" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, header, body, exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program = ir.Program{
        .program_id = "seeded-collision-loop-proof",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var replay = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer replay.deinit();

    const incoming = [_]ir.CfgEdgeRef{.{
        .source = entry,
        .kind = .branch_then,
        .target = header,
    }};
    var overlap = (try structural_overlap.findCollisionSplitAllocWithAnalysisAndReplayContext(
        std.testing.allocator,
        &program,
        &analysis,
        0,
        header,
        &incoming,
        &replay,
    )).?;
    defer overlap.deinit();
    const seed: CollisionSeed = .{
        .function_index = 0,
        .target = header,
        .source = entry,
        .kind = .branch_then,
        .original_target = header,
        .previous = entry,
        .context = null,
    };
    try std.testing.expect(!try seededCollisionIsLive(
        &program,
        &analysis,
        seed,
        &replay,
    ));
}

test "seeded collision accepts a nested source-owned clone lineage" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const original = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const cycle = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    var blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = target },
            .else_edge = .{ .target = owner },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{ .target = original } } },
        .{ .id = original, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = target, .function = function_id, .terminator = .{ .jump = .{ .target = cycle } } },
        .{ .id = cycle, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ source, owner, original, target, cycle },
        .entry_block = source,
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    var rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = source,
            .kind = .branch_then,
            .from = .{ .target = original },
            .to = .{ .target = target },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = source,
            .kind = .branch_then,
            .from = .{ .target = owner },
            .to = .{ .target = original },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(1),
        },
    };
    var program = ir.Program{
        .program_id = "seeded-collision-nested-source-lineage",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    const seed: CollisionSeed = .{
        .function_index = 0,
        .target = target,
        .source = source,
        .kind = .branch_then,
        .original_target = original,
        .previous = owner,
        .context = .{
            .start = owner,
            .stop = null,
            .loop_exit = null,
            .continue_target = null,
        },
    };

    {
        var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
        defer analysis.deinit();
        var replay = try structural_overlap.ReplayProjectionContext.init(
            std.testing.allocator,
            &program,
        );
        defer replay.deinit();
        try std.testing.expect(try analysis.canReachNonEmptyPath(target, target));
        try std.testing.expect(try seededCollisionIsLive(&program, &analysis, seed, &replay));
    }

    var wrong_owner = seed;
    wrong_owner.previous = source;
    {
        var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
        defer analysis.deinit();
        var replay = try structural_overlap.ReplayProjectionContext.init(
            std.testing.allocator,
            &program,
        );
        defer replay.deinit();
        try std.testing.expect(!try seededCollisionIsLive(&program, &analysis, wrong_owner, &replay));
    }

    rewrites[1].node_split_group = null;
    {
        var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
        defer analysis.deinit();
        var replay = try structural_overlap.ReplayProjectionContext.init(
            std.testing.allocator,
            &program,
        );
        defer replay.deinit();
        try std.testing.expect(!try seededCollisionIsLive(&program, &analysis, seed, &replay));
    }
    rewrites[1].node_split_group = ir.NodeSplitGroupId.fromIndex(1);

    blocks[cycle.index()].terminator = .{ .return_values = &.{} };
    {
        var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
        defer analysis.deinit();
        var replay = try structural_overlap.ReplayProjectionContext.init(
            std.testing.allocator,
            &program,
        );
        defer replay.deinit();
        try std.testing.expect(!try analysis.canReachNonEmptyPath(target, target));
        try std.testing.expect(!try seededCollisionIsLive(&program, &analysis, seed, &replay));
    }
}

test "seeded collision requires the exact live clone rewrite" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const original = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    var rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = source,
        .kind = .jump,
        .from = .{ .target = original },
        .to = .{ .target = clone },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = clone } } },
        .{ .id = original, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = clone, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ source, original, clone },
        .entry_block = source,
    };
    var program = ir.Program{
        .program_id = "seeded-collision-exact-rewrite",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var replay = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer replay.deinit();

    const context: structure.CollisionContext = .{
        .start = original,
        .stop = null,
        .loop_exit = null,
        .continue_target = null,
    };
    const seed: CollisionSeed = .{
        .function_index = 0,
        .target = clone,
        .source = source,
        .kind = .jump,
        .original_target = original,
        .previous = source,
        .context = context,
    };
    try std.testing.expect(try seededCollisionIsLive(&program, &analysis, seed, &replay));

    rewrites[0].to.target = original;
    try std.testing.expect(!try seededCollisionIsLive(&program, &analysis, seed, &replay));
}

test "seeded collision accepts authenticated clone-local reentry" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const original = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const cycle = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = clone },
            .else_edge = .{ .target = original },
        } } },
        .{ .id = original, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = clone, .function = function_id, .terminator = .{ .jump = .{ .target = cycle } } },
        .{ .id = cycle, .function = function_id, .terminator = .{ .jump = .{ .target = clone } } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ source, original, clone, cycle },
        .entry_block = source,
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    var rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = source,
        .kind = .branch_then,
        .from = .{ .target = original },
        .to = .{ .target = clone },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    var program = ir.Program{
        .program_id = "seeded-collision-clone-local-reentry",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    const seed: CollisionSeed = .{
        .function_index = 0,
        .target = clone,
        .source = source,
        .kind = .branch_then,
        .original_target = original,
        .previous = original,
        .context = .{
            .start = original,
            .stop = null,
            .loop_exit = null,
            .continue_target = null,
        },
    };

    {
        var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
        defer analysis.deinit();
        var replay = try structural_overlap.ReplayProjectionContext.init(
            std.testing.allocator,
            &program,
        );
        defer replay.deinit();
        try std.testing.expect(!try analysis.canReach(clone, original));
        try std.testing.expect(try analysis.canReachNonEmptyPath(clone, clone));
        try std.testing.expect(try seededCollisionIsLive(&program, &analysis, seed, &replay));
    }

    var wrong_owner = seed;
    wrong_owner.previous = source;
    {
        var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
        defer analysis.deinit();
        var replay = try structural_overlap.ReplayProjectionContext.init(
            std.testing.allocator,
            &program,
        );
        defer replay.deinit();
        try std.testing.expect(!try seededCollisionIsLive(&program, &analysis, wrong_owner, &replay));
    }
}

test "seeded collision rejects an acyclic clone-local reentry" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const original = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const continuation = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = clone },
            .else_edge = .{ .target = original },
        } } },
        .{ .id = original, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = clone, .function = function_id, .terminator = .{ .jump = .{ .target = continuation } } },
        .{ .id = continuation, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ source, original, clone, continuation },
        .entry_block = source,
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = source,
        .kind = .branch_then,
        .from = .{ .target = original },
        .to = .{ .target = clone },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const program = ir.Program{
        .program_id = "seeded-collision-acyclic-clone",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var replay = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer replay.deinit();
    const seed: CollisionSeed = .{
        .function_index = 0,
        .target = clone,
        .source = source,
        .kind = .branch_then,
        .original_target = original,
        .previous = original,
        .context = .{
            .start = original,
            .stop = null,
            .loop_exit = null,
            .continue_target = null,
        },
    };
    try std.testing.expect(!try analysis.canReachNonEmptyPath(clone, clone));
    try std.testing.expect(!try seededCollisionIsLive(&program, &analysis, seed, &replay));
}

test "paired forwarding seed requires its owner edge and exact rewrite" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const source = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const original = ir.BlockId.fromIndex(4);
    const selector = ir.ValueId.fromIndex(0);
    const owner_value = ir.ValueId.fromIndex(1);
    const source_value = ir.ValueId.fromIndex(2);
    const target_parameter = ir.ValueId.fromIndex(3);
    const original_parameter = ir.ValueId.fromIndex(4);
    const owner_arguments = [_]ir.ValueId{owner_value};
    const source_arguments = [_]ir.ValueId{source_value};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = owner_value, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = source_value, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } },
        .{ .id = target_parameter, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 3 } },
        .{ .id = original_parameter, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 4 } },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = source },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = owner_arguments[0..],
        } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = owner_arguments[0..],
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{target_parameter}, .terminator = .{ .jump = .{
            .target = owner,
            .arguments = owner_arguments[0..],
        } } },
        .{ .id = original, .function = function_id, .parameters = &.{original_parameter}, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ selector, owner_value, source_value, target_parameter, original_parameter },
        .blocks = &.{ entry, owner, source, target, original },
        .entry_block = entry,
    };
    var rewrite = ir.CfgEdgeRewrite{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = source,
        .kind = .jump,
        .from = .{ .target = original, .arguments = source_arguments[0..] },
        .to = .{ .target = target, .arguments = owner_arguments[0..] },
        .rule = .forwarding_jump,
    };
    var rewrites = [_]ir.CfgEdgeRewrite{rewrite};
    var program = ir.Program{
        .program_id = "paired-forwarding-seed",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var replay = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer replay.deinit();
    const context: structure.CollisionContext = .{
        .start = owner,
        .stop = null,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = owner_arguments[0..],
    };
    const seed: CollisionSeed = .{
        .function_index = 0,
        .target = target,
        .source = source,
        .kind = .jump,
        .original_target = original,
        .previous = owner,
        .context = context,
        .proof = .paired_forwarding,
    };
    try std.testing.expect(try seededCollisionIsLive(&program, &analysis, seed, &replay));

    rewrite.to.arguments = source_arguments[0..];
    rewrites[0] = rewrite;
    try std.testing.expect(!try seededCollisionIsLive(&program, &analysis, seed, &replay));

    rewrite = rewrites[0];
    rewrite.to.arguments = owner_arguments[0..];
    rewrite.rule = .node_split;
    rewrites[0] = rewrite;
    try std.testing.expect(!try seededCollisionIsLive(&program, &analysis, seed, &replay));
}

test "paired forwarding seed accepts an authenticated live owner descendant" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const source = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const original = ir.BlockId.fromIndex(4);
    const owner_clone = ir.BlockId.fromIndex(5);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{ .target = owner_clone } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .jump = .{ .target = owner } } },
        .{ .id = original, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = owner_clone, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, owner, source, target, original, owner_clone },
        .entry_block = entry,
    };
    var rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = source,
            .kind = .jump,
            .from = .{ .target = original, .arguments = &.{} },
            .to = .{ .target = target, .arguments = &.{} },
            .rule = .forwarding_jump,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = owner,
            .kind = .jump,
            .from = .{ .target = target, .arguments = &.{} },
            .to = .{ .target = owner_clone, .arguments = &.{} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
    };
    var program = ir.Program{
        .program_id = "paired-forwarding-owner-descendant",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var replay = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer replay.deinit();
    const seed: CollisionSeed = .{
        .function_index = 0,
        .target = target,
        .source = source,
        .kind = .jump,
        .original_target = original,
        .previous = owner,
        .context = .{
            .start = owner,
            .stop = null,
            .loop_exit = null,
            .continue_target = null,
            .parameter_arguments = null,
        },
        .proof = .paired_forwarding,
    };
    try std.testing.expect(try seededCollisionIsLive(&program, &analysis, seed, &replay));

    rewrites[1].node_split_group = null;
    replay.deinit();
    replay = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    try std.testing.expect(!try seededCollisionIsLive(&program, &analysis, seed, &replay));
}

// A direct target clone can expose the same authenticated collision arm again
// without changing its source. Reuse that exact live split boundary only when
// the clone parent, edge rewrite, current tuple, and continuation bridge all
// agree. This is intentionally separate from owner-composed source/target
// lineage: a direct target chain may advance one boundary, but an arbitrary
// predecessor has no proof of the carried continuation.
fn directTargetBridgeIsAuthenticated(
    analysis: *const cfg.Analysis,
    owner: CollisionArm,
    candidate: CollisionArm,
    projection_context: *structural_overlap.ReplayProjectionContext,
) NormalizeError!bool {
    if (owner.kind != candidate.kind or owner.target == candidate.target) {
        return false;
    }
    const target_parent = projection_context.cloneLineageParent(candidate.target) orelse return false;
    if (target_parent.block != owner.target) return false;
    if (owner.source != candidate.source) {
        // A target clone may be entered by a separately cloned source.  The
        // target-side node-split boundary plus replayCloneFold authenticates
        // that fold; source identity is not part of clone equivalence.
        return hasNodeSplitTargetArmEdgeInGroup(
            projection_context,
            candidate.kind,
            owner.target,
            candidate.target,
            target_parent.group,
        ) != null;
    }

    const reference: ir.CfgEdgeRef = .{
        .source = owner.source,
        .kind = owner.kind,
        .target = candidate.target,
    };
    return projection_context.hasNodeSplitArmEdge(
        owner.source,
        owner.kind,
        owner.target,
        candidate.target,
        null,
    ) and try projection_context.hasAuthenticatedContinuationBridgeForEdge(analysis, reference);
}

// A persisted node-split seed can land on an effectful direct target clone.
// Re-cloning that block is not a new semantic decision: replayMappingsForClone
// proves that the clone has the same operations, effects, values, packs, and
// structural terminator as its owner.  Fold only that exact authenticated
// boundary back to the owner and retain the forwarding record for replay.
fn collapseAuthenticatedDirectTargetCollisionEdge(
    allocator: std.mem.Allocator,
    program: *ir.Program,
    blocks: *std.ArrayList(ir.Block),
    rewrites: *std.ArrayList(ir.CfgEdgeRewrite),
    analysis: *const cfg.Analysis,
    owner: CollisionArm,
    candidate: CollisionArm,
    projection_context: *structural_overlap.ReplayProjectionContext,
) NormalizeError!bool {
    if (!try directTargetBridgeIsAuthenticated(
        analysis,
        owner,
        candidate,
        projection_context,
    )) return false;
    if (owner.target.index() >= blocks.items.len or
        candidate.source.index() >= blocks.items.len or
        candidate.target.index() >= blocks.items.len or
        blocks.items[owner.target.index()].id != owner.target or
        blocks.items[candidate.source.index()].id != candidate.source or
        blocks.items[candidate.target.index()].id != candidate.target or
        blocks.items[candidate.source.index()].function != blocks.items[owner.target.index()].function or
        blocks.items[candidate.target.index()].function != blocks.items[owner.target.index()].function or
        isHistoricalForwardingTarget(rewrites.items, owner.target))
    {
        return false;
    }

    const reference: ir.CfgEdgeRef = .{
        .source = candidate.source,
        .kind = candidate.kind,
        .target = candidate.target,
    };
    const live = cfg_edge.value(program, reference) orelse return false;
    if (live.target != candidate.target) return false;

    const target_parent = projection_context.cloneLineageParent(candidate.target) orelse return false;
    if (target_parent.block != owner.target) return false;
    const target_rewrite = findNodeSplitArmEdgeInGroup(
        rewrites.items,
        candidate.source,
        candidate.kind,
        owner.target,
        candidate.target,
        target_parent.group,
    ) orelse hasNodeSplitTargetArmEdgeInGroup(
        projection_context,
        candidate.kind,
        owner.target,
        candidate.target,
        target_parent.group,
    ) orelse return false;
    if (!std.mem.eql(ir.ValueId, live.arguments, target_rewrite.to.arguments) or
        live.arguments.len != blocks.items[candidate.target.index()].parameters.len)
    {
        return false;
    }

    // Authenticate the complete clone before changing the live edge.  The
    // argument projection below must agree with the same replay contract that
    // proof validation will use for the persisted clone_fold record.
    const replayed = (try node_split.replayCloneFold(
        allocator,
        program,
        live,
        owner.target,
        target_parent.group,
    )) orelse return false;
    defer if (replayed.arguments.len != 0) allocator.free(replayed.arguments);
    if (replayed.target != owner.target) return false;

    var mappings = (try node_split.replayMappingsForCloneAlloc(
        allocator,
        program,
        owner.target,
        candidate.target,
        target_parent.group,
    )) orelse return false;
    defer mappings.deinit();

    const projected = (try mapEdgeArgumentsBackwardThroughClone(
        allocator,
        program,
        owner.target,
        candidate.target,
        target_parent.group,
        live.arguments,
    )) orelse return false;
    errdefer allocator.free(projected);
    if (projected.len != blocks.items[owner.target.index()].parameters.len or
        !std.mem.eql(ir.ValueId, projected, replayed.arguments)) return false;

    if (!(try redirectEdgeWithDominancePreflight(
        allocator,
        program,
        blocks.items,
        analysis.function.id,
        &blocks.items[candidate.source.index()],
        reference,
        owner.target,
        projected,
    ))) return false;
    const from_arguments = try allocator.dupe(ir.ValueId, live.arguments);
    errdefer allocator.free(from_arguments);
    try rewrites.append(allocator, .{
        .id = ir.EdgeRewriteId.fromIndex(rewrites.items.len),
        .source = candidate.source,
        .kind = candidate.kind,
        .from = .{ .target = candidate.target, .arguments = from_arguments },
        .to = .{ .target = owner.target, .arguments = projected },
        .rule = .clone_fold,
        .node_split_group = target_parent.group,
    });
    program.blocks = blocks.items;
    program.edge_rewrites = rewrites.items;
    return true;
}

// A collision may expose a chain of independently authenticated target
// clones.  Each fold changes the live CFG edge, so rebuild the small CFG
// analysis before the next proof; the immutable clone-lineage index remains
// reusable because clone_fold records do not create new clone ownership.
// Stop at the first failed proof and leave the caller's ordinary feedback
// scan responsible for any shape that is not this exact target chain.
fn collapseAuthenticatedTargetLineageChain(
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    program: *ir.Program,
    blocks: *std.ArrayList(ir.Block),
    rewrites: *std.ArrayList(ir.CfgEdgeRewrite),
    function_index: usize,
    initial_owner: CollisionArm,
    initial_candidate: CollisionArm,
    projection: *structural_overlap.ReplayProjectionContext,
) NormalizeError!usize {
    if (function_index >= program.functions.len) return 0;

    var owner = initial_owner;
    var candidate = initial_candidate;
    var folded: usize = 0;
    var depth: usize = 0;
    const depth_limit = @max(program.blocks.len, 1);
    while (depth < depth_limit) : (depth += 1) {
        if (owner.target == candidate.target) break;

        var analysis = cfg.Analysis.init(
            scratch_allocator,
            program,
            program.functions[function_index],
        ) catch |err| switch (err) {
            error.InvalidCfg => break,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer analysis.deinit();

        const folded_here = if (try collapseOwnerComposedCollisionEdge(
            allocator,
            program,
            blocks,
            rewrites,
            &analysis,
            owner,
            candidate,
            projection,
        )) true else try collapseAuthenticatedDirectTargetCollisionEdge(
            allocator,
            program,
            blocks,
            rewrites,
            &analysis,
            owner,
            candidate,
            projection,
        );
        if (!folded_here) break;
        folded += 1;

        // The live edge now targets the owner.  Walk both endpoint lineages
        // to discover the next independently-authenticated owner; do not
        // infer a relationship from block IDs or source layout.
        const source_parent = projection.cloneLineageParent(candidate.source) orelse break;
        const target_parent = projection.cloneLineageParent(owner.target) orelse break;
        candidate = .{
            .source = candidate.source,
            .kind = candidate.kind,
            .target = owner.target,
            .context = null,
        };
        owner = .{
            .source = source_parent.block,
            .kind = candidate.kind,
            .target = target_parent.block,
            .context = null,
        };
    }
    return folded;
}

test "persisted direct target chain folds an effectful clone without collision history" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const owner_exit = ir.BlockId.fromIndex(2);
    const candidate = ir.BlockId.fromIndex(3);
    const candidate_exit = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const owner_result = ir.ValueId.fromIndex(1);
    const candidate_result = ir.ValueId.fromIndex(2);
    const owner_instruction = ir.InstructionId.fromIndex(0);
    const candidate_instruction = ir.InstructionId.fromIndex(1);
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = candidate },
            .else_edge = .{ .target = owner },
        } } },
        .{ .id = owner, .function = function_id, .instructions = &.{owner_instruction}, .terminator = .{ .jump = .{ .target = owner_exit } } },
        .{ .id = owner_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = candidate, .function = function_id, .instructions = &.{candidate_instruction}, .terminator = .{ .jump = .{ .target = candidate_exit } } },
        .{ .id = candidate_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, owner, owner_exit, candidate, candidate_exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = owner_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = owner_instruction, .index = 0 } } },
        .{ .id = candidate_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = candidate_instruction, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = owner_instruction, .block = owner, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{owner_result}, .effects = .pure },
        .{ .id = candidate_instruction, .block = candidate, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{candidate_result}, .effects = .pure },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .branch_then,
            .from = .{ .target = owner },
            .to = .{ .target = candidate },
            .rule = .node_split,
            .node_split_group = group,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = candidate,
            .kind = .jump,
            .from = .{ .target = owner_exit },
            .to = .{ .target = candidate_exit },
            .rule = .node_split,
            .node_split_group = group,
        },
    };
    var block_storage: std.ArrayList(ir.Block) = .empty;
    defer block_storage.deinit(std.testing.allocator);
    try block_storage.appendSlice(std.testing.allocator, &blocks);
    var rewrite_storage: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    defer rewrite_storage.deinit(std.testing.allocator);
    try rewrite_storage.appendSlice(std.testing.allocator, &rewrites);
    var program = ir.Program{
        .program_id = "persisted-direct-target-fold",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = block_storage.items,
        .instructions = &instructions,
        .values = &values,
        .edge_rewrites = rewrite_storage.items,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var replay = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer replay.deinit();

    const owner_arm: CollisionArm = .{ .source = entry, .kind = .branch_then, .target = owner };
    const candidate_arm: CollisionArm = .{ .source = entry, .kind = .branch_then, .target = candidate };
    try std.testing.expect(try directTargetBridgeIsAuthenticated(
        &analysis,
        owner_arm,
        candidate_arm,
        &replay,
    ));
    try std.testing.expectEqual(@as(usize, 1), try collapseAuthenticatedTargetLineageChain(
        std.testing.allocator,
        std.testing.allocator,
        &program,
        &block_storage,
        &rewrite_storage,
        0,
        owner_arm,
        candidate_arm,
        &replay,
    ));
    try std.testing.expectEqual(owner, program.blocks[entry.index()].terminator.branch.then_edge.target);
    try std.testing.expectEqual(@as(usize, 3), program.edge_rewrites.len);
    try std.testing.expectEqual(ir.EdgeRewriteRule.clone_fold, program.edge_rewrites[2].rule);
    try std.testing.expectEqual(group, program.edge_rewrites[2].node_split_group.?);
    try std.testing.expectEqual(candidate, program.edge_rewrites[2].from.target);
    try std.testing.expectEqual(owner, program.edge_rewrites[2].to.target);

    var report = try @import("validate.zig").validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

// An authenticated repeated arm may land on a transparent empty jump whose
// only purpose is to carry a structural boundary. Forward that exact live
// edge and retain a history record instead of creating an unbounded chain of
// empty clones. The same bridge proof used by the split alternatives owns the
// redirection; no reachability-only collapse is allowed here.
fn collapseAuthenticatedTransparentCollisionEdge(
    allocator: std.mem.Allocator,
    program: *ir.Program,
    blocks: *std.ArrayList(ir.Block),
    rewrites: *std.ArrayList(ir.CfgEdgeRewrite),
    analysis: *const cfg.Analysis,
    function_index: usize,
    owner: CollisionArm,
    candidate: CollisionArm,
    projection_context: *structural_overlap.ReplayProjectionContext,
) NormalizeError!bool {
    const direct_authenticated = try directTargetBridgeIsAuthenticated(
        analysis,
        owner,
        candidate,
        projection_context,
    );
    const composed_authenticated = if (direct_authenticated)
        false
    else
        try sameNodeSplitOwnerComposedArmLineageWithReplay(
            program,
            analysis,
            projection_context,
            owner,
            candidate,
        );
    if (trace_normalize_phases and candidate.target.index() < blocks.items.len) {
        const probe = blocks.items[candidate.target.index()];
        if (probe.id == candidate.target and probe.parameters.len == 0 and probe.instructions.len == 0) {
            switch (probe.terminator) {
                .jump => |outgoing| {
                    const successor = if (outgoing.target.index() < blocks.items.len)
                        blocks.items[outgoing.target.index()]
                    else
                        null;
                    traceNormalize("feedback_transparent_probe owner_source={} owner_target={} candidate_source={} candidate_target={} direct={} composed={} outgoing_target={} outgoing_args={any} successor_params={} successor_canonical={}\n", .{
                        owner.source.index(),
                        owner.target.index(),
                        candidate.source.index(),
                        candidate.target.index(),
                        direct_authenticated,
                        composed_authenticated,
                        outgoing.target.index(),
                        outgoing.arguments,
                        if (successor) |block| block.parameters.len else 0,
                        if (successor) |block| node_split.parametersAreCanonical(program.values, block) else false,
                    });
                },
                else => {},
            }
        }
    }
    if ((!direct_authenticated and !composed_authenticated) or
        function_index >= program.functions.len or
        candidate.source.index() >= blocks.items.len or
        candidate.target.index() >= blocks.items.len)
    {
        return false;
    }
    if (!analysis.isReachable(candidate.source) or
        isHistoricalForwardingTarget(rewrites.items, candidate.target))
    {
        return false;
    }
    const function = program.functions[function_index];
    if (function.id != blocks.items[candidate.source.index()].function or
        blocks.items[candidate.target.index()].function != function.id)
    {
        return false;
    }
    for (program.functions) |other_function| {
        if (other_function.id == function.id and other_function.entry_block == candidate.target) {
            return false;
        }
    }

    const target_block = blocks.items[candidate.target.index()];
    if (target_block.id != candidate.target or target_block.parameters.len != 0 or
        target_block.instructions.len != 0)
    {
        return false;
    }
    const outgoing = switch (target_block.terminator) {
        .jump => |edge| edge,
        .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
    };
    if (outgoing.target == candidate.target or
        outgoing.target.index() >= blocks.items.len)
    {
        return false;
    }
    const successor = blocks.items[outgoing.target.index()];
    if (successor.id != outgoing.target or successor.function != function.id or
        outgoing.arguments.len != successor.parameters.len or
        (successor.parameters.len != 0 and
            !node_split.parametersAreCanonical(program.values, successor)))
    {
        return false;
    }

    const reference: ir.CfgEdgeRef = .{
        .source = candidate.source,
        .kind = candidate.kind,
        .target = candidate.target,
    };
    const live = cfg_edge.value(program, reference) orelse return false;
    if (live.target != reference.target or live.arguments.len != 0) return false;
    if (!redirectEdge(&blocks.items[candidate.source.index()], reference, outgoing.target, outgoing.arguments)) {
        return error.NormalizationInvariantFailed;
    }
    try rewrites.append(allocator, .{
        .id = ir.EdgeRewriteId.fromIndex(rewrites.items.len),
        .source = candidate.source,
        .kind = candidate.kind,
        .from = .{ .target = candidate.target, .arguments = live.arguments },
        .to = .{ .target = outgoing.target, .arguments = outgoing.arguments },
        .rule = .forwarding_jump,
    });
    program.blocks = blocks.items;
    program.edge_rewrites = rewrites.items;
    traceNormalize("feedback_transparent_forward source={} from={} to={}\n", .{
        candidate.source.index(),
        candidate.target.index(),
        outgoing.target.index(),
    });
    return true;
}

fn findDirectTargetBridgeAlternativeWithAnalysis(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    function_index: usize,
    owner: CollisionArm,
    candidate: CollisionArm,
    prior_arms: []const CollisionArm,
    projection_context: *structural_overlap.ReplayProjectionContext,
) NormalizeError!?structural_overlap.Split {
    if (!try directTargetBridgeIsAuthenticated(analysis, owner, candidate, projection_context)) return null;
    const reference: ir.CfgEdgeRef = .{
        .source = owner.source,
        .kind = owner.kind,
        .target = candidate.target,
    };
    for (prior_arms) |arm| {
        if (arm.source == reference.source and arm.kind == reference.kind and
            arm.target == reference.target)
        {
            return null;
        }
    }

    var split = try findCollisionSplitWithContext(
        allocator,
        program,
        analysis,
        function_index,
        candidate.target,
        &.{reference},
        projection_context,
    ) orelse return null;
    if (split.incoming.len != 1 or !std.meta.eql(split.incoming[0], reference)) {
        split.deinit();
        return null;
    }
    return split;
}

// A composed owner may already have an authenticated live edge from its
// source to the candidate's cloned target.  Reusing that persisted bridge is
// the only valid boundary alternative when the candidate source is a separate
// clone of the owner source.  Do not route through arbitrary predecessors:
// they have no proof that they carry this continuation or its tuple.
fn findOwnerComposedDirectBridgeAlternativeWithAnalysis(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    function_index: usize,
    owner: CollisionArm,
    candidate: CollisionArm,
    prior_arms: []const CollisionArm,
    projection_context: *structural_overlap.ReplayProjectionContext,
) NormalizeError!?structural_overlap.Split {
    if (!try sameNodeSplitOwnerComposedArmLineageWithReplay(
        program,
        analysis,
        projection_context,
        owner,
        candidate,
    )) return null;

    // A same-group source/target pair is one authenticated closure clone,
    // not an independently composed endpoint. Treating it as the latter
    // recreates a parameterized loop at every new clone and never changes the
    // structural ownership boundary. Let the owner-boundary fallback handle
    // the paired case instead.
    if (sameNodeSplitPairedArmLineageWithReplay(
        program,
        projection_context,
        owner,
        candidate,
    )) return null;

    const reference: ir.CfgEdgeRef = .{
        .source = owner.source,
        .kind = owner.kind,
        .target = candidate.target,
    };
    const live = cfg_edge.value(program, reference) orelse return null;
    if (live.target != candidate.target or
        !projection_context.hasNodeSplitArmEdge(
            owner.source,
            owner.kind,
            owner.target,
            candidate.target,
            null,
        ) or
        !try projection_context.hasAuthenticatedContinuationBridgeForEdge(analysis, reference))
    {
        return null;
    }

    for (prior_arms) |arm| {
        if (arm.source == reference.source and arm.kind == reference.kind and
            arm.target == reference.target)
        {
            return null;
        }
    }

    var split = try findCollisionSplitWithContext(
        allocator,
        program,
        analysis,
        function_index,
        candidate.target,
        &.{reference},
        projection_context,
    ) orelse return null;
    if (split.incoming.len != 1 or !std.meta.eql(split.incoming[0], reference)) {
        split.deinit();
        return null;
    }
    return split;
}

// When a repeated collision arm is authenticated as a composition of cloned
// endpoints, the current edge cannot be split again: that would manufacture
// the same logical arm indefinitely. Try the owner target and source as
// generic ownership boundaries, retaining only a genuinely fresh incoming
// edge. No family or sample policy is involved; the owner-composed replay
// proof is the only admission to this fallback.
fn findOwnerComposedBoundaryAlternativeWithAnalysis(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    function_index: usize,
    owner: CollisionArm,
    candidate: CollisionArm,
    prior_arms: []const CollisionArm,
    projection_context: *structural_overlap.ReplayProjectionContext,
) NormalizeError!?structural_overlap.Split {
    if (!try sameNodeSplitOwnerComposedArmLineageWithReplay(
        program,
        analysis,
        projection_context,
        owner,
        candidate,
    )) return null;

    const boundaries = [_]ir.BlockId{ owner.target, owner.source };
    for (boundaries) |boundary| {
        const split = try findPredecessorCollisionSplitAllocWithAnalysisAndReplayContext(
            allocator,
            program,
            analysis,
            function_index,
            boundary,
            null,
            prior_arms,
            false,
            null,
            projection_context,
        );
        if (split) |candidate_split| {
            if (try freshCollisionAlternativeWithAnalysis(
                program,
                analysis,
                candidate_split,
                prior_arms,
                projection_context,
                null,
            )) |fresh| return fresh;
        }
    }
    return null;
}

fn findPredecessorCollisionSplitAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function_index: usize,
    target: ir.BlockId,
    prior_arms: []const CollisionArm,
    allow_repeated: bool,
    candidate_context: ?structure.CollisionContext,
    projection_context: ?*structural_overlap.ReplayProjectionContext,
) NormalizeError!?structural_overlap.Split {
    if (projection_context != null) {
        if (function_index >= program.functions.len) return null;
        var local_analysis = cfg.Analysis.init(
            allocator,
            program,
            program.functions[function_index],
        ) catch |err| switch (err) {
            error.InvalidCfg => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer local_analysis.deinit();
        return findPredecessorCollisionSplitAllocWithAnalysisAndReplayContext(
            allocator,
            program,
            &local_analysis,
            function_index,
            target,
            null,
            prior_arms,
            allow_repeated,
            candidate_context,
            projection_context,
        );
    }
    return findPredecessorCollisionSplitAllocWithAnalysisAndReplayContext(
        allocator,
        program,
        null,
        function_index,
        target,
        null,
        prior_arms,
        allow_repeated,
        candidate_context,
        projection_context,
    );
}

fn findPredecessorCollisionSplitAllocWithAnalysisAndReplayContext(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: ?*const cfg.Analysis,
    function_index: usize,
    target: ir.BlockId,
    source_filter: ?ir.BlockId,
    prior_arms: []const CollisionArm,
    allow_repeated: bool,
    candidate_context: ?structure.CollisionContext,
    projection_context: ?*structural_overlap.ReplayProjectionContext,
) NormalizeError!?structural_overlap.Split {
    if (function_index >= program.functions.len) return null;
    var repeated: ?ir.CfgEdgeRef = null;
    const function = program.functions[function_index];
    var predecessor_sources: []const ir.BlockId = function.blocks;
    var owned_predecessor_sources: ?[]ir.BlockId = null;
    defer if (owned_predecessor_sources) |sources| allocator.free(sources);
    if (analysis) |graph| {
        if (graph.function.id != function.id) return error.NormalizationInvariantFailed;
        if (!graph.isReachable(target)) return null;
        const predecessor_count = graph.predecessorCount(target);
        const sources = try allocator.alloc(ir.BlockId, predecessor_count);
        errdefer allocator.free(sources);
        for (sources, 0..) |*source, predecessor_index| {
            source.* = graph.predecessorAt(target, predecessor_index) orelse
                return error.NormalizationInvariantFailed;
        }
        predecessor_sources = sources;
        owned_predecessor_sources = sources;
    }
    for (predecessor_sources) |source| {
        if (source.index() >= program.blocks.len) return error.NormalizationInvariantFailed;
        if (source_filter) |expected| {
            if (source != expected and !sameNodeSplitLineage(program.edge_rewrites, source, expected)) continue;
        }
        const terminator = program.blocks[source.index()].terminator;
        const candidates: [2]?ir.CfgEdgeRef = switch (terminator) {
            .jump => |edge| .{
                if (edge.target == target) .{ .source = source, .kind = .jump, .target = target } else null,
                null,
            },
            .branch => |branch| .{
                if (branch.then_edge.target == target) .{ .source = source, .kind = .branch_then, .target = target } else null,
                if (branch.else_edge.target == target) .{ .source = source, .kind = .branch_else, .target = target } else null,
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => .{ null, null },
        };
        for (candidates) |candidate_optional| {
            const candidate = candidate_optional orelse continue;
            const arm: CollisionArm = .{
                .source = candidate.source,
                .kind = candidate.kind,
                .target = candidate.target,
                .context = candidate_context,
            };
            if (try collisionArmWasTriedWithAnalysis(
                program,
                analysis,
                prior_arms,
                arm,
                projection_context,
            )) {
                if (repeated == null) repeated = candidate;
                continue;
            }
            const split = try findCollisionSplitWithContext(
                allocator,
                program,
                analysis,
                function_index,
                target,
                &.{candidate},
                projection_context,
            );
            if (split) |candidate_split| {
                if (try freshCollisionAlternativeWithAnalysis(
                    program,
                    analysis,
                    candidate_split,
                    prior_arms,
                    projection_context,
                    fallbackCollisionContextForArm(program, candidate, candidate_context),
                )) |fresh| return fresh;
            }
        }
    }
    if (!allow_repeated) return null;
    const candidate = repeated orelse return null;
    const repeated_split = try findCollisionSplitWithContext(
        allocator,
        program,
        analysis,
        function_index,
        target,
        &.{candidate},
        projection_context,
    );
    return repeated_split;
}

// A predecessor fallback does not have a fresh structured visit context, but
// the collision itself may carry the exact entry context for the target. Keep
// that context for arm freshness only when its boundary and tuple match the
// live edge. The fallback remains unseeded after application, so this is not a
// substitute for a replay-authenticated structured context.
fn fallbackCollisionContextForArm(
    program: *const ir.Program,
    reference: ir.CfgEdgeRef,
    context: ?structure.CollisionContext,
) ?structure.CollisionContext {
    const candidate = context orelse return null;
    if (candidate.start != reference.target) return null;
    const edge = cfg_edge.value(program, reference) orelse return null;
    if (candidate.parameter_arguments) |arguments| {
        if (!std.mem.eql(ir.ValueId, arguments, edge.arguments)) return null;
    } else if (edge.arguments.len != 0) {
        return null;
    }
    return candidate;
}

// A fallback split does not carry the structurer's visit context.  Recover it
// only for freshness accounting when its first live incoming edge preserves
// the exact boundary and parameter tuple.  The caller still marks the split
// unseedable: this context prevents duplicate scheduling, but it is not a
// substitute for a fresh structured traversal.
fn fallbackCollisionContextForSplit(
    program: *const ir.Program,
    split: structural_overlap.Split,
    context: ?structure.CollisionContext,
) ?structure.CollisionContext {
    if (split.incoming.len == 0) return null;
    return fallbackCollisionContextForArm(program, split.incoming[0], context);
}

test "fallback freshness retains an authenticated four-value context" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = ir.ValueId.fromIndex(0), .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = ir.ValueId.fromIndex(1), .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = ir.ValueId.fromIndex(2), .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = ir.ValueId.fromIndex(3), .function = function_id, .type = .integer, .origin = .{ .parameter = 3 } },
    };
    const arguments = [_]ir.ValueId{
        ir.ValueId.fromIndex(0),
        ir.ValueId.fromIndex(1),
        ir.ValueId.fromIndex(2),
        ir.ValueId.fromIndex(3),
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = arguments[0..],
        } } },
        .{ .id = target, .function = function_id, .parameters = arguments[0..], .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, target },
        .entry_block = entry,
    };
    const program = ir.Program{
        .program_id = "fallback-four-value-context",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    const context: structure.CollisionContext = .{
        .start = target,
        .stop = null,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = arguments[0..],
    };
    const prior = [_]CollisionArm{.{
        .source = entry,
        .kind = .jump,
        .target = target,
        .context = context,
    }};
    var projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer projection.deinit();

    const split = structural_overlap.Split{
        .allocator = std.testing.allocator,
        .function_index = 0,
        .branch = entry,
        .entry = target,
        .join = target,
        .incoming = try std.testing.allocator.dupe(ir.CfgEdgeRef, &.{.{
            .source = entry,
            .kind = .jump,
            .target = target,
        }}),
        .closure = try std.testing.allocator.dupe(ir.BlockId, &.{target}),
    };
    const retained = fallbackCollisionContextForSplit(&program, split, context);
    try std.testing.expect(retained != null);
    try std.testing.expect((try freshCollisionAlternative(
        &program,
        split,
        &prior,
        &projection,
        retained,
    )) == null);
}

fn findCollisionSplitWithContext(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: ?*const cfg.Analysis,
    function_index: usize,
    target: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    replay_context: ?*structural_overlap.ReplayProjectionContext,
) NormalizeError!?structural_overlap.Split {
    if (replay_context) |context| {
        if (analysis) |graph| {
            return structural_overlap.findCollisionSplitAllocWithAnalysisAndReplayContext(
                allocator,
                program,
                graph,
                function_index,
                target,
                incoming,
                context,
            );
        }
        if (function_index >= program.functions.len) return null;
        var local_analysis = cfg.Analysis.init(
            allocator,
            program,
            program.functions[function_index],
        ) catch |err| switch (err) {
            error.InvalidCfg => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer local_analysis.deinit();
        return structural_overlap.findCollisionSplitAllocWithAnalysisAndReplayContext(
            allocator,
            program,
            &local_analysis,
            function_index,
            target,
            incoming,
            context,
        );
    }
    return structural_overlap.findCollisionSplitAlloc(
        allocator,
        program,
        function_index,
        target,
        incoming,
    );
}

const FreshAlternativeContext = union(enum) {
    fixed: ?structure.CollisionContext,
    deferred: CollisionArm,
};

fn freshAlternativeContextForEdge(
    program: *const ir.Program,
    edge: ir.CfgEdgeRef,
    context: FreshAlternativeContext,
) ?structure.CollisionContext {
    return switch (context) {
        .fixed => |value| value,
        .deferred => |arm| if (arm.source == edge.source and
            arm.kind == edge.kind and
            arm.target == edge.target)
            arm.context
        else
            fallbackCollisionContextForArm(program, edge, arm.context),
    };
}

// A fallback planner may return a split whose first incoming edge is already
// represented by an authenticated collision arm after clone lineage is
// projected.  Reject that candidate before it is applied so the caller can
// try the next generic fallback instead of manufacturing a repeated arm.
fn freshCollisionAlternativeWithContext(
    program: *const ir.Program,
    split: structural_overlap.Split,
    prior_arms: []const CollisionArm,
    projection_context: ?*structural_overlap.ReplayProjectionContext,
    context: FreshAlternativeContext,
) NormalizeError!?structural_overlap.Split {
    return freshCollisionAlternativeWithContextAndAnalysis(
        program,
        null,
        split,
        prior_arms,
        projection_context,
        context,
    );
}

fn freshCollisionAlternativeWithContextAndAnalysis(
    program: *const ir.Program,
    analysis: ?*const cfg.Analysis,
    split: structural_overlap.Split,
    prior_arms: []const CollisionArm,
    projection_context: ?*structural_overlap.ReplayProjectionContext,
    context: FreshAlternativeContext,
) NormalizeError!?structural_overlap.Split {
    var candidate = split;
    errdefer candidate.deinit();
    if (candidate.incoming.len == 0) {
        candidate.deinit();
        return null;
    }

    var fresh_count: usize = 0;
    for (candidate.incoming) |edge| {
        const arm: CollisionArm = .{
            .source = edge.source,
            .kind = edge.kind,
            .target = edge.target,
            .context = freshAlternativeContextForEdge(program, edge, context),
        };
        const was_tried = if (projection_context) |projection|
            try collisionArmWasTriedWithAnalysis(program, analysis, prior_arms, arm, projection)
        else
            try collisionArmWasTried(program, prior_arms, arm, null);
        if (!was_tried) {
            fresh_count += 1;
        }
    }
    if (fresh_count == 0) {
        candidate.deinit();
        return null;
    }

    // Deferred planning can return one closure for several incoming arms. A
    // repeated first arm must not discard a later fresh arm, but applying the
    // whole split would replay the already-consumed edge. Retain only the
    // authenticated-fresh incoming edges and keep the prepared closure.
    if (fresh_count != candidate.incoming.len) {
        const filtered = try candidate.allocator.alloc(ir.CfgEdgeRef, fresh_count);
        var index: usize = 0;
        for (candidate.incoming) |edge| {
            const arm: CollisionArm = .{
                .source = edge.source,
                .kind = edge.kind,
                .target = edge.target,
                .context = freshAlternativeContextForEdge(program, edge, context),
            };
            const was_tried = if (projection_context) |projection|
                try collisionArmWasTriedWithAnalysis(program, analysis, prior_arms, arm, projection)
            else
                try collisionArmWasTried(program, prior_arms, arm, null);
            if (was_tried) continue;
            filtered[index] = edge;
            index += 1;
        }
        candidate.allocator.free(candidate.incoming);
        candidate.incoming = filtered;
    }
    return candidate;
}

fn freshCollisionAlternative(
    program: *const ir.Program,
    split: structural_overlap.Split,
    prior_arms: []const CollisionArm,
    projection_context: ?*structural_overlap.ReplayProjectionContext,
    context: ?structure.CollisionContext,
) NormalizeError!?structural_overlap.Split {
    return freshCollisionAlternativeWithContext(
        program,
        split,
        prior_arms,
        projection_context,
        .{ .fixed = context },
    );
}

fn freshCollisionAlternativeWithAnalysis(
    program: *const ir.Program,
    analysis: ?*const cfg.Analysis,
    split: structural_overlap.Split,
    prior_arms: []const CollisionArm,
    projection_context: ?*structural_overlap.ReplayProjectionContext,
    context: ?structure.CollisionContext,
) NormalizeError!?structural_overlap.Split {
    return freshCollisionAlternativeWithContextAndAnalysis(
        program,
        analysis,
        split,
        prior_arms,
        projection_context,
        .{ .fixed = context },
    );
}

fn freshCollisionAlternativeForDeferred(
    program: *const ir.Program,
    split: structural_overlap.Split,
    deferred: CollisionArm,
    prior_arms: []const CollisionArm,
    projection_context: ?*structural_overlap.ReplayProjectionContext,
) NormalizeError!?structural_overlap.Split {
    return freshCollisionAlternativeWithContext(
        program,
        split,
        prior_arms,
        projection_context,
        .{ .deferred = deferred },
    );
}

test "deferred freshness retains an exact arm context across a different start" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const argument = ir.ValueId.fromIndex(0);
    const arguments = [_]ir.ValueId{argument};
    const blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = arguments[0..],
        } } },
        .{ .id = target, .function = function_id, .parameters = arguments[0..], .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ source, target },
        .entry_block = source,
    };
    const program = ir.Program{
        .program_id = "deferred-exact-context",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{.{
            .id = argument,
            .function = function_id,
            .type = .integer,
            .origin = .{ .parameter = 0 },
        }},
    };
    const context: structure.CollisionContext = .{
        .start = source,
        .stop = null,
        .loop_exit = null,
        .continue_target = null,
        .parameter_arguments = arguments[0..],
    };
    const deferred: CollisionArm = .{
        .source = source,
        .kind = .jump,
        .target = target,
        .context = context,
    };
    const split = structural_overlap.Split{
        .allocator = std.testing.allocator,
        .function_index = 0,
        .branch = source,
        .entry = target,
        .join = target,
        .incoming = try std.testing.allocator.dupe(ir.CfgEdgeRef, &.{.{
            .source = source,
            .kind = .jump,
            .target = target,
        }}),
        .closure = try std.testing.allocator.dupe(ir.BlockId, &.{target}),
    };
    const prior = [_]CollisionArm{deferred};
    try std.testing.expect((try freshCollisionAlternativeForDeferred(
        &program,
        split,
        deferred,
        &prior,
        null,
    )) == null);
}

test "predecessor collision fallback prefers an untried incoming arm" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const first = ir.BlockId.fromIndex(1);
    const second = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first },
            .else_edge = .{ .target = second },
        } } },
        .{ .id = first, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = second, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, first, second, target },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program: ir.Program = .{
        .program_id = "predecessor-collision-fallback",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    const prior = [_]CollisionArm{.{
        .source = first,
        .kind = .jump,
        .target = target,
    }};

    var split = (try findPredecessorCollisionSplitAlloc(
        std.testing.allocator,
        &program,
        0,
        target,
        &prior,
        false,
        null,
        null,
    )).?;
    defer split.deinit();
    try std.testing.expectEqual(@as(usize, 1), split.incoming.len);
    try std.testing.expectEqual(second, split.incoming[0].source);
    try std.testing.expectEqual(ir.CfgEdgeKind.jump, split.incoming[0].kind);
}

test "sibling collision fallback rejects a root-equivalent different target" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const repeated_source = ir.BlockId.fromIndex(1);
    const candidate_source = ir.BlockId.fromIndex(2);
    const target_root = ir.BlockId.fromIndex(3);
    const previous_target = ir.BlockId.fromIndex(4);
    const current_target = ir.BlockId.fromIndex(5);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = repeated_source },
            .else_edge = .{ .target = candidate_source },
        } } },
        .{ .id = repeated_source, .function = function_id, .terminator = .{ .jump = .{ .target = current_target } } },
        .{ .id = candidate_source, .function = function_id, .terminator = .{ .jump = .{ .target = previous_target } } },
        .{ .id = target_root, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = previous_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = current_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, repeated_source, candidate_source, target_root, previous_target, current_target },
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
            .source = entry,
            .kind = .branch_else,
            .from = .{ .target = repeated_source },
            .to = .{ .target = candidate_source },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = candidate_source,
            .kind = .jump,
            .from = .{ .target = target_root },
            .to = .{ .target = previous_target },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(1),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = repeated_source,
            .kind = .jump,
            .from = .{ .target = target_root },
            .to = .{ .target = current_target },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(2),
        },
    };
    const program = ir.Program{
        .program_id = "sibling-target-ownership",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var projection = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer projection.deinit();

    const prior = [_]CollisionArm{};
    var accepted = (try findSiblingCollisionSplitAllocWithAnalysis(
        std.testing.allocator,
        &program,
        &analysis,
        0,
        previous_target,
        repeated_source,
        &prior,
        null,
        &projection,
        previous_target,
    )).?;
    defer accepted.deinit();
    try std.testing.expectEqual(candidate_source, accepted.incoming[0].source);
    try std.testing.expectEqual(previous_target, accepted.incoming[0].target);

    try std.testing.expect((try findSiblingCollisionSplitAllocWithAnalysis(
        std.testing.allocator,
        &program,
        &analysis,
        0,
        previous_target,
        repeated_source,
        &prior,
        null,
        &projection,
        current_target,
    )) == null);
}

test "collision fallback filters a repeated projected arm before application" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const first = ir.BlockId.fromIndex(1);
    const second = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first },
            .else_edge = .{ .target = second },
        } } },
        .{ .id = first, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = second, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, first, second, target },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program: ir.Program = .{
        .program_id = "fresh-collision-alternative",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer projection.deinit();
    const prior = [_]CollisionArm{.{
        .source = first,
        .kind = .jump,
        .target = target,
    }};

    const repeated = structural_overlap.Split{
        .allocator = std.testing.allocator,
        .function_index = 0,
        .branch = entry,
        .entry = first,
        .join = target,
        .incoming = try std.testing.allocator.dupe(ir.CfgEdgeRef, &.{.{
            .source = first,
            .kind = .jump,
            .target = target,
        }}),
        .closure = try std.testing.allocator.dupe(ir.BlockId, &.{first}),
    };
    try std.testing.expect((try freshCollisionAlternative(
        &program,
        repeated,
        &prior,
        &projection,
        null,
    )) == null);

    var fresh = structural_overlap.Split{
        .allocator = std.testing.allocator,
        .function_index = 0,
        .branch = entry,
        .entry = second,
        .join = target,
        .incoming = try std.testing.allocator.dupe(ir.CfgEdgeRef, &.{.{
            .source = second,
            .kind = .jump,
            .target = target,
        }}),
        .closure = try std.testing.allocator.dupe(ir.BlockId, &.{second}),
    };
    fresh = (try freshCollisionAlternative(
        &program,
        fresh,
        &prior,
        &projection,
        null,
    )).?;
    defer fresh.deinit();
    try std.testing.expectEqual(second, fresh.incoming[0].source);
}

test "collision fallback retains a fresh arm after a repeated split arm" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const first = ir.BlockId.fromIndex(1);
    const second = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first },
            .else_edge = .{ .target = second },
        } } },
        .{ .id = first, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = second, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, first, second, target },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program: ir.Program = .{
        .program_id = "fresh-arm-after-repeated-split-arm",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    const prior = [_]CollisionArm{.{
        .source = first,
        .kind = .jump,
        .target = target,
    }};
    var split = structural_overlap.Split{
        .allocator = std.testing.allocator,
        .function_index = 0,
        .branch = entry,
        .entry = first,
        .join = target,
        .incoming = try std.testing.allocator.dupe(ir.CfgEdgeRef, &.{
            .{ .source = first, .kind = .jump, .target = target },
            .{ .source = second, .kind = .jump, .target = target },
        }),
        .closure = try std.testing.allocator.dupe(ir.BlockId, &.{first}),
    };
    split = (try freshCollisionAlternative(
        &program,
        split,
        &prior,
        null,
        null,
    )).?;
    defer split.deinit();
    try std.testing.expectEqual(@as(usize, 1), split.incoming.len);
    try std.testing.expectEqual(second, split.incoming[0].source);
}

test "predecessor fallback scans past an authenticated projected arm" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const second = ir.BlockId.fromIndex(2);
    const clone = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = clone },
            .else_edge = .{ .target = second },
        } } },
        .{ .id = source, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = second, .function = function_id, .terminator = .{ .jump = .{ .target = clone } } },
        .{ .id = clone, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, source, second, clone },
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
        .source = entry,
        .kind = .branch_then,
        .from = .{ .target = source },
        .to = .{ .target = clone },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const program = ir.Program{
        .program_id = "predecessor-projected-arm-scan",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    const prior = [_]CollisionArm{.{
        .source = entry,
        .kind = .branch_then,
        .target = source,
    }};

    var projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &program,
    );
    defer projection.deinit();
    var split = (try findPredecessorCollisionSplitAlloc(
        std.testing.allocator,
        &program,
        0,
        clone,
        &prior,
        false,
        null,
        &projection,
    )).?;
    defer split.deinit();
    try std.testing.expectEqual(@as(usize, 1), split.incoming.len);
    try std.testing.expectEqual(second, split.incoming[0].source);
    try std.testing.expectEqual(ir.CfgEdgeKind.jump, split.incoming[0].kind);

    var tampered_rewrites = rewrites;
    tampered_rewrites[0].to.target = ir.BlockId.fromIndex(99);
    var tampered_program = program;
    tampered_program.edge_rewrites = &tampered_rewrites;
    var tampered_projection = try structural_overlap.ReplayProjectionContext.init(
        std.testing.allocator,
        &tampered_program,
    );
    defer tampered_projection.deinit();
    var tampered_split = (try findPredecessorCollisionSplitAlloc(
        std.testing.allocator,
        &tampered_program,
        0,
        clone,
        &prior,
        false,
        null,
        &tampered_projection,
    )).?;
    defer tampered_split.deinit();
    try std.testing.expectEqual(entry, tampered_split.incoming[0].source);
}

fn findSiblingCollisionSplitAllocWithAnalysis(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    function_index: usize,
    original_target: ir.BlockId,
    repeated_source: ir.BlockId,
    prior_arms: []const CollisionArm,
    candidate_context: ?structure.CollisionContext,
    projection_context: *structural_overlap.ReplayProjectionContext,
    required_target: ir.BlockId,
) NormalizeError!?structural_overlap.Split {
    if (function_index >= program.functions.len) return null;
    if (analysis.function.id != program.functions[function_index].id) return null;
    const repeated_root = nodeSplitRoot(program.edge_rewrites, repeated_source) orelse return null;
    const target_root = nodeSplitRoot(program.edge_rewrites, original_target) orelse return null;
    for (program.functions[function_index].blocks) |source| {
        if (source.index() >= program.blocks.len) return error.NormalizationInvariantFailed;
        const terminator = program.blocks[source.index()].terminator;
        switch (terminator) {
            .jump => |edge| {
                const reference: ir.CfgEdgeRef = .{ .source = source, .kind = .jump, .target = edge.target };
                if (try siblingCollisionSplitAlloc(
                    allocator,
                    program,
                    analysis,
                    function_index,
                    repeated_root,
                    target_root,
                    reference,
                    prior_arms,
                    candidate_context,
                    projection_context,
                    required_target,
                )) |split| return split;
            },
            .branch => |branch| {
                const candidates = [_]ir.CfgEdgeRef{
                    .{ .source = source, .kind = .branch_then, .target = branch.then_edge.target },
                    .{ .source = source, .kind = .branch_else, .target = branch.else_edge.target },
                };
                for (candidates) |reference| {
                    if (try siblingCollisionSplitAlloc(
                        allocator,
                        program,
                        analysis,
                        function_index,
                        repeated_root,
                        target_root,
                        reference,
                        prior_arms,
                        candidate_context,
                        projection_context,
                        required_target,
                    )) |split| return split;
                }
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
    }
    return null;
}

fn siblingCollisionSplitAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    function_index: usize,
    repeated_root: ir.BlockId,
    target_root: ir.BlockId,
    reference: ir.CfgEdgeRef,
    prior_arms: []const CollisionArm,
    candidate_context: ?structure.CollisionContext,
    projection_context: *structural_overlap.ReplayProjectionContext,
    required_target: ir.BlockId,
) NormalizeError!?structural_overlap.Split {
    if (!cfg_edge.isCurrent(program, reference)) return null;
    // A shared lineage root is not a substitute for the live collision edge.
    // Keep this fallback on the actual target; a distinct target needs its own
    // authenticated bridge or contextual proof before it can be selected.
    if (reference.target != required_target) return null;
    const source_root = nodeSplitRoot(program.edge_rewrites, reference.source) orelse return null;
    if (source_root != repeated_root or source_root == reference.source) return null;
    if (nodeSplitRoot(program.edge_rewrites, reference.target) != target_root) return null;
    const candidate: CollisionArm = .{
        .source = reference.source,
        .kind = reference.kind,
        .target = reference.target,
        .context = candidate_context,
    };
    if (try collisionArmWasTriedWithAnalysis(
        program,
        analysis,
        prior_arms,
        candidate,
        projection_context,
    )) {
        return null;
    }
    const split = try findCollisionSplitWithContext(
        allocator,
        program,
        analysis,
        function_index,
        reference.target,
        &.{reference},
        projection_context,
    ) orelse return null;
    return freshCollisionAlternativeWithAnalysis(
        program,
        analysis,
        split,
        prior_arms,
        projection_context,
        null,
    );
}

fn findDeferredCollisionSplitAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    deferred: CollisionArm,
    prior_arms: []const CollisionArm,
    only_function: ?usize,
    projection_context: *structural_overlap.ReplayProjectionContext,
) NormalizeError!?DeferredCollisionAlternative {
    if (deferred.source.index() >= program.blocks.len) return null;
    const blocks = try allocator.dupe(ir.Block, program.blocks);
    defer allocator.free(blocks);
    maskTriedPlanningArms(blocks, deferred, prior_arms);

    var planning = program.*;
    planning.blocks = blocks;
    for (planning.functions, 0..) |function, function_index| {
        if (only_function) |selected_function| if (function_index != selected_function) continue;
        var rejected_edges: usize = 0;
        while (true) {
            var graph = cfg.Analysis.init(allocator, &planning, function) catch |err| switch (err) {
                error.InvalidCfg => break,
                error.OutOfMemory => return error.OutOfMemory,
            };
            defer graph.deinit();
            var collision: ?structure.Collision = null;
            defer if (collision) |*value| value.deinit(allocator);
            if (structure.Plan.initWithCollision(allocator, &graph, &collision)) |plan_value| {
                var plan = plan_value;
                plan.deinit();
                break;
            } else |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.UnsupportedShape => {
                    const obstruction = if (collision) |*value| value else break;
                    if (!collisionCanSplit(obstruction.reason)) break;
                    var selected: ?structural_overlap.Split = null;
                    var single: [1]ir.CfgEdgeRef = undefined;
                    const incoming = if (obstruction.incoming_group.len != 0)
                        obstruction.incoming_group
                    else if (obstruction.incoming) |reference| incoming: {
                        single[0] = reference;
                        break :incoming single[0..];
                    } else incoming: {
                        selected = try findPredecessorCollisionSplitAlloc(
                            allocator,
                            program,
                            function_index,
                            obstruction.block,
                            prior_arms,
                            false,
                            null,
                            projection_context,
                        );
                        break :incoming &.{};
                    };
                    if (incoming.len != 0) {
                        selected = if (obstruction.reason == .unvisited_reachable and
                            obstruction.unvisited_frontiers.len != 0)
                            try structural_overlap.findCollisionClosureSplitAlloc(
                                allocator,
                                program,
                                function_index,
                                obstruction.block,
                                incoming,
                                obstruction.unvisited_frontiers[0].closure,
                            )
                        else
                            try structural_overlap.findCollisionSplitAlloc(
                                allocator,
                                program,
                                function_index,
                                obstruction.block,
                                incoming,
                            );
                    }
                    var split = selected orelse break;
                    if (split.incoming.len == 0) {
                        split.deinit();
                        break;
                    }
                    const rejected = split.incoming[0];
                    if (try freshCollisionAlternativeForDeferred(
                        program,
                        split,
                        deferred,
                        prior_arms,
                        projection_context,
                    )) |fresh| {
                        return .{ .split = fresh };
                    }
                    if (!maskPlanningArm(blocks, rejected)) break;
                    rejected_edges += 1;
                    if (rejected_edges > function.blocks.len * 2 + 1) {
                        return error.NormalizationInvariantFailed;
                    }
                },
            }
        }
    }
    return null;
}

fn maskTriedPlanningArms(
    blocks: []ir.Block,
    deferred: CollisionArm,
    prior_arms: []const CollisionArm,
) void {
    for (blocks) |*block| switch (block.terminator) {
        .jump => {
            if (armSlotWasTried(deferred, prior_arms, block.id, .jump, block.terminator.jump.target)) {
                block.terminator = .{ .unreachable_block = {} };
            }
        },
        .branch => |branch| {
            const then_tried = armSlotWasTried(deferred, prior_arms, block.id, .branch_then, branch.then_edge.target);
            const else_tried = armSlotWasTried(deferred, prior_arms, block.id, .branch_else, branch.else_edge.target);
            if (then_tried and else_tried) {
                block.terminator = .{ .unreachable_block = {} };
            } else if (then_tried) {
                block.terminator = .{ .jump = branch.else_edge };
            } else if (else_tried) {
                block.terminator = .{ .jump = branch.then_edge };
            }
        },
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
    };
}

fn maskPlanningArm(blocks: []ir.Block, reference: ir.CfgEdgeRef) bool {
    if (reference.source.index() >= blocks.len) return false;
    const block = &blocks[reference.source.index()];
    if (block.id != reference.source) return false;
    switch (block.terminator) {
        .jump => |edge| {
            if (reference.kind != .jump or edge.target != reference.target) return false;
            block.terminator = .{ .unreachable_block = {} };
            return true;
        },
        .branch => |branch| {
            if (reference.kind == .branch_then and branch.then_edge.target == reference.target) {
                block.terminator = if (branch.else_edge.target == reference.target)
                    .{ .unreachable_block = {} }
                else
                    .{ .jump = branch.else_edge };
                return true;
            }
            if (reference.kind == .branch_else and branch.else_edge.target == reference.target) {
                block.terminator = if (branch.then_edge.target == reference.target)
                    .{ .unreachable_block = {} }
                else
                    .{ .jump = branch.then_edge };
                return true;
            }
            return false;
        },
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
    }
}

fn armSlotWasTried(
    deferred: CollisionArm,
    prior_arms: []const CollisionArm,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    target: ir.BlockId,
) bool {
    if (deferred.source == source and deferred.kind == kind and deferred.target == target) return true;
    for (prior_arms) |arm| {
        if (arm.source == source and arm.kind == kind and arm.target == target) return true;
    }
    return false;
}

test "deferred planning masks tried edge slots in one pass" {
    const function_id = ir.FunctionId.fromIndex(0);
    const first = ir.BlockId.fromIndex(0);
    const second = ir.BlockId.fromIndex(1);
    const then_target = ir.BlockId.fromIndex(2);
    const else_target = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    var blocks = [_]ir.Block{
        .{ .id = first, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = then_target },
            .else_edge = .{ .target = else_target },
        } } },
        .{ .id = second, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = then_target },
            .else_edge = .{ .target = else_target },
        } } },
    };
    const deferred: CollisionArm = .{
        .source = first,
        .kind = .branch_then,
        .target = then_target,
    };
    const prior = [_]CollisionArm{
        .{ .source = first, .kind = .branch_else, .target = else_target },
        .{ .source = second, .kind = .branch_then, .target = then_target },
    };

    maskTriedPlanningArms(&blocks, deferred, &prior);
    try std.testing.expect(std.meta.activeTag(blocks[0].terminator) == .unreachable_block);
    try std.testing.expect(std.meta.activeTag(blocks[1].terminator) == .jump);
    try std.testing.expectEqual(else_target, blocks[1].terminator.jump.target);

    var alternate = [_]ir.Block{.{ .id = second, .function = function_id, .terminator = .{ .branch = .{
        .condition = condition,
        .then_edge = .{ .target = else_target },
        .else_edge = .{ .target = then_target },
    } } }};
    maskTriedPlanningArms(&alternate, deferred, &prior);
    try std.testing.expect(std.meta.activeTag(alternate[0].terminator) == .branch);
    try std.testing.expectEqual(else_target, alternate[0].terminator.branch.then_edge.target);
}

fn nodeSplitRoot(rewrites: []const ir.CfgEdgeRewrite, initial: ir.BlockId) ?ir.BlockId {
    var current = initial;
    var depth: usize = 0;
    while (depth <= rewrites.len) : (depth += 1) {
        var source: ?ir.BlockId = null;
        for (rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.to.target != current) continue;
            if (source) |existing| {
                if (existing != rewrite.from.target) return null;
            } else {
                source = rewrite.from.target;
            }
        }
        const parent = source orelse return current;
        if (parent == current) return null;
        current = parent;
    }
    return null;
}

fn blockParametersAreCanonical(program: *const ir.Program) bool {
    for (program.blocks) |block| {
        if (!node_split.parametersAreCanonical(program.values, block)) return false;
    }
    return true;
}

fn scanProgram(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    only_function: ?usize,
) NormalizeError!Scan {
    var result: Scan = .{};
    errdefer result.deinit();
    for (program.functions, 0..) |function, function_index| {
        if (only_function) |selected_function| if (function_index != selected_function) continue;
        var graph = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
            error.InvalidCfg => continue,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer graph.deinit();
        var regions = try irreducible_region.analyze(allocator, &graph);
        defer regions.deinit();
        for (regions.regions) |region| {
            result.entry_measure += region.entries.len;
            if (result.plan == null) result.plan = try planRegion(allocator, program, &graph, function_index, region);
        }
    }
    return result;
}

fn irreducibleEntryMeasure(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    only_function: ?usize,
) NormalizeError!usize {
    var measure: usize = 0;
    for (program.functions, 0..) |function, function_index| {
        if (only_function) |selected_function| if (function_index != selected_function) continue;
        var graph = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
            error.InvalidCfg => continue,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer graph.deinit();
        var regions = try irreducible_region.analyze(allocator, &graph);
        defer regions.deinit();
        for (regions.regions) |region| measure += region.entries.len;
    }
    return measure;
}

fn planRegion(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    graph: *const cfg.Analysis,
    function_index: usize,
    region: irreducible_region.Region,
) NormalizeError!?SplitPlan {
    const selection = try irreducible_policy.selectPrimary(allocator, program, region);
    if (selection.refusal != null) return null;
    const primary = selection.block;

    for (region.entries) |entry| {
        if (entry.block == primary) continue;
        // Successor shape deliberately not refused; see `irreducible_policy.classifySecondary`.
        if (irreducible_policy.classifySecondarySource(program, entry) != null) continue;
        const closure = try cloneClosure(
            allocator,
            program,
            graph,
            region,
            primary,
            entry.block,
            entry.incoming,
        ) orelse continue;
        errdefer allocator.free(closure);
        const secondaries = try allocator.alloc(Secondary, 1);
        errdefer allocator.free(secondaries);
        secondaries[0] = .{
            .block = entry.block,
            .incoming = try allocator.dupe(ir.CfgEdgeRef, entry.incoming),
            .closure = closure,
        };
        return .{
            .allocator = allocator,
            .function_index = function_index,
            .secondaries = secondaries,
            .secondary_count = 1,
        };
    }
    return null;
}

fn cloneClosure(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    graph: *const cfg.Analysis,
    region: irreducible_region.Region,
    primary: ir.BlockId,
    secondary: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
) NormalizeError!?[]ir.BlockId {
    var found = try allocator.alloc(bool, program.blocks.len);
    defer allocator.free(found);
    @memset(found, false);
    var pending: std.ArrayList(ir.BlockId) = .empty;
    defer pending.deinit(allocator);
    var closure: std.ArrayList(ir.BlockId) = .empty;
    errdefer closure.deinit(allocator);
    if (secondary.index() >= program.blocks.len) return null;
    const source_function = program.blocks[secondary.index()].function;
    try pending.append(allocator, secondary);
    while (pending.pop()) |block_id| {
        if (block_id == primary or block_id.index() >= program.blocks.len or found[block_id.index()]) continue;
        const block = program.blocks[block_id.index()];
        if (!blockInRegion(region.blocks, block_id) and
            (block.function != source_function or block.parameters.len != 0)) continue;
        if (block.id != block_id or !node_split.parametersAreCanonical(program.values, block)) return null;
        found[block_id.index()] = true;
        try closure.append(allocator, block_id);
        const outgoing = successorTargets(block.terminator);
        for (outgoing.ids[0..outgoing.len]) |target| {
            if (target == primary or target.index() >= program.blocks.len) continue;
            if (blockInRegion(region.blocks, target)) {
                try pending.append(allocator, target);
                continue;
            }
            const target_block = program.blocks[target.index()];
            if (target_block.function == block.function and target_block.parameters.len == 0) {
                try pending.append(allocator, target);
            }
        }
    }
    if (closure.items.len == 0) return null;
    const initial_closure_len = closure.items.len;
    if (!try extendContinuationClosure(allocator, program, graph, primary, &closure)) return null;
    if (stage_trace.enabled) std.debug.print("normalize diagnostic clone-closure secondary={} primary={} primary_parameters={} before={} after={}\n", .{
        secondary.index(),
        primary.index(),
        program.blocks[primary.index()].parameters.len,
        initial_closure_len,
        closure.items.len,
    });
    if (!structural_overlap.prepareClosure(
        allocator,
        program,
        graph,
        closure.items,
        incoming,
    )) return null;
    return try closure.toOwnedSlice(allocator);
}

fn extendContinuationClosure(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    graph: *const cfg.Analysis,
    primary: ir.BlockId,
    closure: *std.ArrayList(ir.BlockId),
) NormalizeError!bool {
    if (primary.index() >= program.blocks.len or closure.items.len == 0) return false;
    const source_function = program.blocks[closure.items[0].index()].function;
    const primary_block = program.blocks[primary.index()];
    if (graph.function.id != source_function or primary_block.function != source_function) return true;

    var mapped_values: std.ArrayList(ir.ValueId) = .empty;
    defer mapped_values.deinit(allocator);
    var mapped_packs: std.ArrayList(ir.ValuePackId) = .empty;
    defer mapped_packs.deinit(allocator);
    for (closure.items) |block_id| {
        if (block_id.index() >= program.blocks.len) return false;
        const block = program.blocks[block_id.index()];
        if (block.id != block_id or block.function != source_function or
            !node_split.parametersAreCanonical(program.values, block)) return false;
        try appendSourceMappings(allocator, program, block, &mapped_values, &mapped_packs);
    }

    // A mapped value can be consumed after several parameterized blocks at a
    // shared continuation.  Discover the same-function continuation first,
    // then retain only blocks that can reach a mapped use.  The old local
    // direct-use check stopped at the first parameterized boundary and could
    // leave a clone-local SSA value live in the shared suffix.
    const candidate = try allocator.alloc(bool, program.blocks.len);
    defer allocator.free(candidate);
    @memset(candidate, false);
    const pending_blocks = try allocator.alloc(ir.BlockId, program.blocks.len);
    defer allocator.free(pending_blocks);
    var pending_len: usize = 1;
    pending_blocks[0] = primary;
    var pending_index: usize = 0;
    // The primary is part of the split closure even when it does not consume
    // a mapped value itself.  Its outgoing blocks may cross a parameterized
    // boundary where the mapped value is first used.
    candidate[primary.index()] = true;
    for (closure.items) |block_id| {
        if (block_id.index() >= program.blocks.len) return false;
        const outgoing = successorTargets(program.blocks[block_id.index()].terminator);
        for (outgoing.ids[0..outgoing.len]) |target| {
            if (target.index() >= program.blocks.len or
                candidate[target.index()] or
                blockInRegion(closure.items, target)) continue;
            if (pending_len >= pending_blocks.len) return false;
            candidate[target.index()] = true;
            pending_blocks[pending_len] = target;
            pending_len += 1;
        }
    }
    while (pending_index < pending_len) : (pending_index += 1) {
        const block_id = pending_blocks[pending_index];
        if (block_id.index() >= program.blocks.len or
            blockInRegion(closure.items, block_id)) continue;
        const block = program.blocks[block_id.index()];
        if (block.id != block_id or block.function != source_function) continue;
        const outgoing = successorTargets(block.terminator);
        for (outgoing.ids[0..outgoing.len]) |target| {
            if (target.index() >= program.blocks.len or
                candidate[target.index()] or
                blockInRegion(closure.items, target)) continue;
            if (pending_len >= pending_blocks.len) return false;
            candidate[target.index()] = true;
            pending_blocks[pending_len] = target;
            pending_len += 1;
        }
    }

    if (trace_normalize_phases and closure.items.len >= 20) {
        std.debug.print("normalize delayed-use candidate closure={} candidates={} mapped_values={} mapped_packs={}\n", .{
            closure.items.len,
            std.mem.countScalar(bool, candidate, true),
            mapped_values.items.len,
            mapped_packs.items.len,
        });
    }

    const needs = try allocator.alloc(bool, program.blocks.len);
    defer allocator.free(needs);
    @memset(needs, false);
    pending_len = 0;
    for (graph.function.blocks) |block_id| {
        if (block_id.index() >= program.blocks.len or !candidate[block_id.index()]) continue;
        const block = program.blocks[block_id.index()];
        if (!node_split.blockUsesMappedValues(program, block, mapped_values.items, mapped_packs.items)) continue;
        needs[block_id.index()] = true;
        if (pending_len >= pending_blocks.len) return false;
        pending_blocks[pending_len] = block_id;
        pending_len += 1;
    }
    var mapped_use_index: usize = 0;
    while (mapped_use_index < pending_len) : (mapped_use_index += 1) {
        const block_id = pending_blocks[mapped_use_index];
        var predecessor_index: usize = 0;
        while (graph.predecessorAt(block_id, predecessor_index)) |predecessor| : (predecessor_index += 1) {
            if (predecessor.index() >= program.blocks.len or
                !candidate[predecessor.index()] or
                needs[predecessor.index()]) continue;
            needs[predecessor.index()] = true;
            if (pending_len >= pending_blocks.len) return false;
            pending_blocks[pending_len] = predecessor;
            pending_len += 1;
        }
    }

    if (trace_normalize_phases and closure.items.len >= 20) {
        std.debug.print("normalize delayed-use needs closure={} blocks={}\n", .{
            closure.items.len,
            pending_len,
        });
    }

    var needs_extension = false;
    for (graph.function.blocks) |block_id| {
        if (block_id.index() < needs.len and needs[block_id.index()]) {
            needs_extension = true;
            break;
        }
    }
    if (!needs_extension) return true;
    // Once a mapped use requires an extension, retain the primary alongside
    // the mapped continuation.  No-use closures still take the original
    // no-op path and must not grow merely because a stop was supplied.
    needs[primary.index()] = true;

    var visited = try allocator.alloc(bool, program.blocks.len);
    defer allocator.free(visited);
    @memset(visited, false);
    var pending: std.ArrayList(ir.BlockId) = .empty;
    defer pending.deinit(allocator);
    var continuation: std.ArrayList(ir.BlockId) = .empty;
    defer continuation.deinit(allocator);
    try pending.append(allocator, primary);
    for (closure.items) |block_id| {
        if (block_id.index() >= program.blocks.len) return false;
        const outgoing = successorTargets(program.blocks[block_id.index()].terminator);
        for (outgoing.ids[0..outgoing.len]) |target| {
            if (target.index() >= program.blocks.len or blockInRegion(closure.items, target)) continue;
            try pending.append(allocator, target);
        }
    }

    while (pending.pop()) |block_id| {
        if (block_id.index() >= program.blocks.len or visited[block_id.index()] or
            blockInRegion(closure.items, block_id) or
            !needs[block_id.index()]) continue;
        const block = program.blocks[block_id.index()];
        if (block.id != block_id or block.function != source_function or
            !node_split.parametersAreCanonical(program.values, block)) return false;
        visited[block_id.index()] = true;
        try continuation.append(allocator, block_id);
        const outgoing = successorTargets(block.terminator);
        for (outgoing.ids[0..outgoing.len]) |target| {
            if (target.index() >= program.blocks.len or
                blockInRegion(closure.items, target) or
                !needs[target.index()]) continue;
            try pending.append(allocator, target);
        }
    }

    try closure.appendSlice(allocator, continuation.items);
    return true;
}

fn appendSourceMappings(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    block: ir.Block,
    values: *std.ArrayList(ir.ValueId),
    packs: *std.ArrayList(ir.ValuePackId),
) NormalizeError!void {
    try values.appendSlice(allocator, block.parameters);
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return error.NormalizationInvariantFailed;
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.id != instruction_id or instruction.block != block.id) return error.NormalizationInvariantFailed;
        try values.appendSlice(allocator, instruction.results);
        if (instruction.pack_result) |pack_id| try packs.append(allocator, pack_id);
    }
}

const SuccessorTargets = struct {
    ids: [2]ir.BlockId = undefined,
    len: usize = 0,
};

fn successorTargets(terminator: ir.Terminator) SuccessorTargets {
    var result: SuccessorTargets = .{};
    switch (terminator) {
        .jump => |edge| {
            result.ids[0] = edge.target;
            result.len = 1;
        },
        .branch => |branch| {
            result.ids[0] = branch.then_edge.target;
            result.ids[1] = branch.else_edge.target;
            result.len = 2;
        },
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
    }
    return result;
}

fn blockInRegion(region: []const ir.BlockId, candidate: ir.BlockId) bool {
    for (region) |block| if (block == candidate) return true;
    return false;
}

fn applyPlan(
    allocator: std.mem.Allocator,
    program: *ir.Program,
    blocks: *std.ArrayList(ir.Block),
    functions: *std.ArrayList(ir.Function),
    instructions: *std.ArrayList(ir.Instruction),
    values: *std.ArrayList(ir.Value),
    packs: *std.ArrayList(ir.ValuePack),
    rewrites: *std.ArrayList(ir.CfgEdgeRewrite),
    plan: *const SplitPlan,
    result: *Result,
) NormalizeError!void {
    if (plan.function_index >= functions.items.len) {
        return error.NormalizationInvariantFailed;
    }
    const function = &functions.items[plan.function_index];
    const secondaries = plan.secondaries[0..plan.secondary_count];
    const apply_start = normalizePhaseNow();
    const initial_program = program.*;
    const initial_block_count = blocks.items.len;
    const initial_function_blocks = function.blocks;
    const initial_instruction_count = instructions.items.len;
    const initial_value_count = values.items.len;
    const initial_pack_count = packs.items.len;
    const initial_rewrite_count = rewrites.items.len;
    const initial_result = result.*;
    var clone_count: usize = 0;
    for (secondaries) |secondary| clone_count = std.math.add(usize, clone_count, secondary.closure.len) catch
        return error.NormalizationInvariantFailed;
    const expanded_blocks = try allocator.alloc(ir.BlockId, function.blocks.len + clone_count);
    errdefer allocator.free(expanded_blocks);
    const block_snapshot = try allocator.dupe(ir.Block, blocks.items);
    defer allocator.free(block_snapshot);
    var committed = false;
    errdefer if (!committed) {
        blocks.shrinkRetainingCapacity(initial_block_count);
        @memcpy(blocks.items, block_snapshot);
        functions.items[plan.function_index].blocks = initial_function_blocks;
        instructions.shrinkRetainingCapacity(initial_instruction_count);
        values.shrinkRetainingCapacity(initial_value_count);
        packs.shrinkRetainingCapacity(initial_pack_count);
        rewrites.shrinkRetainingCapacity(initial_rewrite_count);
        program.* = initial_program;
        program.blocks = blocks.items;
        program.functions = functions.items;
        program.instructions = instructions.items;
        program.values = values.items;
        program.value_packs = packs.items;
        program.edge_rewrites = rewrites.items;
        result.* = initial_result;
    };
    @memcpy(expanded_blocks[0..function.blocks.len], function.blocks);
    var expanded_index = function.blocks.len;

    program.blocks = blocks.items;
    program.functions = functions.items;
    program.instructions = instructions.items;
    program.values = values.items;
    program.value_packs = packs.items;
    program.edge_rewrites = rewrites.items;

    // All secondary mappings must be authenticated against one immutable
    // graph snapshot. Applying one incoming edge first can make the remaining
    // edge references invalid until the function block list is published.
    const prepared = try allocator.alloc(PreparedSecondary, secondaries.len);
    var prepared_count: usize = 0;
    defer {
        for (prepared[0..prepared_count]) |*item| item.external.deinit();
        allocator.free(prepared);
    }
    var snapshot_analysis = cfg.Analysis.init(allocator, program, functions.items[plan.function_index]) catch |err| switch (err) {
        error.InvalidCfg => return error.NormalizationInvariantFailed,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer snapshot_analysis.deinit();
    for (secondaries) |secondary| {
        const external = (structural_overlap.collectExternalCloneMappingsAlloc(
            allocator,
            program,
            &snapshot_analysis,
            secondary.closure,
            secondary.incoming,
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
        }) orelse {
            return error.NormalizationInvariantFailed;
        };
        prepared[prepared_count] = .{ .external = external };
        prepared_count += 1;
    }

    for (secondaries, 0..) |secondary, secondary_index| {
        if (secondary.block.index() >= blocks.items.len) {
            return error.NormalizationInvariantFailed;
        }
        const node_split_group = ir.NodeSplitGroupId.fromIndex(rewrites.items.len);
        const source_block = blocks.items[secondary.block.index()];
        const clones = try allocator.alloc(ir.BlockId, secondary.closure.len);
        defer allocator.free(clones);
        const external = prepared[secondary_index].external;
        var mapped_source_values: std.ArrayList(ir.ValueId) = .empty;
        defer mapped_source_values.deinit(allocator);
        var mapped_clone_values: std.ArrayList(ir.ValueId) = .empty;
        defer mapped_clone_values.deinit(allocator);
        var mapped_source_packs: std.ArrayList(ir.ValuePackId) = .empty;
        defer mapped_source_packs.deinit(allocator);
        var mapped_clone_packs: std.ArrayList(ir.ValuePackId) = .empty;
        defer mapped_clone_packs.deinit(allocator);
        try mapped_source_values.appendSlice(allocator, external.values);
        try mapped_clone_values.appendSlice(allocator, external.clone_values);
        try mapped_source_packs.appendSlice(allocator, external.packs);
        try mapped_clone_packs.appendSlice(allocator, external.clone_packs);
        const clone_start = normalizePhaseNow();
        for (secondary.closure, 0..) |source_id, closure_index| {
            if (trace_normalize_phases and secondary.closure.len >= 128 and closure_index % 512 == 0) {
                std.debug.print("normalize_phase clone_progress function={} entry={} index={} total={} ms={} blocks={} instructions={}\\n", .{
                    plan.function_index,
                    secondary.block.index(),
                    closure_index,
                    secondary.closure.len,
                    normalizePhaseMillis(clone_start),
                    blocks.items.len,
                    instructions.items.len,
                });
            }
            if (source_id.index() >= blocks.items.len) return error.NormalizationInvariantFailed;
            const clone_id = ir.BlockId.fromIndex(blocks.items.len);
            const cloned = node_split.cloneBlockWithMappingsInArena(
                allocator,
                program,
                instructions,
                values,
                packs,
                blocks.items[source_id.index()],
                clone_id,
                mapped_source_values.items,
                mapped_clone_values.items,
                mapped_source_packs.items,
                mapped_clone_packs.items,
            ) catch |err| switch (err) {
                error.InvalidNodeSplitSource => {
                    return error.NormalizationInvariantFailed;
                },
                error.OutOfMemory => return error.OutOfMemory,
            };
            try blocks.append(allocator, cloned.block);
            clones[closure_index] = clone_id;
            expanded_blocks[expanded_index] = clone_id;
            expanded_index += 1;
            result.cloned_blocks += 1;
            result.cloned_values += cloned.cloned_values;
            result.cloned_packs += cloned.cloned_packs;
            result.cloned_instructions += cloned.cloned_instructions;
            program.blocks = blocks.items;
            program.instructions = instructions.items;
            program.values = values.items;
            program.value_packs = packs.items;
            try appendCloneMappings(
                allocator,
                program,
                blocks.items[source_id.index()],
                cloned.block,
                &mapped_source_values,
                &mapped_clone_values,
                &mapped_source_packs,
                &mapped_clone_packs,
            );
        }
        const clone_ms = normalizePhaseMillis(clone_start);
        const edge_start = normalizePhaseNow();
        for (secondary.closure, clones) |source_id, clone_id| {
            result.rewritten_edges += try rewriteClonedClosureEdges(
                allocator,
                program,
                blocks,
                rewrites,
                secondary.closure,
                clones,
                mapped_source_values.items,
                mapped_clone_values.items,
                node_split_group,
                source_id,
                clone_id,
                block_snapshot,
                &snapshot_analysis,
            );
        }
        const edge_ms = normalizePhaseMillis(edge_start);
        const secondary_clone = mappedClone(secondary.closure, clones, secondary.block) orelse {
            return error.NormalizationInvariantFailed;
        };

        const incoming_start = normalizePhaseNow();
        for (secondary.incoming) |reference| {
            const incoming = cfg_edge.value(program, reference) orelse {
                return error.NormalizationInvariantFailed;
            };
            if (incoming.target != secondary.block or incoming.arguments.len != source_block.parameters.len) {
                return error.NormalizationInvariantFailed;
            }
            const from_arguments = try allocator.dupe(ir.ValueId, incoming.arguments);
            const to_arguments = try allocator.dupe(ir.ValueId, incoming.arguments);
            if (!redirectEdge(&blocks.items[reference.source.index()], reference, secondary_clone, to_arguments)) {
                return error.NormalizationInvariantFailed;
            }
            try rewrites.append(allocator, .{
                .id = ir.EdgeRewriteId.fromIndex(rewrites.items.len),
                .source = reference.source,
                .kind = reference.kind,
                .from = .{ .target = secondary.block, .arguments = from_arguments },
                .to = .{ .target = secondary_clone, .arguments = to_arguments },
                .rule = .node_split,
                .node_split_group = node_split_group,
            });
            result.rewritten_edges += 1;
            program.edge_rewrites = rewrites.items;

            // Clone publication and the preceding incoming redirects mutate
            // the dominance graph.  Rebuild the proof view from the current
            // function membership before forwarding any successor tuple;
            // the immutable snapshot above is only for clone preparation.
            function.blocks = expanded_blocks[0..expanded_index];
            program.functions = functions.items;
            result.rewritten_edges += try forwardClonedIterationEntry(
                allocator,
                program,
                blocks,
                rewrites,
                function.*,
                reference.source,
                reference.kind,
                secondary_clone,
            );
        }
        const incoming_ms = normalizePhaseMillis(incoming_start);
        if (trace_normalize_phases and secondary.closure.len >= 128) {
            std.debug.print("normalize_phase apply function={} entry={} closure={} clone_ms={} edge_ms={} incoming_ms={} total_ms={} blocks={} instructions={} values={}\\n", .{
                plan.function_index,
                secondary.block.index(),
                secondary.closure.len,
                clone_ms,
                edge_ms,
                incoming_ms,
                normalizePhaseMillis(apply_start),
                blocks.items.len,
                instructions.items.len,
                values.items.len,
            });
        }
    }
    if (expanded_index != expanded_blocks.len) {
        return error.NormalizationInvariantFailed;
    }
    function.blocks = expanded_blocks;
    program.blocks = blocks.items;
    program.functions = functions.items;
    program.instructions = instructions.items;
    program.values = values.items;
    program.value_packs = packs.items;
    program.edge_rewrites = rewrites.items;
    var availability_analysis = cfg.Analysis.init(allocator, program, function.*) catch |err| switch (err) {
        error.InvalidCfg => return error.NormalizationInvariantFailed,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer availability_analysis.deinit();
    if (!(try clone_availability.functionUsesAreAvailable(allocator, program, &availability_analysis))) {
        if (stage_trace.enabled) std.debug.print("normalize diagnostic clone-availability-plan function={} secondaries={} blocks={} rewrites={}\n", .{
            plan.function_index,
            secondaries.len,
            blocks.items.len,
            rewrites.items.len,
        });
        for (secondaries, 0..) |secondary, index| {
            if (stage_trace.enabled) std.debug.print("normalize diagnostic clone-availability-secondary index={} entry={} closure={any} incoming={any}\n", .{
                index,
                secondary.block.index(),
                secondary.closure,
                secondary.incoming,
            });
        }
        std.debug.print("normalize failure phase=clone-availability function={} blocks={} rewrites={}\n", .{
            function.id.index(),
            function.blocks.len,
            rewrites.items.len,
        });
        return error.NormalizationInvariantFailed;
    }
    committed = true;
}

fn appendCloneMappings(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source: ir.Block,
    clone: ir.Block,
    source_values: *std.ArrayList(ir.ValueId),
    clone_values: *std.ArrayList(ir.ValueId),
    source_packs: *std.ArrayList(ir.ValuePackId),
    clone_packs: *std.ArrayList(ir.ValuePackId),
) NormalizeError!void {
    if (source.parameters.len != clone.parameters.len or source.instructions.len != clone.instructions.len) {
        return error.NormalizationInvariantFailed;
    }
    try source_values.appendSlice(allocator, source.parameters);
    try clone_values.appendSlice(allocator, clone.parameters);
    for (source.instructions, clone.instructions) |source_id, clone_id| {
        if (source_id.index() >= program.instructions.len or clone_id.index() >= program.instructions.len) {
            return error.NormalizationInvariantFailed;
        }
        const source_instruction = program.instructions[source_id.index()];
        const clone_instruction = program.instructions[clone_id.index()];
        if (source_instruction.id != source_id or clone_instruction.id != clone_id or
            source_instruction.results.len != clone_instruction.results.len or
            (source_instruction.pack_result == null) != (clone_instruction.pack_result == null))
        {
            return error.NormalizationInvariantFailed;
        }
        try source_values.appendSlice(allocator, source_instruction.results);
        try clone_values.appendSlice(allocator, clone_instruction.results);
        if (source_instruction.pack_result) |pack_id| {
            try source_packs.append(allocator, pack_id);
            try clone_packs.append(allocator, clone_instruction.pack_result.?);
        }
    }
}

fn mappedClone(source: []const ir.BlockId, clones: []const ir.BlockId, target: ir.BlockId) ?ir.BlockId {
    for (source, clones) |candidate, clone| if (candidate == target) return clone;
    return null;
}

fn rewriteClonedClosureEdges(
    allocator: std.mem.Allocator,
    program: *ir.Program,
    blocks: *std.ArrayList(ir.Block),
    rewrites: *std.ArrayList(ir.CfgEdgeRewrite),
    source_blocks: []const ir.BlockId,
    clone_blocks: []const ir.BlockId,
    mapped_source_values: []const ir.ValueId,
    mapped_clone_values: []const ir.ValueId,
    node_split_group: ir.NodeSplitGroupId,
    source_id: ir.BlockId,
    clone_id: ir.BlockId,
    source_blocks_snapshot: []const ir.Block,
    source_analysis: *const cfg.Analysis,
) NormalizeError!usize {
    if (source_id.index() >= source_blocks_snapshot.len or clone_id.index() >= blocks.items.len) return error.NormalizationInvariantFailed;
    const source = source_blocks_snapshot[source_id.index()];
    var changed: usize = 0;
    switch (source.terminator) {
        .jump => |edge| changed += try rewriteClonedClosureEdge(
            allocator,
            program,
            blocks,
            rewrites,
            source_blocks,
            clone_blocks,
            mapped_source_values,
            mapped_clone_values,
            node_split_group,
            source_id,
            clone_id,
            .jump,
            edge.target,
            edge,
            source_analysis,
        ),
        .branch => |branch| {
            changed += try rewriteClonedClosureEdge(
                allocator,
                program,
                blocks,
                rewrites,
                source_blocks,
                clone_blocks,
                mapped_source_values,
                mapped_clone_values,
                node_split_group,
                source_id,
                clone_id,
                .branch_then,
                branch.then_edge.target,
                branch.then_edge,
                source_analysis,
            );
            changed += try rewriteClonedClosureEdge(
                allocator,
                program,
                blocks,
                rewrites,
                source_blocks,
                clone_blocks,
                mapped_source_values,
                mapped_clone_values,
                node_split_group,
                source_id,
                clone_id,
                .branch_else,
                branch.else_edge.target,
                branch.else_edge,
                source_analysis,
            );
        },
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
    }
    return changed;
}

fn rewriteClonedClosureEdge(
    allocator: std.mem.Allocator,
    program: *ir.Program,
    blocks: *std.ArrayList(ir.Block),
    rewrites: *std.ArrayList(ir.CfgEdgeRewrite),
    source_blocks: []const ir.BlockId,
    clone_blocks: []const ir.BlockId,
    mapped_source_values: []const ir.ValueId,
    mapped_clone_values: []const ir.ValueId,
    node_split_group: ir.NodeSplitGroupId,
    source_id: ir.BlockId,
    clone_id: ir.BlockId,
    kind: ir.CfgEdgeKind,
    source_target: ir.BlockId,
    source_edge: ir.Edge,
    source_analysis: *const cfg.Analysis,
) NormalizeError!usize {
    const clone_target = mappedClone(source_blocks, clone_blocks, source_target) orelse return 0;
    if (source_id.index() >= blocks.items.len or clone_id.index() >= blocks.items.len or
        source_target.index() >= blocks.items.len or clone_target.index() >= blocks.items.len)
    {
        return error.NormalizationInvariantFailed;
    }
    const source_block = blocks.items[source_id.index()];
    if (source_block.id != source_id or source_block.function != source_analysis.function.id or
        source_edge.target != source_target or
        !edgeArgumentsAvailableAtSource(program, source_analysis, source_id, source_edge.arguments))
    {
        return error.NormalizationInvariantFailed;
    }
    if (source_target == source_id and clone_target == clone_id) return 0;
    const reference: ir.CfgEdgeRef = .{ .source = clone_id, .kind = kind, .target = source_target };
    const incoming = cfg_edge.value(program, reference) orelse return error.NormalizationInvariantFailed;
    const target_block = blocks.items[source_target.index()];
    const clone_target_block = blocks.items[clone_target.index()];
    if (target_block.id != source_target or clone_target_block.id != clone_target or
        target_block.function != source_block.function or clone_target_block.function != source_block.function or
        incoming.arguments.len != source_edge.arguments.len or
        clone_target_block.parameters.len != target_block.parameters.len)
    {
        return error.NormalizationInvariantFailed;
    }
    for (source_edge.arguments, incoming.arguments) |source_argument, incoming_argument| {
        if (remapValueFromMappings(source_argument, mapped_source_values, mapped_clone_values) != incoming_argument) {
            return error.NormalizationInvariantFailed;
        }
    }
    const from_arguments = try allocator.dupe(ir.ValueId, incoming.arguments);
    const to_arguments = try remapEdgeArgumentsAlloc(
        allocator,
        source_edge.arguments,
        mapped_source_values,
        mapped_clone_values,
    );
    if (!redirectEdge(&blocks.items[clone_id.index()], reference, clone_target, to_arguments)) return error.NormalizationInvariantFailed;
    try rewrites.append(allocator, .{
        .id = ir.EdgeRewriteId.fromIndex(rewrites.items.len),
        .source = clone_id,
        .kind = kind,
        .from = .{ .target = source_target, .arguments = from_arguments },
        .to = .{ .target = clone_target, .arguments = to_arguments },
        .rule = .node_split,
        .node_split_group = node_split_group,
    });
    program.blocks = blocks.items;
    program.edge_rewrites = rewrites.items;
    return 1;
}

fn forwardClonedIterationEntry(
    allocator: std.mem.Allocator,
    program: *ir.Program,
    blocks: *std.ArrayList(ir.Block),
    rewrites: *std.ArrayList(ir.CfgEdgeRewrite),
    function: ir.Function,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    clone_id: ir.BlockId,
) !usize {
    var analysis = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
        error.InvalidCfg => return error.NormalizationInvariantFailed,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    const reference: ir.CfgEdgeRef = .{ .source = source, .kind = kind, .target = clone_id };
    const incoming = cfg_edge.value(program, reference) orelse return 0;
    if (incoming.target != clone_id) return 0;

    var path: std.ArrayList(ir.Edge) = .empty;
    defer {
        for (path.items) |edge| if (edge.arguments.len != 0) allocator.free(edge.arguments);
        path.deinit(allocator);
    }
    var current = incoming;
    while (path.items.len < program.blocks.len) {
        const forwarded = try control_flow.replayForwardingJump(allocator, program, current) orelse return 0;
        if (forwarded.target == source or
            forwardingTargetWasVisited(rewrites.items, source, kind, forwarded.target) or
            pathContainsTarget(incoming.target, path.items, forwarded.target) or
            forwarded.target.index() >= program.blocks.len)
        {
            if (forwarded.arguments.len != 0) allocator.free(forwarded.arguments);
            return 0;
        }
        try path.append(allocator, forwarded);
        const target = program.blocks[forwarded.target.index()];
        if (iteration_protocol.transitionForHeader(program, target) != null) break;
        current = forwarded;
    }
    if (path.items.len == 0 or path.items.len >= program.blocks.len) return 0;
    const final = path.items[path.items.len - 1];
    if (final.target.index() >= program.blocks.len or
        iteration_protocol.transitionForHeader(program, program.blocks[final.target.index()]) == null)
    {
        return 0;
    }
    // The forwarding block may carry values that are valid only because the
    // forwarding block is reached from a narrower context.  Substituting its
    // final tuple directly into the original source edge is sound only when
    // every value is already available at that source.  Keep the forwarding
    // path explicit otherwise; its intermediate block owns that context.
    if (!edgeArgumentsAvailableAtSource(program, &analysis, source, final.arguments)) return 0;

    current = incoming;
    for (path.items) |forwarded| {
        try rewrites.append(allocator, .{
            .id = ir.EdgeRewriteId.fromIndex(rewrites.items.len),
            .source = source,
            .kind = kind,
            .from = .{
                .target = current.target,
                .arguments = try allocator.dupe(ir.ValueId, current.arguments),
            },
            .to = .{
                .target = forwarded.target,
                .arguments = try allocator.dupe(ir.ValueId, forwarded.arguments),
            },
            .rule = .forwarding_jump,
        });
        current = forwarded;
    }
    if (!replaceEdge(&blocks.items[source.index()], kind, incoming, final)) return error.NormalizationInvariantFailed;
    for (path.items[0 .. path.items.len - 1]) |*edge| {
        if (edge.arguments.len != 0) allocator.free(edge.arguments);
        edge.arguments = &.{};
    }
    path.items[path.items.len - 1].arguments = &.{};
    program.blocks = blocks.items;
    program.edge_rewrites = rewrites.items;
    return path.items.len;
}

fn edgeArgumentsAvailableAtSource(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.BlockId,
    arguments: []const ir.ValueId,
) bool {
    if (source.index() >= program.blocks.len or
        analysis.blockIndex(source) == null or
        !analysis.isReachable(source)) return false;
    const source_block = program.blocks[source.index()];
    if (source_block.id != source or source_block.function != analysis.function.id) return false;

    for (arguments) |value_id| {
        if (value_id.index() >= program.values.len) return false;
        const value = program.values[value_id.index()];
        if (value.id != value_id or value.function != source_block.function) return false;
        switch (value.origin) {
            .parameter, .capture => {},
            .block_parameter => |origin| {
                if (origin.block == source) continue;
                if (!analysis.dominates(origin.block, source)) return false;
            },
            .instruction_result => |origin| {
                if (origin.instruction.index() >= program.instructions.len) return false;
                const definition = program.instructions[origin.instruction.index()];
                if (definition.id != origin.instruction or
                    definition.block.index() >= program.blocks.len or
                    origin.index >= definition.results.len)
                {
                    return false;
                }
                const definition_block = program.blocks[definition.block.index()];
                if (definition_block.id != definition.block or
                    definition_block.function != source_block.function)
                {
                    return false;
                }
                if (definition.block == source) {
                    var found = false;
                    for (source_block.instructions) |instruction_id| {
                        if (instruction_id == origin.instruction) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) return false;
                } else if (!analysis.dominates(definition.block, source)) {
                    return false;
                }
            },
        }
    }
    return true;
}

test "forwarded iteration entry requires source-available successor arguments" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const foreign = ir.BlockId.fromIndex(1);
    const source = ir.BlockId.fromIndex(2);
    const clone = ir.BlockId.fromIndex(3);
    const header = ir.BlockId.fromIndex(4);
    const exit = ir.BlockId.fromIndex(5);

    const selector = ir.ValueId.fromIndex(0);
    const payload = ir.ValueId.fromIndex(1);
    const foreign_value = ir.ValueId.fromIndex(2);
    const clone_values = [_]ir.ValueId{
        ir.ValueId.fromIndex(3),
        ir.ValueId.fromIndex(4),
        ir.ValueId.fromIndex(5),
        ir.ValueId.fromIndex(6),
    };
    const header_values = [_]ir.ValueId{
        ir.ValueId.fromIndex(7),
        ir.ValueId.fromIndex(8),
        ir.ValueId.fromIndex(9),
        ir.ValueId.fromIndex(10),
    };
    const transition_results = [_]ir.ValueId{
        ir.ValueId.fromIndex(11),
        ir.ValueId.fromIndex(12),
        ir.ValueId.fromIndex(13),
        ir.ValueId.fromIndex(14),
    };
    const transition_id = ir.InstructionId.fromIndex(0);
    const positive_source_arguments = [_]ir.ValueId{ foreign_value, payload, payload, payload };
    const negative_source_arguments = [_]ir.ValueId{ foreign_value, payload, payload, payload };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = foreign, .arguments = &.{payload} },
            .else_edge = .{ .target = foreign, .arguments = &.{payload} },
        } } },
        .{ .id = foreign, .function = function_id, .parameters = &.{foreign_value}, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{
            .target = clone,
            .arguments = &positive_source_arguments,
        } } },
        .{ .id = clone, .function = function_id, .parameters = &clone_values, .terminator = .{ .jump = .{
            .target = header,
            .arguments = &clone_values,
        } } },
        .{ .id = header, .function = function_id, .parameters = &header_values, .instructions = &.{transition_id}, .terminator = .{ .branch = .{
            .condition = transition_results[0],
            .then_edge = .{ .target = exit },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ selector, payload },
        .blocks = &.{ entry, foreign, source, clone, header, exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = payload, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = foreign_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = foreign, .index = 0 } } },
        .{ .id = clone_values[0], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 0 } } },
        .{ .id = clone_values[1], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 1 } } },
        .{ .id = clone_values[2], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 2 } } },
        .{ .id = clone_values[3], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 3 } } },
        .{ .id = header_values[0], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
        .{ .id = header_values[1], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = header, .index = 1 } } },
        .{ .id = header_values[2], .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = header, .index = 2 } } },
        .{ .id = header_values[3], .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = header, .index = 3 } } },
        .{ .id = transition_results[0], .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 0 } } },
        .{ .id = transition_results[1], .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 1 } } },
        .{ .id = transition_results[2], .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 2 } } },
        .{ .id = transition_results[3], .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 3 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = transition_id,
        .block = header,
        .operation = .{ .numeric_for_next = .{
            .control = header_values[0],
            .limit = header_values[1],
            .step = header_values[2],
            .initial = header_values[3],
            .mode = .semantic_normalized,
        } },
        .results = &transition_results,
        .effects = .numeric_for_next,
    }};

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const work = arena.allocator();
    var block_list: std.ArrayList(ir.Block) = .empty;
    try block_list.appendSlice(work, &blocks);
    var rewrite_list: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    var program = ir.Program{
        .program_id = "forwarded-iteration-entry-availability",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = block_list.items,
        .instructions = &instructions,
        .values = &values,
        .edge_rewrites = rewrite_list.items,
    };
    try std.testing.expectEqual(@as(usize, 1), try forwardClonedIterationEntry(
        work,
        &program,
        &block_list,
        &rewrite_list,
        function,
        source,
        .jump,
        clone,
    ));
    try std.testing.expectEqual(header, program.blocks[source.index()].terminator.jump.target);
    try std.testing.expectEqual(@as(usize, 1), rewrite_list.items.len);
    try std.testing.expectEqualSlices(
        ir.ValueId,
        positive_source_arguments[0..],
        rewrite_list.items[0].to.arguments,
    );

    // Bypass the defining block after the first successful call.  A stale
    // dominance snapshot would still accept foreign_value here.
    block_list.items[entry.index()].terminator = .{ .branch = .{
        .condition = selector,
        .then_edge = .{ .target = foreign, .arguments = &.{payload} },
        .else_edge = .{ .target = source },
    } };
    block_list.items[source.index()].terminator = .{ .jump = .{
        .target = clone,
        .arguments = &negative_source_arguments,
    } };
    rewrite_list.clearRetainingCapacity();
    program.blocks = block_list.items;
    program.edge_rewrites = rewrite_list.items;
    try std.testing.expectEqual(@as(usize, 0), try forwardClonedIterationEntry(
        work,
        &program,
        &block_list,
        &rewrite_list,
        function,
        source,
        .jump,
        clone,
    ));
    try std.testing.expectEqual(clone, program.blocks[source.index()].terminator.jump.target);
    try std.testing.expectEqual(@as(usize, 0), rewrite_list.items.len);
}

test "cloned closure edge remaps the immutable source tuple once" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const source_target = ir.BlockId.fromIndex(3);
    const clone_target = ir.BlockId.fromIndex(4);
    const exit = ir.BlockId.fromIndex(5);
    const condition = ir.ValueId.fromIndex(0);
    const external_source = ir.ValueId.fromIndex(1);
    const external_clone = ir.ValueId.fromIndex(2);
    const local_clone = ir.ValueId.fromIndex(3);
    const source_target_parameter = ir.ValueId.fromIndex(4);
    const clone_target_parameter = ir.ValueId.fromIndex(5);

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = source },
            .else_edge = .{ .target = clone },
        } } },
        .{ .id = source, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = source_target, .arguments = &.{external_source} },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = clone, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = source_target, .arguments = &.{external_clone} },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = source_target, .function = function_id, .parameters = &.{source_target_parameter}, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = clone_target, .function = function_id, .parameters = &.{clone_target_parameter}, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ condition, external_source, external_clone, local_clone },
        .blocks = &.{ entry, source, clone, source_target, clone_target, exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = external_source, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = external_clone, .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = local_clone, .function = function_id, .type = .integer, .origin = .{ .parameter = 3 } },
        .{ .id = source_target_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_target, .index = 0 } } },
        .{ .id = clone_target_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone_target, .index = 0 } } },
    };

    var block_list: std.ArrayList(ir.Block) = .empty;
    defer block_list.deinit(std.testing.allocator);
    try block_list.appendSlice(std.testing.allocator, &blocks);
    var rewrite_list: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    defer rewrite_list.deinit(std.testing.allocator);
    defer if (rewrite_list.items.len != 0) {
        std.testing.allocator.free(rewrite_list.items[0].from.arguments);
        std.testing.allocator.free(rewrite_list.items[0].to.arguments);
    };
    var program = ir.Program{
        .program_id = "clone-edge-source-tuple",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = block_list.items,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = rewrite_list.items,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();

    const source_edge = blocks[source.index()].terminator.branch.then_edge;
    const remapped_source_values = [_]ir.ValueId{ external_source, external_clone };
    const remapped_clone_values = [_]ir.ValueId{ external_clone, local_clone };
    try std.testing.expectEqual(@as(usize, 1), try rewriteClonedClosureEdge(
        std.testing.allocator,
        &program,
        &block_list,
        &rewrite_list,
        &.{ source, source_target },
        &.{ clone, clone_target },
        &remapped_source_values,
        &remapped_clone_values,
        ir.NodeSplitGroupId.fromIndex(0),
        source,
        clone,
        .branch_then,
        source_target,
        source_edge,
        &analysis,
    ));

    const rewritten_edge = program.blocks[clone.index()].terminator.branch.then_edge;
    try std.testing.expectEqual(clone_target, rewritten_edge.target);
    try std.testing.expectEqualSlices(ir.ValueId, &.{external_clone}, rewritten_edge.arguments);
    try std.testing.expectEqualSlices(ir.ValueId, &.{external_clone}, rewrite_list.items[0].from.arguments);
    try std.testing.expectEqualSlices(ir.ValueId, &.{external_clone}, rewrite_list.items[0].to.arguments);
}

fn pathContainsTarget(initial: ir.BlockId, path: []const ir.Edge, target: ir.BlockId) bool {
    if (target == initial) return true;
    for (path) |edge| if (edge.target == target) return true;
    return false;
}

fn forwardingTargetWasVisited(
    rewrites: []const ir.CfgEdgeRewrite,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    target: ir.BlockId,
) bool {
    for (rewrites) |rewrite| {
        if (rewrite.source != source or rewrite.kind != kind) continue;
        if (rewrite.from.target == target or rewrite.to.target == target) return true;
    }
    return false;
}

fn replaceEdge(block: *ir.Block, kind: ir.CfgEdgeKind, expected: ir.Edge, replacement: ir.Edge) bool {
    switch (block.terminator) {
        .jump => |edge| {
            if (kind != .jump or !sameEdge(edge, expected)) return false;
            block.terminator = .{ .jump = replacement };
        },
        .branch => |branch| {
            var changed = branch;
            switch (kind) {
                .branch_then => {
                    if (!sameEdge(branch.then_edge, expected)) return false;
                    changed.then_edge = replacement;
                },
                .branch_else => {
                    if (!sameEdge(branch.else_edge, expected)) return false;
                    changed.else_edge = replacement;
                },
                .jump => return false,
            }
            block.terminator = .{ .branch = changed };
        },
        else => return false,
    }
    return true;
}

fn sameEdge(left: ir.Edge, right: ir.Edge) bool {
    return left.target == right.target and std.mem.eql(ir.ValueId, left.arguments, right.arguments);
}

fn remapEdgeArgumentsAlloc(
    allocator: std.mem.Allocator,
    arguments: []const ir.ValueId,
    source_values: []const ir.ValueId,
    clone_values: []const ir.ValueId,
) NormalizeError![]const ir.ValueId {
    if (source_values.len != clone_values.len) return error.NormalizationInvariantFailed;
    if (arguments.len == 0) return &.{};
    const mapped = try allocator.alloc(ir.ValueId, arguments.len);
    for (arguments, 0..) |argument, index| mapped[index] = remapValueFromMappings(argument, source_values, clone_values);
    return mapped;
}

fn remapValueFromMappings(
    value: ir.ValueId,
    source_values: []const ir.ValueId,
    clone_values: []const ir.ValueId,
) ir.ValueId {
    for (source_values, clone_values) |source, clone| if (value == source) return clone;
    return value;
}

fn redirectEdge(
    block: *ir.Block,
    reference: ir.CfgEdgeRef,
    target: ir.BlockId,
    arguments: []const ir.ValueId,
) bool {
    if (block.id != reference.source) return false;
    switch (block.terminator) {
        .jump => |edge| {
            if (reference.kind != .jump or edge.target != reference.target) return false;
            var redirected = edge;
            redirected.target = target;
            redirected.arguments = arguments;
            block.terminator = .{ .jump = redirected };
        },
        .branch => |branch| {
            var redirected = branch;
            switch (reference.kind) {
                .branch_then => {
                    if (branch.then_edge.target != reference.target) return false;
                    redirected.then_edge.target = target;
                    redirected.then_edge.arguments = arguments;
                },
                .branch_else => {
                    if (branch.else_edge.target != reference.target) return false;
                    redirected.else_edge.target = target;
                    redirected.else_edge.arguments = arguments;
                },
                .jump => return false,
            }
            block.terminator = .{ .branch = redirected };
        },
        else => return false,
    }
    return true;
}

// A clone fold changes the live control-flow graph without creating a new
// block or value.  Recheck availability on the redirected graph before the
// fold is published; otherwise a valid clone-equivalence proof can still
// erase the only dominating producer of a later use.
fn redirectEdgeWithDominancePreflight(
    allocator: std.mem.Allocator,
    program: *ir.Program,
    blocks: []ir.Block,
    function_id: ir.FunctionId,
    block: *ir.Block,
    reference: ir.CfgEdgeRef,
    target: ir.BlockId,
    arguments: []const ir.ValueId,
) NormalizeError!bool {
    const original_terminator = block.terminator;
    if (!redirectEdge(block, reference, target, arguments)) return false;
    program.blocks = blocks;
    var committed = false;
    defer {
        if (!committed) block.terminator = original_terminator;
    }

    if (function_id.index() >= program.functions.len or
        program.functions[function_id.index()].id != function_id)
    {
        return false;
    }
    var post_redirect_analysis = cfg.Analysis.init(
        allocator,
        program,
        program.functions[function_id.index()],
    ) catch |err| switch (err) {
        error.InvalidCfg => return false,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer post_redirect_analysis.deinit();

    const available = try clone_availability.functionUsesAreAvailable(
        allocator,
        program,
        &post_redirect_analysis,
    );
    traceNormalize("normalize_phase clone_fold_dominance_preflight source={} kind={s} from={} to={} available={} blocks={} reachable={}\n", .{
        reference.source.index(),
        @tagName(reference.kind),
        reference.target.index(),
        target.index(),
        available,
        post_redirect_analysis.function.blocks.len,
        post_redirect_analysis.reachableCount(),
    });
    if (!available) {
        return false;
    }
    committed = true;
    return true;
}

test "clone fold dominance preflight rolls back an unsafe redirect" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const producer = ir.BlockId.fromIndex(3);
    const use = ir.BlockId.fromIndex(4);
    const producer_instruction = ir.InstructionId.fromIndex(0);
    const produced = ir.ValueId.fromIndex(0);
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = clone } } },
        .{ .id = clone, .function = function_id, .terminator = .{ .jump = .{ .target = producer } } },
        .{ .id = producer, .function = function_id, .instructions = &.{producer_instruction}, .terminator = .{ .jump = .{ .target = use } } },
        .{ .id = use, .function = function_id, .terminator = .{ .return_values = &.{produced} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, source, clone, producer, use },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = produced,
        .function = function_id,
        .type = .integer,
        .origin = .{ .instruction_result = .{ .instruction = producer_instruction, .index = 0 } },
    }};
    const instructions = [_]ir.Instruction{.{
        .id = producer_instruction,
        .block = producer,
        .operation = .{ .constant = .{ .integer = "1" } },
        .results = &.{produced},
        .effects = .pure,
    }};
    const functions = [_]ir.Function{function};
    var program = ir.Program{
        .program_id = "clone-fold-dominance-preflight",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = blocks[0..],
        .instructions = &instructions,
        .values = &values,
    };
    const reference: ir.CfgEdgeRef = .{
        .source = source,
        .kind = .jump,
        .target = clone,
    };

    try std.testing.expect(!(try redirectEdgeWithDominancePreflight(
        std.testing.allocator,
        &program,
        blocks[0..],
        function_id,
        &blocks[source.index()],
        reference,
        use,
        &.{},
    )));
    try std.testing.expectEqual(clone, blocks[source.index()].terminator.jump.target);
}

test "eligible two-entry cycles normalize through authenticated node splitting" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const first = ir.BlockId.fromIndex(1);
    const second = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    const selector = ir.ValueId.fromIndex(0);
    const keep_looping = ir.ValueId.fromIndex(1);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = first },
            .else_edge = .{ .target = second },
        } }, .evidence = &.{evidence_id} },
        .{ .id = first, .function = function_id, .terminator = .{ .branch = .{
            .condition = keep_looping,
            .then_edge = .{ .target = second },
            .else_edge = .{ .target = exit },
        } }, .evidence = &.{evidence_id} },
        .{ .id = second, .function = function_id, .terminator = .{ .jump = .{ .target = first } }, .evidence = &.{evidence_id} },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} }, .evidence = &.{evidence_id} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, keep_looping },
        .blocks = &.{ second, entry, exit, first },
        .entry_block = entry,
        .evidence = &.{evidence_id},
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = keep_looping, .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
    };
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .dynamic_fixture, .locator = "fixture:node-split-normalization" }};
    const program: ir.Program = .{
        .program_id = "node-split-normalization",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const normalized = try normalizeInArena(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 1), normalized.cloned_blocks);
    try std.testing.expectEqual(@as(usize, 1), normalized.rewritten_edges);
    try std.testing.expectEqual(@as(usize, 5), normalized.program.blocks.len);
    try std.testing.expectEqual(ir.EdgeRewriteRule.node_split, normalized.program.edge_rewrites[0].rule);
    try std.testing.expectEqual(ir.BlockId.fromIndex(4), normalized.program.blocks[entry.index()].terminator.branch.else_edge.target);

    var graph = try cfg.Analysis.init(std.testing.allocator, &normalized.program, normalized.program.functions[0]);
    defer graph.deinit();
    var regions = try irreducible_region.analyze(std.testing.allocator, &graph);
    defer regions.deinit();
    try std.testing.expectEqual(@as(usize, 0), regions.regions.len);
    var structure_plan = try @import("structure.zig").Plan.init(std.testing.allocator, &graph);
    defer structure_plan.deinit();

    var report = try @import("validate.zig").validate(std.testing.allocator, &normalized.program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());

    const rerun = try normalizeInArena(arena.allocator(), &normalized.program);
    try std.testing.expectEqual(@as(usize, 0), rerun.cloned_blocks);
    try std.testing.expectEqual(normalized.program.blocks.len, rerun.program.blocks.len);
    try std.testing.expectEqual(normalized.program.edge_rewrites.len, rerun.program.edge_rewrites.len);
}

test "parameterized secondary entries clone value identity and terminator uses" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const primary = ir.BlockId.fromIndex(1);
    const secondary = ir.BlockId.fromIndex(2);
    const selector = ir.ValueId.fromIndex(0);
    const payload = ir.ValueId.fromIndex(1);
    const primary_value = ir.ValueId.fromIndex(2);
    const secondary_value = ir.ValueId.fromIndex(3);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = primary, .arguments = &.{payload} },
            .else_edge = .{ .target = secondary, .arguments = &.{payload} },
        } }, .evidence = &.{evidence_id} },
        .{ .id = primary, .function = function_id, .parameters = &.{primary_value}, .terminator = .{ .jump = .{
            .target = secondary,
            .arguments = &.{primary_value},
        } }, .evidence = &.{evidence_id} },
        .{ .id = secondary, .function = function_id, .parameters = &.{secondary_value}, .terminator = .{ .jump = .{
            .target = primary,
            .arguments = &.{secondary_value},
        } }, .evidence = &.{evidence_id} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, payload },
        .blocks = &.{ secondary, entry, primary },
        .entry_block = entry,
        .evidence = &.{evidence_id},
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = payload, .function = function_id, .type = .integer, .name_hint = "payload", .origin = .{ .parameter = 1 } },
        .{ .id = primary_value, .function = function_id, .type = .integer, .name_hint = "primary_value", .origin = .{ .block_parameter = .{ .block = primary, .index = 0 } } },
        .{ .id = secondary_value, .function = function_id, .type = .integer, .name_hint = "secondary_value", .origin = .{ .block_parameter = .{ .block = secondary, .index = 0 } } },
    };
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .dynamic_fixture, .locator = "fixture:parameterized-node-split" }};
    const program: ir.Program = .{
        .program_id = "parameterized-node-split",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const normalized = try normalizeInArena(arena.allocator(), &program);
    const clone_id = ir.BlockId.fromIndex(3);
    const clone_value = ir.ValueId.fromIndex(4);
    try std.testing.expectEqual(@as(usize, 1), normalized.cloned_blocks);
    try std.testing.expectEqual(@as(usize, 1), normalized.cloned_values);
    try std.testing.expectEqual(@as(usize, 1), normalized.rewritten_edges);
    try std.testing.expectEqual(@as(usize, 4), normalized.program.blocks.len);
    try std.testing.expectEqual(@as(usize, 5), normalized.program.values.len);
    try std.testing.expectEqualSlices(ir.ValueId, &.{payload}, normalized.program.edge_rewrites[0].from.arguments);
    try std.testing.expectEqualSlices(ir.ValueId, &.{payload}, normalized.program.edge_rewrites[0].to.arguments);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_value}, normalized.program.blocks[clone_id.index()].parameters);
    try std.testing.expectEqualSlices(ir.ValueId, &.{clone_value}, normalized.program.blocks[clone_id.index()].terminator.jump.arguments);
    try std.testing.expectEqual(secondary, normalized.program.values[secondary_value.index()].origin.block_parameter.block);
    try std.testing.expectEqual(clone_id, normalized.program.values[clone_value.index()].origin.block_parameter.block);
    try std.testing.expectEqualStrings("secondary_value", normalized.program.values[clone_value.index()].name_hint.?);

    var graph = try cfg.Analysis.init(std.testing.allocator, &normalized.program, normalized.program.functions[0]);
    defer graph.deinit();
    var regions = try irreducible_region.analyze(std.testing.allocator, &graph);
    defer regions.deinit();
    try std.testing.expectEqual(@as(usize, 0), regions.regions.len);
    var structure_plan = try @import("structure.zig").Plan.init(std.testing.allocator, &graph);
    defer structure_plan.deinit();

    var report = try @import("validate.zig").validate(std.testing.allocator, &normalized.program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());

    const rerun = try normalizeInArena(arena.allocator(), &normalized.program);
    try std.testing.expectEqual(@as(usize, 0), rerun.cloned_blocks);
    try std.testing.expectEqual(@as(usize, 0), rerun.cloned_values);
    try std.testing.expectEqual(normalized.program.values.len, rerun.program.values.len);

    var invalid_values = values;
    invalid_values[secondary_value.index()].origin = .{ .parameter = 2 };
    var invalid_program = program;
    invalid_program.values = &invalid_values;
    const refused = try normalizeInArena(arena.allocator(), &invalid_program);
    try std.testing.expectEqual(@as(usize, 0), refused.cloned_blocks);
    var refused_report = try @import("validate.zig").validate(std.testing.allocator, &refused.program, .readable_luau);
    defer refused_report.deinit();
    try std.testing.expect(refused_report.contains(.block_parameter_origin_mismatch));
    // The malformed value origin is the admission error. The node-split
    // parameter-contract diagnostic describes a splitter limitation, not an
    // admission error when dispatch is available.
    try std.testing.expect(!refused_report.contains(.irreducible_entry_parameter_contract));
}

test "mapped parameterized continuations clone while stable ones remain shared" {
    const function_id = ir.FunctionId.fromIndex(0);
    const secondary = ir.BlockId.fromIndex(0);
    const primary = ir.BlockId.fromIndex(1);
    const mapped_continuation = ir.BlockId.fromIndex(2);
    const stable_continuation = ir.BlockId.fromIndex(3);
    const stable_input = ir.ValueId.fromIndex(0);
    const mapped_value = ir.ValueId.fromIndex(1);
    const mapped_parameter = ir.ValueId.fromIndex(2);
    const stable_parameter = ir.ValueId.fromIndex(3);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = secondary, .function = function_id, .parameters = &.{mapped_value}, .terminator = .{ .branch = .{
            .condition = stable_input,
            .then_edge = .{ .target = mapped_continuation, .arguments = &.{mapped_value} },
            .else_edge = .{ .target = stable_continuation, .arguments = &.{stable_input} },
        } }, .evidence = &.{evidence_id} },
        .{ .id = primary, .function = function_id, .terminator = .{ .return_values = &.{stable_input} }, .evidence = &.{evidence_id} },
        .{ .id = mapped_continuation, .function = function_id, .parameters = &.{mapped_parameter}, .terminator = .{ .return_values = &.{mapped_value} }, .evidence = &.{evidence_id} },
        .{ .id = stable_continuation, .function = function_id, .parameters = &.{stable_parameter}, .terminator = .{ .return_values = &.{stable_input} }, .evidence = &.{evidence_id} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{stable_input},
        .blocks = &.{ secondary, primary, mapped_continuation, stable_continuation },
        .entry_block = secondary,
        .evidence = &.{evidence_id},
    }};
    const values = [_]ir.Value{
        .{ .id = stable_input, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = mapped_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = secondary, .index = 0 } } },
        .{ .id = mapped_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = mapped_continuation, .index = 0 } } },
        .{ .id = stable_parameter, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = stable_continuation, .index = 0 } } },
    };
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .dynamic_fixture, .locator = "fixture:mapped-parameterized-continuation" }};
    const program: ir.Program = .{
        .program_id = "mapped-parameterized-continuation",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var analysis = try cfg.Analysis.init(arena.allocator(), &program, functions[0]);
    defer analysis.deinit();
    var closure: std.ArrayList(ir.BlockId) = .empty;
    try closure.append(arena.allocator(), secondary);

    try std.testing.expect(try extendContinuationClosure(
        arena.allocator(),
        &program,
        &analysis,
        primary,
        &closure,
    ));
    try std.testing.expectEqual(@as(usize, 3), closure.items.len);
    try std.testing.expect(blockInRegion(closure.items, primary));
    try std.testing.expect(blockInRegion(closure.items, mapped_continuation));
    try std.testing.expect(!blockInRegion(closure.items, stable_continuation));
}

test "continuation cloning carries secondary values through a zero-parameter primary" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const secondary = ir.BlockId.fromIndex(1);
    const primary = ir.BlockId.fromIndex(2);
    const continuation = ir.BlockId.fromIndex(3);
    const target = ir.BlockId.fromIndex(4);
    const payload = ir.ValueId.fromIndex(0);
    const secondary_value = ir.ValueId.fromIndex(1);
    const target_value = ir.ValueId.fromIndex(2);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{
            .target = secondary,
            .arguments = &.{payload},
        } }, .evidence = &.{evidence_id} },
        .{ .id = secondary, .function = function_id, .parameters = &.{secondary_value}, .terminator = .{ .jump = .{
            .target = primary,
        } }, .evidence = &.{evidence_id} },
        .{ .id = primary, .function = function_id, .terminator = .{ .jump = .{ .target = continuation } }, .evidence = &.{evidence_id} },
        .{ .id = continuation, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &.{secondary_value},
        } }, .evidence = &.{evidence_id} },
        .{ .id = target, .function = function_id, .parameters = &.{target_value}, .terminator = .{ .return_values = &.{target_value} }, .evidence = &.{evidence_id} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{payload},
        .blocks = &.{ entry, secondary, primary, continuation, target },
        .entry_block = entry,
        .evidence = &.{evidence_id},
    }};
    const values = [_]ir.Value{
        .{ .id = payload, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = secondary_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = secondary, .index = 0 } } },
        .{ .id = target_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
    };
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .dynamic_fixture, .locator = "fixture:continuation-value-clone" }};
    const program: ir.Program = .{
        .program_id = "continuation-value-clone",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
    };

    var primary_incoming = [_]ir.CfgEdgeRef{.{ .source = secondary, .kind = .jump, .target = primary }};
    var secondary_incoming = [_]ir.CfgEdgeRef{.{ .source = entry, .kind = .jump, .target = secondary }};
    var region_blocks = [_]ir.BlockId{ primary, secondary };
    var entries = [_]irreducible_region.Entry{
        .{ .block = primary, .incoming = &primary_incoming, .is_function_entry = false },
        .{ .block = secondary, .incoming = &secondary_incoming, .is_function_entry = false },
    };
    const region: irreducible_region.Region = .{ .blocks = &region_blocks, .entries = &entries };

    var graph = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer graph.deinit();
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const work = arena.allocator();
    const closure = (try cloneClosure(
        work,
        &program,
        &graph,
        region,
        primary,
        secondary,
        secondary_incoming[0..],
    )).?;
    try std.testing.expectEqual(@as(usize, 3), closure.len);
    try std.testing.expect(blockInRegion(closure, secondary));
    try std.testing.expect(blockInRegion(closure, primary));
    try std.testing.expect(blockInRegion(closure, continuation));

    const incoming = try work.dupe(ir.CfgEdgeRef, &secondary_incoming);
    const secondaries = try work.alloc(Secondary, 1);
    secondaries[0] = .{ .block = secondary, .incoming = incoming, .closure = closure };
    var plan = SplitPlan{
        .allocator = work,
        .function_index = 0,
        .secondaries = secondaries,
        .secondary_count = 1,
    };
    defer plan.deinit();

    var block_list: std.ArrayList(ir.Block) = .empty;
    try block_list.appendSlice(work, &blocks);
    var function_list: std.ArrayList(ir.Function) = .empty;
    try function_list.appendSlice(work, &functions);
    var instruction_list: std.ArrayList(ir.Instruction) = .empty;
    var value_list: std.ArrayList(ir.Value) = .empty;
    try value_list.appendSlice(work, &values);
    var pack_list: std.ArrayList(ir.ValuePack) = .empty;
    var rewrite_list: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    var working_program = program;
    var result: Result = .{ .program = working_program };
    try applyPlan(
        work,
        &working_program,
        &block_list,
        &function_list,
        &instruction_list,
        &value_list,
        &pack_list,
        &rewrite_list,
        &plan,
        &result,
    );

    var clones: [3]ir.BlockId = undefined;
    for (closure, 0..) |_, index| clones[index] = ir.BlockId.fromIndex(blocks.len + index);
    const secondary_clone = mappedClone(closure, &clones, secondary).?;
    const continuation_clone = mappedClone(closure, &clones, continuation).?;
    try std.testing.expectEqual(secondary_clone, working_program.blocks[entry.index()].terminator.jump.target);
    switch (working_program.blocks[continuation_clone.index()].terminator) {
        .jump => |edge| {
            try std.testing.expectEqual(target, edge.target);
            try std.testing.expectEqual(@as(usize, 1), edge.arguments.len);
            try std.testing.expectEqual(working_program.blocks[secondary_clone.index()].parameters[0], edge.arguments[0]);
        },
        else => try std.testing.expect(false),
    }
    var report = try @import("validate.zig").validate(std.testing.allocator, &working_program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "failed clone application rolls back graph and rewrite state" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const secondary = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const payload = ir.ValueId.fromIndex(0);
    const secondary_value = ir.ValueId.fromIndex(1);
    const target_value = ir.ValueId.fromIndex(2);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{
            .target = secondary,
            .arguments = &.{payload},
        } }, .evidence = &.{evidence_id} },
        .{ .id = secondary, .function = function_id, .parameters = &.{secondary_value}, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &.{secondary_value},
        } }, .evidence = &.{evidence_id} },
        .{ .id = target, .function = function_id, .parameters = &.{target_value}, .terminator = .{ .return_values = &.{target_value} }, .evidence = &.{evidence_id} },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{payload},
        .blocks = &.{ entry, secondary, target },
        .entry_block = entry,
        .evidence = &.{evidence_id},
    };
    const values = [_]ir.Value{
        .{ .id = payload, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = secondary_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = secondary, .index = 0 } } },
        .{ .id = target_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
    };
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .dynamic_fixture, .locator = "fixture:transactional-clone-rollback" }};
    const program: ir.Program = .{
        .program_id = "transactional-clone-rollback",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const work = arena.allocator();
    const incoming = try work.dupe(ir.CfgEdgeRef, &.{
        .{ .source = entry, .kind = .jump, .target = secondary },
        .{ .source = entry, .kind = .jump, .target = secondary },
    });
    const closure = try work.dupe(ir.BlockId, &.{secondary});
    const secondaries = try work.alloc(Secondary, 1);
    secondaries[0] = .{ .block = secondary, .incoming = incoming, .closure = closure };
    var plan = SplitPlan{
        .allocator = work,
        .function_index = 0,
        .secondaries = secondaries,
        .secondary_count = 1,
    };
    defer plan.deinit();

    var block_list: std.ArrayList(ir.Block) = .empty;
    defer block_list.deinit(work);
    try block_list.appendSlice(work, &blocks);
    var function_list: std.ArrayList(ir.Function) = .empty;
    defer function_list.deinit(work);
    try function_list.appendSlice(work, &.{function});
    var instruction_list: std.ArrayList(ir.Instruction) = .empty;
    defer instruction_list.deinit(work);
    var value_list: std.ArrayList(ir.Value) = .empty;
    defer value_list.deinit(work);
    try value_list.appendSlice(work, &values);
    var pack_list: std.ArrayList(ir.ValuePack) = .empty;
    defer pack_list.deinit(work);
    var rewrite_list: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    defer rewrite_list.deinit(work);
    var working_program = program;
    var result: Result = .{ .program = working_program };

    try std.testing.expectError(
        error.NormalizationInvariantFailed,
        applyPlan(
            work,
            &working_program,
            &block_list,
            &function_list,
            &instruction_list,
            &value_list,
            &pack_list,
            &rewrite_list,
            &plan,
            &result,
        ),
    );
    try std.testing.expectEqual(@as(usize, blocks.len), block_list.items.len);
    try std.testing.expectEqual(@as(usize, values.len), value_list.items.len);
    try std.testing.expectEqual(@as(usize, 0), instruction_list.items.len);
    try std.testing.expectEqual(@as(usize, 0), rewrite_list.items.len);
    try std.testing.expectEqual(secondary, block_list.items[entry.index()].terminator.jump.target);
    try std.testing.expectEqualSlices(ir.BlockId, function.blocks, function_list.items[0].blocks);
    try std.testing.expectEqual(@as(usize, 0), result.cloned_blocks);
    try std.testing.expectEqual(@as(usize, 0), result.cloned_values);
    try std.testing.expectEqual(@as(usize, 0), result.rewritten_edges);
    try std.testing.expectEqual(block_list.items.ptr, working_program.blocks.ptr);
    try std.testing.expectEqual(rewrite_list.items.ptr, working_program.edge_rewrites.ptr);
}

test "mixed irreducible regions split self-loop secondaries to full reducibility" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const primary = ir.BlockId.fromIndex(1);
    const eligible = ir.BlockId.fromIndex(2);
    const blocked = ir.BlockId.fromIndex(3);
    const router = ir.BlockId.fromIndex(4);
    const first_condition = ir.ValueId.fromIndex(0);
    const second_condition = ir.ValueId.fromIndex(1);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = first_condition,
            .then_edge = .{ .target = primary },
            .else_edge = .{ .target = router },
        } }, .evidence = &.{evidence_id} },
        .{ .id = primary, .function = function_id, .terminator = .{ .branch = .{
            .condition = first_condition,
            .then_edge = .{ .target = eligible },
            .else_edge = .{ .target = blocked },
        } }, .evidence = &.{evidence_id} },
        .{ .id = eligible, .function = function_id, .terminator = .{ .jump = .{ .target = primary } }, .evidence = &.{evidence_id} },
        .{ .id = blocked, .function = function_id, .terminator = .{ .branch = .{
            .condition = second_condition,
            .then_edge = .{ .target = blocked },
            .else_edge = .{ .target = primary },
        } }, .evidence = &.{evidence_id} },
        .{ .id = router, .function = function_id, .terminator = .{ .branch = .{
            .condition = second_condition,
            .then_edge = .{ .target = eligible },
            .else_edge = .{ .target = blocked },
        } }, .evidence = &.{evidence_id} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ first_condition, second_condition },
        .blocks = &.{ blocked, router, entry, eligible, primary },
        .entry_block = entry,
        .evidence = &.{evidence_id},
    }};
    const values = [_]ir.Value{
        .{ .id = first_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = second_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
    };
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .dynamic_fixture, .locator = "fixture:mixed-irreducible-policy" }};
    const program: ir.Program = .{
        .program_id = "mixed-irreducible-policy",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const normalized = try normalizeInArena(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 2), normalized.cloned_blocks);
    try std.testing.expectEqual(@as(usize, 2), normalized.rewritten_edges);
    try std.testing.expectEqual(ir.EdgeRewriteRule.node_split, normalized.program.edge_rewrites[0].rule);
    try std.testing.expectEqual(ir.EdgeRewriteRule.node_split, normalized.program.edge_rewrites[1].rule);
    try std.testing.expectEqual(ir.BlockId.fromIndex(5), normalized.program.blocks[router.index()].terminator.branch.then_edge.target);
    const blocked_clone = ir.BlockId.fromIndex(6);
    try std.testing.expectEqual(blocked_clone, normalized.program.blocks[router.index()].terminator.branch.else_edge.target);
    try std.testing.expectEqual(blocked_clone, normalized.program.blocks[blocked_clone.index()].terminator.branch.then_edge.target);
    try std.testing.expectEqual(primary, normalized.program.blocks[blocked_clone.index()].terminator.branch.else_edge.target);

    var graph = try cfg.Analysis.init(std.testing.allocator, &normalized.program, normalized.program.functions[0]);
    defer graph.deinit();
    var regions = try irreducible_region.analyze(std.testing.allocator, &graph);
    defer regions.deinit();
    try std.testing.expectEqual(@as(usize, 0), regions.regions.len);

    var core_report = try @import("validate.zig").validate(std.testing.allocator, &normalized.program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try @import("validate.zig").validate(std.testing.allocator, &normalized.program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());

    const rerun = try normalizeInArena(arena.allocator(), &normalized.program);
    try std.testing.expectEqual(@as(usize, 0), rerun.cloned_blocks);
    try std.testing.expectEqual(normalized.program.blocks.len, rerun.program.blocks.len);
    try std.testing.expectEqual(normalized.program.edge_rewrites.len, rerun.program.edge_rewrites.len);

    const tampered_blocks = try std.testing.allocator.dupe(ir.Block, normalized.program.blocks);
    defer std.testing.allocator.free(tampered_blocks);
    tampered_blocks[blocked_clone.index()].terminator.branch.then_edge.target = blocked;
    var tampered = normalized.program;
    tampered.blocks = tampered_blocks;
    var tampered_report = try @import("validate.zig").validate(std.testing.allocator, &tampered, .core);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.invalid_edge_rewrite));
}

test "mixed region plan retains only eligible secondary entries" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const primary = ir.BlockId.fromIndex(1);
    const eligible = ir.BlockId.fromIndex(2);
    const ineligible = ir.BlockId.fromIndex(3);
    const other_source = ir.BlockId.fromIndex(4);
    const parameter = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = parameter,
            .then_edge = .{ .target = primary },
            .else_edge = .{ .target = eligible },
        } } },
        .{ .id = primary, .function = function_id, .terminator = .{ .jump = .{ .target = eligible } } },
        .{ .id = eligible, .function = function_id, .terminator = .{ .jump = .{ .target = primary } } },
        .{ .id = ineligible, .function = function_id, .parameters = &.{parameter}, .terminator = .{ .jump = .{ .target = primary } } },
        .{ .id = other_source, .function = function_id, .terminator = .{ .jump = .{ .target = ineligible } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{parameter},
        .blocks = &.{ entry, primary, eligible, ineligible, other_source },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{.{ .id = parameter, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } }};
    const program: ir.Program = .{
        .program_id = "partial-node-split-plan",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var primary_incoming = [_]ir.CfgEdgeRef{.{ .source = entry, .kind = .branch_then, .target = primary }};
    var eligible_incoming = [_]ir.CfgEdgeRef{.{ .source = entry, .kind = .branch_else, .target = eligible }};
    var ineligible_incoming = [_]ir.CfgEdgeRef{.{ .source = other_source, .kind = .jump, .target = ineligible }};
    var entries = [_]irreducible_region.Entry{
        .{ .block = primary, .incoming = &primary_incoming, .is_function_entry = false },
        .{ .block = eligible, .incoming = &eligible_incoming, .is_function_entry = false },
        .{ .block = ineligible, .incoming = &ineligible_incoming, .is_function_entry = false },
    };
    var region_blocks = [_]ir.BlockId{ primary, eligible, ineligible };
    const region: irreducible_region.Region = .{ .blocks = &region_blocks, .entries = &entries };

    var graph = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer graph.deinit();
    var plan = (try planRegion(std.testing.allocator, &program, &graph, 0, region)).?;
    defer plan.deinit();
    try std.testing.expectEqual(@as(usize, 1), plan.secondary_count);
    try std.testing.expectEqual(eligible, plan.secondaries[0].block);
}
