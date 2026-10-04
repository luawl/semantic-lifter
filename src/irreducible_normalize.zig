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
