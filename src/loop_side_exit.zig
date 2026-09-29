const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const natural_loop = @import("natural_loop.zig");
const proof_effect_closure = @import("proof_effect_closure.zig");
const structural_overlap = @import("structural_overlap.zig");

pub const Error = error{UnsupportedShape} || std.mem.Allocator.Error;

/// Selects one effectful outside region entered by multiple loop boundary
/// edges before the loop's canonical exit. Exact predecessor ownership keeps
/// the region single-entry once those boundary edges are projected as breaks.
pub fn selectSharedRegionEntryAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    membership: []const bool,
    canonical_exit: ir.BlockId,
) Error!?ir.BlockId {
    return selectSharedRegionEntryAllocWithReplayContext(
        allocator,
        analysis,
        membership,
        canonical_exit,
        null,
    );
}

pub fn selectSharedRegionEntryAllocWithReplayContext(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    membership: []const bool,
    canonical_exit: ir.BlockId,
    replay_context: ?*structural_overlap.ReplayProjectionContext,
) Error!?ir.BlockId {
    const entries = try selectSharedRegionEntriesAllocWithReplayContext(
        allocator,
        analysis,
        membership,
        canonical_exit,
        replay_context,
    );
    defer allocator.free(entries);
    if (entries.len != 1) return null;
    return entries[0];
}

/// Select every independently owned side-region entry for one loop exit.
///
/// A parameterized continuation may have several authenticated clone handoffs
/// from one loop body.  Returning only the first candidate loses the entry
/// tuple of the other arms and makes the structurer report a false ownership
/// collision.  The caller still has to build and own each region; this
/// function authenticates eligibility only.
pub fn selectSharedRegionEntriesAllocWithReplayContext(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    membership: []const bool,
    canonical_exit: ir.BlockId,
    replay_context: ?*structural_overlap.ReplayProjectionContext,
) Error![]ir.BlockId {
    if (membership.len != analysis.function.blocks.len) return error.UnsupportedShape;
    const exit_index = analysis.blockIndex(canonical_exit) orelse return error.UnsupportedShape;
    if (membership[exit_index] or !analysis.isReachable(canonical_exit)) return error.UnsupportedShape;

    var counts: std.AutoHashMapUnmanaged(ir.BlockId, usize) = .empty;
    defer counts.deinit(allocator);
    for (analysis.function.blocks, 0..) |source, source_index| {
        if (!membership[source_index] or !analysis.isReachable(source)) continue;
        const branch = switch (analysis.program.blocks[source.index()].terminator) {
            .branch => |value| value,
            else => continue,
        };
        const edges = [_]ir.Edge{ branch.then_edge, branch.else_edge };
        for (edges, 0..) |edge, edge_index| {
            if (edge.target == canonical_exit) continue;
            const target_index = analysis.blockIndex(edge.target) orelse return error.UnsupportedShape;
            const other_index = analysis.blockIndex(edges[1 - edge_index].target) orelse return error.UnsupportedShape;
            if (edge.target.index() < analysis.program.blocks.len and
                analysis.program.blocks[edge.target.index()].parameters.len != 0)
            {
                structural_overlap.traceStructural(
                    "structural_phase shared_entry_count_edge function={} source={} target={} target_member={} other={} other_member={} reachable={} canonical_exit={}\n",
                    .{
                        analysis.function.id.index(),
                        source.index(),
                        edge.target.index(),
                        membership[target_index],
                        edges[1 - edge_index].target.index(),
                        membership[other_index],
                        analysis.isReachable(edge.target),
                        canonical_exit.index(),
                    },
                );
            }
            if (membership[target_index] or !membership[other_index] or !analysis.isReachable(edge.target)) continue;
            const entry = try counts.getOrPut(allocator, edge.target);
            if (!entry.found_existing) {
                entry.value_ptr.* = 0;
            }
            entry.value_ptr.* += 1;
            if (analysis.program.blocks[edge.target.index()].parameters.len != 0) {
                structural_overlap.traceStructural(
                    "structural_phase shared_entry_counted function={} source={} target={} stored={} count={} map_count={} canonical_exit={} raw_target={} raw_stored={}\n",
                    .{
                        analysis.function.id.index(),
                        source.index(),
                        edge.target.index(),
                        entry.key_ptr.*.index(),
                        entry.value_ptr.*,
                        counts.count(),
                        canonical_exit.index(),
                        @intFromEnum(edge.target),
                        @intFromEnum(entry.key_ptr.*),
                    },
                );
            }
        }
    }

    structural_overlap.traceStructural(
        "structural_phase shared_entry_preflight function={} map_count={} canonical_exit={}\n",
        .{ analysis.function.id.index(), counts.count(), canonical_exit.index() },
    );
    var preflight_iterator = counts.iterator();
    while (preflight_iterator.next()) |entry| {
        structural_overlap.traceStructural(
            "structural_phase shared_entry_preflight_iter function={} target={} incoming={} map_count={} canonical_exit={} raw_target={}\n",
            .{ analysis.function.id.index(), entry.key_ptr.*.index(), entry.value_ptr.*, counts.count(), canonical_exit.index(), @intFromEnum(entry.key_ptr.*) },
        );
    }

    var selected = std.ArrayList(ir.BlockId).empty;
    errdefer selected.deinit(allocator);
    var iterator = counts.iterator();
    while (iterator.next()) |entry| {
        const target = entry.key_ptr.*;
        const incoming_count = entry.value_ptr.*;
        structural_overlap.traceStructural(
            "structural_phase shared_entry_iter_raw function={} target={} incoming={} map_count={} canonical_exit={} raw_target={}\n",
            .{ analysis.function.id.index(), target.index(), incoming_count, counts.count(), canonical_exit.index(), @intFromEnum(target) },
        );
        if (target.index() < analysis.program.blocks.len and
            analysis.program.blocks[target.index()].parameters.len != 0)
        {
            structural_overlap.traceStructural(
                "structural_phase shared_entry_iter function={} target={} incoming={} map_count={} canonical_exit={} raw_target={}\n",
                .{ analysis.function.id.index(), target.index(), incoming_count, counts.count(), canonical_exit.index(), @intFromEnum(target) },
            );
        }
        const observable_entry = try targetHasObservableEntryState(analysis, target);
        const reaches_exit = try natural_loop.canReachOutsideLoopAlloc(
            allocator,
            analysis,
            membership,
            target,
            canonical_exit,
        );
        if (observable_entry or reaches_exit) {
            structural_overlap.traceStructural(
                "structural_phase shared_entry_candidate function={} target={} incoming={} observable={} reaches_exit={} parameters={} predecessors={}\n",
                .{
                    analysis.function.id.index(),
                    target.index(),
                    incoming_count,
                    observable_entry,
                    reaches_exit,
                    analysis.program.blocks[target.index()].parameters.len,
                    analysis.predecessorCount(target),
                },
            );
        }
        if (incoming_count == 0 or !observable_entry or !reaches_exit) continue;

        const boundary_edges = try collectBoundaryEdgesAlloc(allocator, analysis, membership, target);
        defer allocator.free(boundary_edges);
        if (boundary_edges.len != incoming_count) {
            structural_overlap.traceStructural(
                "structural_phase shared_entry_reject function={} target={} reason=boundary_count incoming={} boundary={}\n",
                .{ analysis.function.id.index(), target.index(), incoming_count, boundary_edges.len },
            );
            continue;
        }

        const external_predecessors = try countExternalPredecessors(
            analysis,
            membership,
            target,
            boundary_edges,
        );
        if (external_predecessors == null) continue;
        const external_count = external_predecessors.?;

        if (external_count == 0) {
            // Preserve the original shared-side rule for ordinary CFGs. A
            // single in-loop edge is not a shared entry merely because its
            // target happens to be effectful.
            if (incoming_count < 2 or analysis.predecessorCount(target) != incoming_count) {
                structural_overlap.traceStructural(
                    "structural_phase shared_entry_reject function={} target={} reason=ordinary_entry_shape external={} incoming={} predecessors={}\n",
                    .{
                        analysis.function.id.index(),
                        target.index(),
                        external_count,
                        incoming_count,
                        analysis.predecessorCount(target),
                    },
                );
                continue;
            }
        } else {
            const authenticated = try authenticatedExternalPredecessors(
                analysis,
                target,
                boundary_edges,
                replay_context,
            );
            structural_overlap.traceStructural(
                "structural_phase shared_entry_replay function={} target={} external={} authenticated={} boundary={}\n",
                .{ analysis.function.id.index(), target.index(), external_count, authenticated, boundary_edges.len },
            );
            if (!authenticated) continue;
        }

        try selected.append(allocator, target);
        structural_overlap.traceStructural(
            "structural_phase shared_entry_select function={} target={}\n",
            .{ analysis.function.id.index(), target.index() },
        );
    }
    std.mem.sort(ir.BlockId, selected.items, {}, struct {
        fn lessThan(_: void, left: ir.BlockId, right: ir.BlockId) bool {
            return left.index() < right.index();
        }
    }.lessThan);
    if (selected.items.len > 1 and
        !try selectedEntriesHaveDisjointRegions(
            allocator,
            analysis,
            membership,
            canonical_exit,
            selected.items,
        ))
    {
        // Each entry is materialized as an independently owned region. A
        // shared non-exit block cannot be assigned to two such regions.
        selected.clearRetainingCapacity();
    }
    return selected.toOwnedSlice(allocator);
}

/// Check the ownership contract of a multi-entry side exit before the
/// structurer starts mutating its visited set. The exact structured region is
/// intentionally not guessed here; a conservative CFG closure is enough to
/// reject any pair that could compete for a non-exit block. The canonical exit
/// is the one permitted convergence point and is therefore excluded.
fn selectedEntriesHaveDisjointRegions(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    membership: []const bool,
    canonical_exit: ir.BlockId,
    entries: []const ir.BlockId,
) Error!bool {
    const block_count = analysis.function.blocks.len;
    const aggregate = try allocator.alloc(bool, block_count);
    defer allocator.free(aggregate);
    const closure = try allocator.alloc(bool, block_count);
    defer allocator.free(closure);
    const pending = try allocator.alloc(ir.BlockId, block_count);
    defer allocator.free(pending);
    @memset(aggregate, false);

    for (entries) |entry| {
        const entry_index = analysis.blockIndex(entry) orelse return error.UnsupportedShape;
        if (entry_index >= membership.len or membership[entry_index]) return error.UnsupportedShape;

        @memset(closure, false);
        var pending_len: usize = 1;
        var cursor: usize = 0;
        pending[0] = entry;
        while (cursor < pending_len) : (cursor += 1) {
            const current = pending[cursor];
            if (current == canonical_exit) continue;
            const current_index = analysis.blockIndex(current) orelse return error.UnsupportedShape;
            if (current_index >= membership.len or membership[current_index]) continue;
            if (!analysis.isReachable(current)) return error.UnsupportedShape;
            if (closure[current_index]) continue;
            closure[current_index] = true;

            for (0..analysis.successorCount(current)) |successor_index| {
                const successor = analysis.successorAt(current, successor_index) orelse
                    return error.UnsupportedShape;
                if (successor == canonical_exit) continue;
                const successor_local = analysis.blockIndex(successor) orelse
                    return error.UnsupportedShape;
                if (successor_local >= membership.len or membership[successor_local] or
                    closure[successor_local]) continue;
                if (pending_len >= pending.len) return error.UnsupportedShape;
                pending[pending_len] = successor;
                pending_len += 1;
            }
        }

        for (closure, 0..) |owns_block, local_index| {
            if (!owns_block) continue;
            if (aggregate[local_index]) {
                structural_overlap.traceStructural(
                    "structural_phase shared_entry_reject function={} reason=overlapping_regions entry={} block={} canonical_exit={}\n",
                    .{
                        analysis.function.id.index(),
                        entry.index(),
                        analysis.function.blocks[local_index].index(),
                        canonical_exit.index(),
                    },
                );
                return false;
            }
        }
        for (closure, 0..) |owns_block, local_index| {
            if (owns_block) aggregate[local_index] = true;
        }
    }
    return true;
}

fn targetHasObservableEntryState(
    analysis: *const cfg.Analysis,
    target: ir.BlockId,
) Error!bool {
    if (target.index() >= analysis.program.blocks.len) return error.UnsupportedShape;
    const block = analysis.program.blocks[target.index()];
    if (block.id != target or block.function != analysis.function.id) return error.UnsupportedShape;
    if (block.parameters.len != 0) return true;
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= analysis.program.instructions.len) return error.UnsupportedShape;
        const instruction = analysis.program.instructions[instruction_id.index()];
        if (instruction.id != instruction_id or instruction.block != target) return error.UnsupportedShape;
        if (proof_effect_closure.hasObservableEffects(instruction.effects)) return true;
    }
    return false;
}

fn collectBoundaryEdgesAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    membership: []const bool,
    target: ir.BlockId,
) Error![]ir.CfgEdgeRef {
    var edges: std.ArrayList(ir.CfgEdgeRef) = .empty;
    errdefer edges.deinit(allocator);
    for (analysis.function.blocks, 0..) |source, source_index| {
        if (!membership[source_index] or !analysis.isReachable(source)) continue;
        const branch = switch (analysis.program.blocks[source.index()].terminator) {
            .branch => |value| value,
            else => continue,
        };
        if (branch.then_edge.target == target and
            (analysis.blockIndex(branch.else_edge.target) orelse return error.UnsupportedShape) < membership.len and
            membership[(analysis.blockIndex(branch.else_edge.target) orelse return error.UnsupportedShape)])
        {
            try edges.append(allocator, .{ .source = source, .kind = .branch_then, .target = target });
        }
        if (branch.else_edge.target == target and
            (analysis.blockIndex(branch.then_edge.target) orelse return error.UnsupportedShape) < membership.len and
            membership[(analysis.blockIndex(branch.then_edge.target) orelse return error.UnsupportedShape)])
        {
            try edges.append(allocator, .{ .source = source, .kind = .branch_else, .target = target });
        }
    }
    return edges.toOwnedSlice(allocator);
}

fn edgeReferenceForTarget(
    program: *const ir.Program,
    source: ir.BlockId,
    target: ir.BlockId,
) ?ir.CfgEdgeRef {
    if (source.index() >= program.blocks.len) return null;
    const block = program.blocks[source.index()];
    if (block.id != source) return null;
    return switch (block.terminator) {
        .jump => |edge| if (edge.target == target)
            .{ .source = source, .kind = .jump, .target = target }
        else
            null,
        .branch => |branch| {
            const then_matches = branch.then_edge.target == target;
            const else_matches = branch.else_edge.target == target;
            if (then_matches == else_matches) return null;
            return if (then_matches)
                .{ .source = source, .kind = .branch_then, .target = target }
            else
                .{ .source = source, .kind = .branch_else, .target = target };
        },
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => null,
    };
}

fn containsBoundaryEdge(edges: []const ir.CfgEdgeRef, reference: ir.CfgEdgeRef) bool {
    for (edges) |candidate| if (std.meta.eql(candidate, reference)) return true;
    return false;
}

fn countExternalPredecessors(
    analysis: *const cfg.Analysis,
    membership: []const bool,
    target: ir.BlockId,
    boundary_edges: []const ir.CfgEdgeRef,
) Error!?usize {
    var external_count: usize = 0;
    for (0..analysis.predecessorCount(target)) |index| {
        const predecessor = analysis.predecessorAt(target, index) orelse return null;
        const predecessor_index = analysis.blockIndex(predecessor) orelse return error.UnsupportedShape;
        const reference = edgeReferenceForTarget(analysis.program, predecessor, target) orelse return null;
        if (membership[predecessor_index]) {
            if (!containsBoundaryEdge(boundary_edges, reference)) return null;
        } else {
            external_count += 1;
        }
    }
    return external_count;
}

fn authenticatedExternalPredecessors(
    analysis: *const cfg.Analysis,
    target: ir.BlockId,
    boundary_edges: []const ir.CfgEdgeRef,
    replay_context: ?*structural_overlap.ReplayProjectionContext,
) Error!bool {
    const context = replay_context orelse return false;
    if (target.index() >= analysis.program.blocks.len or
        analysis.program.blocks[target.index()].parameters.len == 0) return false;

    for (0..analysis.predecessorCount(target)) |index| {
        const predecessor = analysis.predecessorAt(target, index) orelse return false;
        const predecessor_index = analysis.blockIndex(predecessor) orelse return error.UnsupportedShape;
        if (containsBoundaryEdge(boundary_edges, .{ .source = predecessor, .kind = .jump, .target = target }) or
            containsBoundaryEdge(boundary_edges, .{ .source = predecessor, .kind = .branch_then, .target = target }) or
            containsBoundaryEdge(boundary_edges, .{ .source = predecessor, .kind = .branch_else, .target = target })) continue;

        const incoming = edgeReferenceForTarget(analysis.program, predecessor, target) orelse return false;
        var matches: usize = 0;
        for (boundary_edges) |owner| {
            if (try context.hasAuthenticatedParameterizedCloneHandoffForEdge(analysis, owner, incoming)) {
                matches += 1;
            }
        }
        if (matches != 1) return false;
        _ = predecessor_index;
    }
    return true;
}
