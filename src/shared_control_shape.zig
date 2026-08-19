const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const natural_loop = @import("natural_loop.zig");

pub const Error = error{UnsupportedShape} || std.mem.Allocator.Error;

/// Finds a partial sibling convergence before a later boundary. Every path
/// from either branch arm must reach the candidate or the final boundary, so
/// neither sibling may claim the candidate independently.
pub fn selectConvergenceAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    branch: ir.BlockId,
    final_boundary: ir.BlockId,
    additional_boundaries: []const ir.BlockId,
    membership: []const bool,
) Error!?ir.BlockId {
    if (membership.len != analysis.function.blocks.len) return error.UnsupportedShape;
    const branch_index = analysis.blockIndex(branch) orelse return error.UnsupportedShape;
    _ = analysis.blockIndex(final_boundary) orelse return error.UnsupportedShape;
    if (!membership[branch_index]) return null;

    var boundaries: std.ArrayList(ir.BlockId) = .empty;
    defer boundaries.deinit(allocator);
    try appendUniqueBoundary(allocator, &boundaries, final_boundary);
    for (additional_boundaries) |boundary| {
        _ = analysis.blockIndex(boundary) orelse return error.UnsupportedShape;
        try appendUniqueBoundary(allocator, &boundaries, boundary);
    }
    for (analysis.function.blocks) |block_id| {
        if (analysis.isReachable(block_id) and isTerminal(analysis.program.blocks[block_id.index()].terminator)) {
            try appendUniqueBoundary(allocator, &boundaries, block_id);
        }
    }

    const branch_terminator = switch (analysis.program.blocks[branch.index()].terminator) {
        .branch => |value| value,
        else => return null,
    };
    const direct_candidates = [_]struct { candidate: ir.BlockId, other: ir.BlockId }{
        .{ .candidate = branch_terminator.then_edge.target, .other = branch_terminator.else_edge.target },
        .{ .candidate = branch_terminator.else_edge.target, .other = branch_terminator.then_edge.target },
    };
    var direct: ?ir.BlockId = null;
    for (direct_candidates) |item| {
        if (containsBoundary(boundaries.items, item.candidate) or !try analysis.allPathsReachTargetOrBoundariesAlloc(
            allocator,
            item.other,
            item.candidate,
            boundaries.items,
            null,
        )) continue;
        if (direct != null and direct.? != item.candidate) return null;
        direct = item.candidate;
    }
    if (direct) |candidate| return candidate;

    var candidate = (try analysis.immediateStructuralConvergenceBeforeAny(
        allocator,
        branch,
        boundaries.items,
        null,
    )) orelse return selectLoopConvergenceAlloc(
        allocator,
        analysis,
        branch,
        branch_terminator,
        boundaries.items,
    );
    const seen = try allocator.alloc(bool, analysis.function.blocks.len);
    defer allocator.free(seen);
    @memset(seen, false);
    seen[analysis.blockIndex(candidate) orelse return error.UnsupportedShape] = true;
    const refinement_boundaries = try allocator.alloc(ir.BlockId, boundaries.items.len + 1);
    defer allocator.free(refinement_boundaries);
    @memcpy(refinement_boundaries[1..], boundaries.items);
    while (true) {
        refinement_boundaries[0] = candidate;
        const earlier = (try analysis.immediateStructuralConvergenceBeforeAny(
            allocator,
            branch,
            refinement_boundaries,
            null,
        )) orelse break;
        if (containsBoundary(boundaries.items, earlier)) break;
        if (earlier == candidate or earlier == branch) return error.UnsupportedShape;
        const earlier_index = analysis.blockIndex(earlier) orelse return error.UnsupportedShape;
        if (seen[earlier_index]) break;
        seen[earlier_index] = true;
        candidate = earlier;
    }
    _ = analysis.blockIndex(candidate) orelse return error.UnsupportedShape;
    if (candidate == branch or containsBoundary(boundaries.items, candidate) or !analysis.isReachable(candidate) or
        !try reachesAnyBoundary(analysis, candidate, boundaries.items)) return selectLoopConvergenceAlloc(
        allocator,
        analysis,
        branch,
        branch_terminator,
        boundaries.items,
    );
    return candidate;
}

fn selectLoopConvergenceAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    branch: ir.BlockId,
    terminator: ir.Branch,
    boundaries: []const ir.BlockId,
) Error!?ir.BlockId {
    const then_reachable = try reachableBeforeAnyBoundaryAlloc(
        allocator,
        analysis,
        terminator.then_edge.target,
        boundaries,
    );
    defer allocator.free(then_reachable);
    const else_reachable = try reachableBeforeAnyBoundaryAlloc(
        allocator,
        analysis,
        terminator.else_edge.target,
        boundaries,
    );
    defer allocator.free(else_reachable);

    var selected: ?ir.BlockId = null;
    for (analysis.function.blocks) |candidate| {
        const candidate_index = analysis.blockIndex(candidate) orelse return error.UnsupportedShape;
        if (candidate == branch or containsBoundary(boundaries, candidate) or !analysis.isReachable(candidate) or
            !then_reachable[candidate_index] or
            !else_reachable[candidate_index] or
            !try reachesAnyBoundary(analysis, candidate, boundaries)) continue;

        var membership = (try natural_loop.collect(allocator, analysis, candidate)) orelse continue;
        membership.deinit();
        const then_paths = try allFiniteExitsReachTargetOrBoundariesAlloc(
            allocator,
            analysis,
            terminator.then_edge.target,
            candidate,
            boundaries,
        );
        const else_paths = try allFiniteExitsReachTargetOrBoundariesAlloc(
            allocator,
            analysis,
            terminator.else_edge.target,
            candidate,
            boundaries,
        );
        if (!then_paths or !else_paths) continue;

        if (selected) |existing| {
            const candidate_precedes = try analysis.canReach(candidate, existing);
            const existing_precedes = try analysis.canReach(existing, candidate);
            if (existing_precedes and !candidate_precedes) {
                selected = candidate;
            } else if (candidate_precedes == existing_precedes) {
                if (!candidate_precedes) return null;
                const candidate_dominates = analysis.dominates(candidate, existing);
                const existing_dominates = analysis.dominates(existing, candidate);
                if (candidate_dominates == existing_dominates) return null;
                if (candidate_dominates) selected = candidate;
            }
        } else {
            selected = candidate;
        }
    }
    return selected;
}

fn reachableBeforeAnyBoundaryAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    start: ir.BlockId,
    boundaries: []const ir.BlockId,
) Error![]bool {
    const visited = try allocator.alloc(bool, analysis.function.blocks.len);
    errdefer allocator.free(visited);
    @memset(visited, false);
    const pending = try allocator.alloc(ir.BlockId, analysis.function.blocks.len);
    defer allocator.free(pending);

    const start_index = analysis.blockIndex(start) orelse return error.UnsupportedShape;
    visited[start_index] = true;
    pending[0] = start;
    var cursor: usize = 0;
    var pending_len: usize = 1;
    while (cursor < pending_len) : (cursor += 1) {
        const current = pending[cursor];
        if (containsBoundary(boundaries, current)) continue;
        for (0..analysis.successorCount(current)) |successor_index| {
            const successor = analysis.successorAt(current, successor_index) orelse return error.UnsupportedShape;
            const local_index = analysis.blockIndex(successor) orelse return error.UnsupportedShape;
            if (visited[local_index]) continue;
            visited[local_index] = true;
            pending[pending_len] = successor;
            pending_len += 1;
        }
    }
    return visited;
}

fn allFiniteExitsReachTargetOrBoundariesAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    start: ir.BlockId,
    target: ir.BlockId,
    boundaries: []const ir.BlockId,
) Error!bool {
    const visited = try allocator.alloc(bool, analysis.function.blocks.len);
    defer allocator.free(visited);
    @memset(visited, false);
    const pending = try allocator.alloc(ir.BlockId, analysis.function.blocks.len);
    defer allocator.free(pending);

    const start_index = analysis.blockIndex(start) orelse return error.UnsupportedShape;
    visited[start_index] = true;
    pending[0] = start;
    var cursor: usize = 0;
    var pending_len: usize = 1;
    while (cursor < pending_len) : (cursor += 1) {
        const current = pending[cursor];
        if (current == target or containsBoundary(boundaries, current)) continue;
        if (isTerminal(analysis.program.blocks[current.index()].terminator)) return false;
        for (0..analysis.successorCount(current)) |successor_index| {
            const successor = analysis.successorAt(current, successor_index) orelse return error.UnsupportedShape;
            const local_index = analysis.blockIndex(successor) orelse return error.UnsupportedShape;
            if (visited[local_index]) continue;
            visited[local_index] = true;
            pending[pending_len] = successor;
            pending_len += 1;
        }
    }
    return true;
}

fn reachesAnyBoundary(
    analysis: *const cfg.Analysis,
    candidate: ir.BlockId,
    boundaries: []const ir.BlockId,
) std.mem.Allocator.Error!bool {
    for (boundaries) |boundary| if (try analysis.canReach(candidate, boundary)) return true;
    return false;
}

fn appendUniqueBoundary(
    allocator: std.mem.Allocator,
    boundaries: *std.ArrayList(ir.BlockId),
    candidate: ir.BlockId,
) std.mem.Allocator.Error!void {
    if (!containsBoundary(boundaries.items, candidate)) try boundaries.append(allocator, candidate);
}

fn containsBoundary(boundaries: []const ir.BlockId, candidate: ir.BlockId) bool {
    for (boundaries) |boundary| if (boundary == candidate) return true;
    return false;
}

fn isTerminal(terminator: ir.Terminator) bool {
    return switch (terminator) {
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => true,
        .jump, .branch => false,
    };
}

test "loop convergence after the final boundary is not shared control" {
    const function_id = ir.FunctionId.fromIndex(0);
    const branch = ir.BlockId.fromIndex(0);
    const then_arm = ir.BlockId.fromIndex(1);
    const else_arm = ir.BlockId.fromIndex(2);
    const boundary = ir.BlockId.fromIndex(3);
    const downstream_loop = ir.BlockId.fromIndex(4);
    const latch = ir.BlockId.fromIndex(5);
    const terminal = ir.BlockId.fromIndex(6);
    const blocks = [_]ir.Block{
        .{ .id = branch, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = then_arm },
            .else_edge = .{ .target = else_arm },
        } } },
        .{ .id = then_arm, .function = function_id, .terminator = .{ .jump = .{ .target = boundary } } },
        .{ .id = else_arm, .function = function_id, .terminator = .{ .jump = .{ .target = boundary } } },
        .{ .id = boundary, .function = function_id, .terminator = .{ .jump = .{ .target = downstream_loop } } },
        .{ .id = downstream_loop, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = latch },
            .else_edge = .{ .target = terminal },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .jump = .{ .target = downstream_loop } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .blocks = &.{ branch, then_arm, else_arm, boundary, downstream_loop, latch, terminal },
        .entry_block = branch,
    };
    const program: ir.Program = .{
        .program_id = "boundary-limited-shared-control",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const membership = [_]bool{true} ** blocks.len;
    try std.testing.expectEqual(
        @as(?ir.BlockId, null),
        try selectConvergenceAlloc(
            std.testing.allocator,
            &analysis,
            branch,
            boundary,
            &.{},
            &membership,
        ),
    );
}
