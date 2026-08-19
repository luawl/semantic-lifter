const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");

pub const Error = error{UnsupportedShape} || std.mem.Allocator.Error;

pub const Membership = struct {
    allocator: std.mem.Allocator,
    bits: []bool,
    header_index: usize,
    owns_bits: bool = true,

    pub fn deinit(self: *Membership) void {
        if (self.owns_bits) self.allocator.free(self.bits);
        self.* = undefined;
    }
};

pub const PostTested = struct {
    exit: ir.BlockId,
    latch_count: usize,
    single_latch: ?ir.BlockId,
    has_non_latch_backedge: bool,
};

pub const ExitShape = union(enum) {
    closed: void,
    unique: ir.BlockId,
    multiple: void,
};

pub const ExitLatches = struct {
    allocator: std.mem.Allocator,
    bits: []bool,
    count: usize,

    pub fn deinit(self: *ExitLatches) void {
        self.allocator.free(self.bits);
        self.* = undefined;
    }
};

pub fn collect(allocator: std.mem.Allocator, analysis: *const cfg.Analysis, header: ir.BlockId) Error!?Membership {
    const block_count = analysis.function.blocks.len;
    const membership = try allocator.alloc(bool, block_count);
    errdefer allocator.free(membership);
    @memset(membership, false);
    const stack = try allocator.alloc(ir.BlockId, block_count);
    defer allocator.free(stack);

    const header_index = analysis.blockIndex(header) orelse return error.UnsupportedShape;
    membership[header_index] = true;
    var stack_len: usize = 0;
    var has_backedge = false;
    // The CFG already owns the reverse edge index.  Walking every function
    // block for each loop candidate makes nested-loop discovery quadratic in
    // the function size before the actual reverse walk even starts.
    for (0..analysis.predecessorCount(header)) |predecessor_index| {
        const source = analysis.predecessorAt(header, predecessor_index) orelse return error.UnsupportedShape;
        if (!analysis.dominates(header, source)) continue;
        if (!terminatorTargets(analysis.program.blocks[source.index()].terminator, header)) continue;
        const source_local = analysis.blockIndex(source) orelse return error.UnsupportedShape;
        has_backedge = true;
        if (!membership[source_local]) {
            membership[source_local] = true;
            stack[stack_len] = source;
            stack_len += 1;
        }
    }
    if (!has_backedge) {
        allocator.free(membership);
        return null;
    }

    while (stack_len != 0) {
        stack_len -= 1;
        const block_id = stack[stack_len];
        for (0..analysis.predecessorCount(block_id)) |predecessor_index| {
            const predecessor = analysis.predecessorAt(block_id, predecessor_index) orelse return error.UnsupportedShape;
            if (!terminatorTargets(analysis.program.blocks[predecessor.index()].terminator, block_id)) continue;
            if (!analysis.dominates(header, predecessor)) continue;
            const local_index = analysis.blockIndex(predecessor) orelse return error.UnsupportedShape;
            if (membership[local_index]) continue;
            membership[local_index] = true;
            stack[stack_len] = predecessor;
            stack_len += 1;
        }
    }

    return .{
        .allocator = allocator,
        .bits = membership,
        .header_index = header_index,
    };
}

/// Collect the strongly connected component containing `header`.
///
/// Natural-loop collection intentionally requires header dominance.  An
/// irreducible loop has the same authenticated cycle but can have an entry
/// that bypasses the candidate header, so dominance cannot be used as its
/// ownership test.  Build the component from forward and reverse reachability
/// instead; callers still impose the semantic bridge and exit-shape checks
/// appropriate to the operation they are admitting.
pub fn collectStronglyConnected(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    header: ir.BlockId,
) Error!?Membership {
    const block_count = analysis.function.blocks.len;
    const header_index = analysis.blockIndex(header) orelse return error.UnsupportedShape;
    if (!analysis.isReachable(header) or
        !try analysis.canReachNonEmptyPath(header, header))
    {
        return null;
    }

    const forward = try allocator.alloc(bool, block_count);
    defer allocator.free(forward);
    const reverse = try allocator.alloc(bool, block_count);
    defer allocator.free(reverse);
    const queue = try allocator.alloc(ir.BlockId, block_count);
    defer allocator.free(queue);

    @memset(forward, false);
    forward[header_index] = true;
    queue[0] = header;
    var queue_len: usize = 1;
    var read_index: usize = 0;
    while (read_index < queue_len) : (read_index += 1) {
        const source = queue[read_index];
        for (0..analysis.successorCount(source)) |successor_index| {
            const successor = analysis.successorAt(source, successor_index) orelse
                return error.UnsupportedShape;
            const local_index = analysis.blockIndex(successor) orelse return error.UnsupportedShape;
            if (forward[local_index]) continue;
            forward[local_index] = true;
            queue[queue_len] = successor;
            queue_len += 1;
        }
    }

    @memset(reverse, false);
    reverse[header_index] = true;
    queue_len = 1;
    read_index = 0;
    queue[0] = header;
    while (read_index < queue_len) : (read_index += 1) {
        const target = queue[read_index];
        for (0..analysis.predecessorCount(target)) |predecessor_index| {
            const predecessor = analysis.predecessorAt(target, predecessor_index) orelse
                return error.UnsupportedShape;
            const local_index = analysis.blockIndex(predecessor) orelse return error.UnsupportedShape;
            if (reverse[local_index]) continue;
            reverse[local_index] = true;
            queue[queue_len] = predecessor;
            queue_len += 1;
        }
    }

    const membership = try allocator.alloc(bool, block_count);
    errdefer allocator.free(membership);
    for (membership, 0..) |*is_member, local_index| {
        is_member.* = forward[local_index] and reverse[local_index];
    }
    return .{
        .allocator = allocator,
        .bits = membership,
        .header_index = header_index,
    };
}

pub fn headerCandidatesAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
) std.mem.Allocator.Error![]bool {
    const candidates = try allocator.alloc(bool, analysis.function.blocks.len);
    @memset(candidates, false);

    // A natural loop header must dominate a reachable predecessor whose
    // terminator targets the header. Compute this necessary condition once so
    // callers can skip full membership walks for non-loop blocks.
    for (analysis.function.blocks) |source| {
        if (!analysis.isReachable(source)) continue;
        switch (analysis.program.blocks[source.index()].terminator) {
            .jump => |edge| markHeaderCandidate(analysis, candidates, source, edge.target),
            .branch => |branch| {
                markHeaderCandidate(analysis, candidates, source, branch.then_edge.target);
                markHeaderCandidate(analysis, candidates, source, branch.else_edge.target);
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
    }
    return candidates;
}

fn markHeaderCandidate(
    analysis: *const cfg.Analysis,
    candidates: []bool,
    source: ir.BlockId,
    target: ir.BlockId,
) void {
    const target_index = analysis.blockIndex(target) orelse return;
    if (analysis.isReachable(target) and analysis.dominates(target, source)) {
        candidates[target_index] = true;
    }
}

pub fn classifyPostTested(analysis: *const cfg.Analysis, header: ir.BlockId, membership: []const bool) Error!?PostTested {
    if (!terminatorStaysWithin(analysis, analysis.program.blocks[header.index()].terminator, membership)) return null;

    var exit_target: ?ir.BlockId = null;
    var latch_count: usize = 0;
    var single_latch: ?ir.BlockId = null;
    var has_non_latch_backedge = false;
    for (analysis.function.blocks) |source| {
        const source_index = analysis.blockIndex(source) orelse return error.UnsupportedShape;
        if (!membership[source_index]) continue;
        const terminator = analysis.program.blocks[source.index()].terminator;
        if (!terminatorTargets(terminator, header)) continue;
        const branch = switch (terminator) {
            .branch => |value| value,
            .jump => {
                has_non_latch_backedge = true;
                continue;
            },
            else => return null,
        };
        const then_is_backedge = branch.then_edge.target == header;
        const else_is_backedge = branch.else_edge.target == header;
        if (then_is_backedge and else_is_backedge) {
            has_non_latch_backedge = true;
            continue;
        }
        if (!then_is_backedge and !else_is_backedge) return null;
        const exit_edge = if (then_is_backedge) branch.else_edge else branch.then_edge;
        const exit_index = analysis.blockIndex(exit_edge.target) orelse return error.UnsupportedShape;
        if (membership[exit_index]) {
            has_non_latch_backedge = true;
            continue;
        }
        const canonical_exit = try canonicalExitTarget(analysis, membership, exit_edge.target);
        if (exit_target == null) exit_target = canonical_exit;
        latch_count += 1;
        single_latch = if (latch_count == 1) source else null;
    }
    return .{
        .exit = exit_target orelse return null,
        .latch_count = latch_count,
        .single_latch = single_latch,
        .has_non_latch_backedge = has_non_latch_backedge,
    };
}

test "post-tested classification retains distinct canonical latch exits for promotion" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const first_latch = ir.BlockId.fromIndex(1);
    const second_latch = ir.BlockId.fromIndex(2);
    const first_exit = ir.BlockId.fromIndex(3);
    const second_exit = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first_latch },
            .else_edge = .{ .target = second_latch },
        } } },
        .{ .id = first_latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = first_exit },
        } } },
        .{ .id = second_latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = second_exit },
        } } },
        .{ .id = first_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = second_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ header, first_latch, second_latch, first_exit, second_exit },
        .entry_block = header,
    }};
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program: ir.Program = .{
        .program_id = "distinct-post-tested-latch-exits",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const membership = [_]bool{ true, true, true, false, false };

    const shape = (try classifyPostTested(&analysis, header, &membership)).?;
    try std.testing.expectEqual(first_exit, shape.exit);
    try std.testing.expectEqual(@as(usize, 2), shape.latch_count);
}

test "post-tested latch collection accepts cleanup paths to a promoted exit" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const first_latch = ir.BlockId.fromIndex(1);
    const second_latch = ir.BlockId.fromIndex(2);
    const first_cleanup = ir.BlockId.fromIndex(3);
    const second_cleanup = ir.BlockId.fromIndex(4);
    const exit = ir.BlockId.fromIndex(5);
    const condition = ir.ValueId.fromIndex(0);
    const first_cleanup_parameter = ir.ValueId.fromIndex(1);
    const second_cleanup_parameter = ir.ValueId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first_latch },
            .else_edge = .{ .target = second_latch },
        } } },
        .{ .id = first_latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = first_cleanup, .arguments = &.{condition} },
        } } },
        .{ .id = second_latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = second_cleanup, .arguments = &.{condition} },
        } } },
        .{ .id = first_cleanup, .function = function_id, .parameters = &.{first_cleanup_parameter}, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = second_cleanup, .function = function_id, .parameters = &.{second_cleanup_parameter}, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ header, first_latch, second_latch, first_cleanup, second_cleanup, exit },
        .entry_block = header,
    }};
    const values = [_]ir.Value{
        .{
            .id = condition,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .parameter = 0 },
        },
        .{
            .id = first_cleanup_parameter,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .block_parameter = .{ .block = first_cleanup, .index = 0 } },
        },
        .{
            .id = second_cleanup_parameter,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .block_parameter = .{ .block = second_cleanup, .index = 0 } },
        },
    };
    const program: ir.Program = .{
        .program_id = "promoted-post-tested-latch-exit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const membership = [_]bool{ true, true, true, false, false, false };

    const shape = (try classifyPostTested(&analysis, header, &membership)).?;
    try std.testing.expectEqual(first_cleanup, shape.exit);
    var latches = try collectExitLatches(std.testing.allocator, &analysis, header, &membership, exit);
    defer latches.deinit();
    try std.testing.expectEqual(@as(usize, 2), latches.count);
    try std.testing.expect(latches.bits[1]);
    try std.testing.expect(latches.bits[2]);
}

test "continuing exit convergence preserves distance and id tie breaks" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const latch = ir.BlockId.fromIndex(1);
    const first_start = ir.BlockId.fromIndex(2);
    const second_start = ir.BlockId.fromIndex(3);
    const first_candidate = ir.BlockId.fromIndex(4);
    const second_candidate = ir.BlockId.fromIndex(5);
    const first_tail = ir.BlockId.fromIndex(6);
    const second_tail = ir.BlockId.fromIndex(7);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = latch },
            .else_edge = .{ .target = first_start },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = second_start },
        } } },
        .{ .id = first_start, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first_candidate },
            .else_edge = .{ .target = first_tail },
        } } },
        .{ .id = second_start, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = second_candidate },
            .else_edge = .{ .target = second_tail },
        } } },
        .{ .id = first_candidate, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = second_candidate, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = first_tail, .function = function_id, .terminator = .{ .jump = .{ .target = second_candidate } } },
        .{ .id = second_tail, .function = function_id, .terminator = .{ .jump = .{ .target = first_candidate } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{
            header,
            latch,
            first_start,
            second_start,
            first_candidate,
            second_candidate,
            first_tail,
            second_tail,
        },
        .entry_block = header,
    }};
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program: ir.Program = .{
        .program_id = "continuing-exit-convergence-tie-break",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const membership = [_]bool{ true, true, false, false, false, false, false, false };

    const selected = (try selectContinuingExitConvergenceAlloc(
        std.testing.allocator,
        &analysis,
        &membership,
    )).?;
    try std.testing.expectEqual(first_candidate, selected);
}

pub fn collectExitLatches(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    header: ir.BlockId,
    membership: []const bool,
    exit: ir.BlockId,
) Error!ExitLatches {
    if (membership.len != analysis.function.blocks.len) return error.UnsupportedShape;
    const bits = try allocator.alloc(bool, membership.len);
    errdefer allocator.free(bits);
    @memset(bits, false);

    var count: usize = 0;
    for (analysis.function.blocks, 0..) |source, source_index| {
        if (!membership[source_index]) continue;
        const branch = switch (analysis.program.blocks[source.index()].terminator) {
            .branch => |value| value,
            else => continue,
        };
        const then_is_backedge = branch.then_edge.target == header;
        const else_is_backedge = branch.else_edge.target == header;
        if (then_is_backedge == else_is_backedge) continue;
        const exit_edge = if (then_is_backedge) branch.else_edge else branch.then_edge;
        const exit_index = analysis.blockIndex(exit_edge.target) orelse return error.UnsupportedShape;
        if (membership[exit_index]) continue;
        const canonical_exit = try canonicalExitTarget(analysis, membership, exit_edge.target);
        if (canonical_exit != exit and
            !try canReachOutsideLoopAlloc(allocator, analysis, membership, exit_edge.target, exit)) continue;
        bits[source_index] = true;
        count += 1;
    }
    if (count == 0) return error.UnsupportedShape;
    return .{ .allocator = allocator, .bits = bits, .count = count };
}

pub fn isClosed(analysis: *const cfg.Analysis, membership: []const bool) bool {
    for (membership, 0..) |is_member, local_index| {
        if (!is_member) continue;
        const block_id = analysis.function.blocks[local_index];
        if (!terminatorStaysWithin(analysis, analysis.program.blocks[block_id.index()].terminator, membership)) return false;
    }
    return true;
}

pub fn classifyExit(analysis: *const cfg.Analysis, membership: []const bool) Error!ExitShape {
    return classifyExitAtBoundary(analysis, membership, null);
}

pub fn classifyExitAtBoundary(
    analysis: *const cfg.Analysis,
    membership: []const bool,
    boundary: ?ir.BlockId,
) Error!ExitShape {
    var exit: ?ir.BlockId = null;
    var multiple = false;
    var terminal_exit: ?ir.BlockId = null;
    var multiple_terminals = false;
    for (membership, 0..) |is_member, local_index| {
        if (!is_member) continue;
        const block_id = analysis.function.blocks[local_index];
        const terminator = analysis.program.blocks[block_id.index()].terminator;
        switch (terminator) {
            .jump => |edge| try includeExit(analysis, membership, edge.target, boundary, &exit, &multiple, &terminal_exit, &multiple_terminals),
            .branch => |branch| {
                try includeExit(analysis, membership, branch.then_edge.target, boundary, &exit, &multiple, &terminal_exit, &multiple_terminals);
                try includeExit(analysis, membership, branch.else_edge.target, boundary, &exit, &multiple, &terminal_exit, &multiple_terminals);
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return .{ .multiple = {} },
        }
        if (multiple) return .{ .multiple = {} };
    }
    if (exit) |target| return .{ .unique = target };
    if (!multiple_terminals) {
        if (terminal_exit) |target| return .{ .unique = target };
    }
    return .{ .closed = {} };
}

pub fn selectExitReaching(
    analysis: *const cfg.Analysis,
    membership: []const bool,
    continuation: ir.BlockId,
) Error!?ir.BlockId {
    if (membership.len != analysis.function.blocks.len) return error.UnsupportedShape;
    var selected: ?ir.BlockId = null;
    var multiple = false;
    for (membership, 0..) |is_member, local_index| {
        if (!is_member) continue;
        const block_id = analysis.function.blocks[local_index];
        const terminator = analysis.program.blocks[block_id.index()].terminator;
        switch (terminator) {
            .jump => |edge| try includeExitReaching(analysis, membership, edge.target, continuation, &selected, &multiple),
            .branch => |branch| {
                try includeExitReaching(analysis, membership, branch.then_edge.target, continuation, &selected, &multiple);
                try includeExitReaching(analysis, membership, branch.else_edge.target, continuation, &selected, &multiple);
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
        if (multiple) return null;
    }
    return selected;
}

pub fn allContinuingExitsReach(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    membership: []const bool,
    continuation: ir.BlockId,
) Error!bool {
    if (membership.len != analysis.function.blocks.len) return error.UnsupportedShape;
    const continuation_index = analysis.blockIndex(continuation) orelse return error.UnsupportedShape;
    if (membership[continuation_index] or !analysis.isReachable(continuation)) return false;

    // Every query below asks whether an outside edge target can reach the same
    // continuation while remaining outside the loop.  A forward BFS per edge
    // repeats the same suffix walk for every latch.  Compute the equivalent
    // reverse closure once, excluding loop members, then reuse it for all
    // outgoing edges.
    const outside_reachable = try allocator.alloc(bool, membership.len);
    defer allocator.free(outside_reachable);
    const pending = try allocator.alloc(ir.BlockId, membership.len);
    defer allocator.free(pending);
    @memset(outside_reachable, false);
    outside_reachable[continuation_index] = true;
    pending[0] = continuation;
    var pending_index: usize = 0;
    var pending_len: usize = 1;
    while (pending_index < pending_len) : (pending_index += 1) {
        const current = pending[pending_index];
        for (0..analysis.predecessorCount(current)) |predecessor_index| {
            const predecessor = analysis.predecessorAt(current, predecessor_index) orelse
                return error.UnsupportedShape;
            const predecessor_local = analysis.blockIndex(predecessor) orelse return error.UnsupportedShape;
            if (membership[predecessor_local] or
                outside_reachable[predecessor_local] or
                !analysis.isReachable(predecessor)) continue;
            outside_reachable[predecessor_local] = true;
            pending[pending_len] = predecessor;
            pending_len += 1;
        }
    }

    var found_continuing_exit = false;
    for (membership, 0..) |is_member, local_index| {
        if (!is_member) continue;
        const source = analysis.function.blocks[local_index];
        const outgoing = successorTargets(analysis.program.blocks[source.index()].terminator);
        for (outgoing.ids[0..outgoing.len]) |target| {
            const target_index = analysis.blockIndex(target) orelse return error.UnsupportedShape;
            if (membership[target_index]) continue;
            if (outside_reachable[target_index]) {
                found_continuing_exit = true;
                continue;
            }
            if (try outsidePathMustTerminateAlloc(allocator, analysis, membership, target)) continue;
            return false;
        }
    }
    return found_continuing_exit;
}

pub fn selectContinuingExitConvergenceAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    membership: []const bool,
) Error!?ir.BlockId {
    if (membership.len != analysis.function.blocks.len) return error.UnsupportedShape;
    const starts = try allocator.alloc(bool, membership.len);
    defer allocator.free(starts);
    @memset(starts, false);

    var start_count: usize = 0;
    for (membership, 0..) |is_member, source_index| {
        if (!is_member) continue;
        const source = analysis.function.blocks[source_index];
        const outgoing = successorTargets(analysis.program.blocks[source.index()].terminator);
        for (outgoing.ids[0..outgoing.len]) |target| {
            const target_index = analysis.blockIndex(target) orelse return error.UnsupportedShape;
            if (membership[target_index]) continue;
            if (!starts[target_index]) {
                starts[target_index] = true;
                start_count += 1;
            }
        }
    }
    if (start_count == 0) return null;
    for (starts, 0..) |is_start, start_index| {
        if (is_start and !analysis.isReachable(analysis.function.blocks[start_index])) return null;
    }

    // Compute one distance map per outside start, then fold those distances
    // into the candidate scores. The previous candidate-major walk repeated a
    // full BFS for every start/candidate pair, turning a loop with many exits
    // into a cubic planner hot spot while preserving the same score ordering.
    const candidate_valid = try allocator.alloc(bool, membership.len);
    defer allocator.free(candidate_valid);
    const candidate_maximums = try allocator.alloc(usize, membership.len);
    defer allocator.free(candidate_maximums);
    const candidate_totals = try allocator.alloc(usize, membership.len);
    defer allocator.free(candidate_totals);
    @memset(candidate_valid, false);
    @memset(candidate_maximums, 0);
    @memset(candidate_totals, 0);
    for (analysis.function.blocks, 0..) |candidate, candidate_index| {
        if (membership[candidate_index] or !analysis.isReachable(candidate)) continue;
        candidate_valid[candidate_index] = true;
    }

    const distances = try allocator.alloc(usize, membership.len);
    defer allocator.free(distances);
    const pending = try allocator.alloc(usize, membership.len);
    defer allocator.free(pending);
    const unseen = std.math.maxInt(usize);
    for (starts, 0..) |is_start, start_index| {
        if (!is_start) continue;
        try fillOutsideDistances(analysis, membership, start_index, distances, pending);
        for (candidate_valid, 0..) |valid, candidate_index| {
            if (!valid) continue;
            const distance = distances[candidate_index];
            if (distance == unseen) {
                candidate_valid[candidate_index] = false;
                continue;
            }
            candidate_maximums[candidate_index] = @max(candidate_maximums[candidate_index], distance);
            candidate_totals[candidate_index] = std.math.add(
                usize,
                candidate_totals[candidate_index],
                distance,
            ) catch {
                candidate_valid[candidate_index] = false;
                continue;
            };
        }
    }

    var selected: ?ir.BlockId = null;
    var selected_maximum: usize = std.math.maxInt(usize);
    var selected_total: usize = std.math.maxInt(usize);
    for (analysis.function.blocks, 0..) |candidate, candidate_index| {
        if (!candidate_valid[candidate_index]) continue;
        const maximum = candidate_maximums[candidate_index];
        const total = candidate_totals[candidate_index];
        if (maximum < selected_maximum or
            (maximum == selected_maximum and total < selected_total) or
            (maximum == selected_maximum and total == selected_total and
                (selected == null or candidate.index() < selected.?.index())))
        {
            selected = candidate;
            selected_maximum = maximum;
            selected_total = total;
        }
    }
    return selected;
}

pub fn outsidePathMustTerminateAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    membership: []const bool,
    start: ir.BlockId,
) Error!bool {
    if (membership.len != analysis.function.blocks.len) return error.UnsupportedShape;
    const start_index = analysis.blockIndex(start) orelse return error.UnsupportedShape;
    if (membership[start_index] or !analysis.isReachable(start)) return false;

    const active = try allocator.alloc(bool, membership.len);
    defer allocator.free(active);
    @memset(active, false);
    const pending = try allocator.alloc(ir.BlockId, membership.len);
    defer allocator.free(pending);
    active[start_index] = true;
    pending[0] = start;
    var pending_index: usize = 0;
    var pending_len: usize = 1;
    while (pending_index < pending_len) : (pending_index += 1) {
        const current = pending[pending_index];
        for (0..analysis.successorCount(current)) |successor_index| {
            const successor = analysis.successorAt(current, successor_index) orelse return error.UnsupportedShape;
            const local_index = analysis.blockIndex(successor) orelse return error.UnsupportedShape;
            if (membership[local_index]) return false;
            if (active[local_index]) continue;
            active[local_index] = true;
            pending[pending_len] = successor;
            pending_len += 1;
        }
    }

    const must_terminate = try allocator.alloc(bool, membership.len);
    defer allocator.free(must_terminate);
    @memset(must_terminate, false);
    const remaining_successors = try allocator.alloc(usize, membership.len);
    defer allocator.free(remaining_successors);
    @memset(remaining_successors, 0);

    // A node is terminating when it is a structured terminal or when every
    // outgoing edge reaches a node already proven terminating. Propagate that
    // fact backwards once instead of rescanning the entire active graph until
    // a fixed point. Cycles and dead ends never enter the worklist and remain
    // non-terminating, matching the old monotone fixed-point rule.
    var termination_queue_len: usize = 0;
    for (active, 0..) |is_active, local_index| {
        if (!is_active) continue;
        const block = analysis.function.blocks[local_index];
        if (isStructuredTerminal(analysis.program.blocks[block.index()].terminator)) {
            must_terminate[local_index] = true;
            pending[termination_queue_len] = block;
            termination_queue_len += 1;
        } else {
            remaining_successors[local_index] = analysis.successorCount(block);
        }
    }

    var termination_queue_index: usize = 0;
    while (termination_queue_index < termination_queue_len) : (termination_queue_index += 1) {
        const current = pending[termination_queue_index];
        const predecessor_count = analysis.predecessorCount(current);
        for (0..predecessor_count) |predecessor_index| {
            const predecessor = analysis.predecessorAt(current, predecessor_index) orelse return error.UnsupportedShape;
            const predecessor_local_index = analysis.blockIndex(predecessor) orelse return error.UnsupportedShape;
            if (!active[predecessor_local_index] or must_terminate[predecessor_local_index]) continue;
            if (remaining_successors[predecessor_local_index] == 0) return error.UnsupportedShape;
            remaining_successors[predecessor_local_index] -= 1;
            if (remaining_successors[predecessor_local_index] == 0) {
                must_terminate[predecessor_local_index] = true;
                pending[termination_queue_len] = predecessor;
                termination_queue_len += 1;
            }
        }
    }
    return must_terminate[start_index];
}

fn fillOutsideDistances(
    analysis: *const cfg.Analysis,
    membership: []const bool,
    start_index: usize,
    distances: []usize,
    pending: []usize,
) Error!void {
    const unseen = std.math.maxInt(usize);
    if (membership.len != analysis.function.blocks.len or
        distances.len != membership.len or
        pending.len != membership.len or
        start_index >= membership.len or
        membership[start_index] or
        !analysis.isReachable(analysis.function.blocks[start_index])) return error.UnsupportedShape;
    @memset(distances, unseen);
    distances[start_index] = 0;
    pending[0] = start_index;
    var pending_index: usize = 0;
    var pending_len: usize = 1;
    while (pending_index < pending_len) : (pending_index += 1) {
        const current_index = pending[pending_index];
        const current = analysis.function.blocks[current_index];
        const outgoing = successorTargets(analysis.program.blocks[current.index()].terminator);
        for (outgoing.ids[0..outgoing.len]) |successor| {
            const successor_index = analysis.blockIndex(successor) orelse return error.UnsupportedShape;
            if (membership[successor_index] or distances[successor_index] != unseen) continue;
            distances[successor_index] = distances[current_index] + 1;
            pending[pending_len] = successor_index;
            pending_len += 1;
        }
    }
}

pub fn canReachOutsideLoopAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    membership: []const bool,
    start: ir.BlockId,
    target: ir.BlockId,
) Error!bool {
    return canReachOutsideLoopWithBlockedAlloc(allocator, analysis, membership, start, target, null);
}

pub fn canReachOutsideLoopAvoidingAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    membership: []const bool,
    start: ir.BlockId,
    target: ir.BlockId,
    blocked: ir.BlockId,
) Error!bool {
    return canReachOutsideLoopWithBlockedAlloc(allocator, analysis, membership, start, target, blocked);
}

fn canReachOutsideLoopWithBlockedAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    membership: []const bool,
    start: ir.BlockId,
    target: ir.BlockId,
    blocked: ?ir.BlockId,
) Error!bool {
    const start_index = analysis.blockIndex(start) orelse return error.UnsupportedShape;
    const target_index = analysis.blockIndex(target) orelse return error.UnsupportedShape;
    if (membership[start_index] or membership[target_index] or
        !analysis.isReachable(start) or !analysis.isReachable(target)) return false;
    if (blocked != null and (start == blocked.? or target == blocked.?)) return false;

    const visited = try allocator.alloc(bool, membership.len);
    defer allocator.free(visited);
    @memset(visited, false);
    const pending = try allocator.alloc(ir.BlockId, membership.len);
    defer allocator.free(pending);
    visited[start_index] = true;
    pending[0] = start;
    var pending_index: usize = 0;
    var pending_len: usize = 1;
    while (pending_index < pending_len) : (pending_index += 1) {
        const current = pending[pending_index];
        if (current == target) return true;
        const outgoing = successorTargets(analysis.program.blocks[current.index()].terminator);
        for (outgoing.ids[0..outgoing.len]) |successor| {
            const successor_index = analysis.blockIndex(successor) orelse return error.UnsupportedShape;
            if ((blocked != null and successor == blocked.?) or membership[successor_index] or visited[successor_index]) continue;
            visited[successor_index] = true;
            pending[pending_len] = successor;
            pending_len += 1;
        }
    }
    return false;
}

fn includeExitReaching(
    analysis: *const cfg.Analysis,
    membership: []const bool,
    direct_target: ir.BlockId,
    continuation: ir.BlockId,
    selected: *?ir.BlockId,
    multiple: *bool,
) Error!void {
    const direct_index = analysis.blockIndex(direct_target) orelse return error.UnsupportedShape;
    if (membership[direct_index]) return;
    const candidate = try canonicalExitTarget(analysis, membership, direct_target);
    const candidate_index = analysis.blockIndex(candidate) orelse return error.UnsupportedShape;
    if (membership[candidate_index] or !try analysis.canReach(candidate, continuation)) return;
    includeDistinctExit(candidate, selected, multiple);
}

fn includeExit(
    analysis: *const cfg.Analysis,
    membership: []const bool,
    target: ir.BlockId,
    boundary: ?ir.BlockId,
    exit: *?ir.BlockId,
    multiple: *bool,
    terminal_exit: *?ir.BlockId,
    multiple_terminals: *bool,
) Error!void {
    const direct_index = analysis.blockIndex(target) orelse return error.UnsupportedShape;
    if (membership[direct_index]) return;
    if (isTerminal(analysis.program.blocks[target.index()].terminator)) {
        includeDistinctExit(target, terminal_exit, multiple_terminals);
        return;
    }

    const canonical_target = try canonicalExitTargetAtBoundary(analysis, membership, target, boundary);
    const target_index = analysis.blockIndex(canonical_target) orelse return error.UnsupportedShape;
    if (membership[target_index]) return;
    includeDistinctExit(canonical_target, exit, multiple);
}

fn includeDistinctExit(target: ir.BlockId, exit: *?ir.BlockId, multiple: *bool) void {
    if (exit.*) |existing| {
        if (existing != target) multiple.* = true;
    } else {
        exit.* = target;
    }
}

fn isTerminal(terminator: ir.Terminator) bool {
    return switch (terminator) {
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => true,
        .jump, .branch => false,
    };
}

fn isStructuredTerminal(terminator: ir.Terminator) bool {
    return switch (terminator) {
        .return_values, .return_pack, .return_expanded, .throw_error => true,
        .jump, .branch, .unreachable_block => false,
    };
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

fn canonicalExitTarget(analysis: *const cfg.Analysis, membership: []const bool, initial: ir.BlockId) Error!ir.BlockId {
    return canonicalExitTargetAtBoundary(analysis, membership, initial, null);
}

fn canonicalExitTargetAtBoundary(
    analysis: *const cfg.Analysis,
    membership: []const bool,
    initial: ir.BlockId,
    boundary: ?ir.BlockId,
) Error!ir.BlockId {
    var current = initial;
    var remaining = analysis.function.blocks.len + 1;
    while (remaining != 0) : (remaining -= 1) {
        if (boundary != null and current == boundary.?) return current;
        const current_index = analysis.blockIndex(current) orelse return error.UnsupportedShape;
        if (membership[current_index]) return current;
        const block = analysis.program.blocks[current.index()];
        if (block.parameters.len != 0 or block.instructions.len != 0) return current;
        const jump = switch (block.terminator) {
            .jump => |value| value,
            else => return current,
        };
        if (jump.arguments.len != 0 or jump.target == current) return current;
        current = jump.target;
    }
    return error.UnsupportedShape;
}

fn terminatorTargets(terminator: ir.Terminator, target: ir.BlockId) bool {
    return switch (terminator) {
        .jump => |edge| edge.target == target,
        .branch => |branch| branch.then_edge.target == target or branch.else_edge.target == target,
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => false,
    };
}

fn terminatorStaysWithin(analysis: *const cfg.Analysis, terminator: ir.Terminator, membership: []const bool) bool {
    return switch (terminator) {
        .jump => |edge| membership[analysis.blockIndex(edge.target) orelse return false],
        .branch => |branch| membership[analysis.blockIndex(branch.then_edge.target) orelse return false] and
            membership[analysis.blockIndex(branch.else_edge.target) orelse return false],
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => false,
    };
}
