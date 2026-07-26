const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const cfg_edge = @import("cfg_edge.zig");

pub const AuditError = error{UnsupportedShape} || std.mem.Allocator.Error;
pub const ValidationError = error{UnsupportedControlFlow} || std.mem.Allocator.Error;

pub const SharedPaths = struct {
    exit: ir.BlockId,
    blocks: []ir.BlockId,
    route_indices: []u32,
    entries: []Entry,

    pub const Entry = struct {
        reference: ir.CfgEdgeRef,
        route_start: u32,
        route_len: u32,
    };

    pub const EntryRef = struct {
        owner: *const SharedPaths,
        index: u32,

        pub fn value(self: EntryRef) ?Entry {
            if (self.index >= self.owner.entries.len) return null;
            return self.owner.entries[self.index];
        }
    };

    pub fn entryRef(self: *const SharedPaths, reference: ir.CfgEdgeRef) ?EntryRef {
        for (self.entries, 0..) |entry, index| {
            if (std.meta.eql(entry.reference, reference)) return .{ .owner = self, .index = @intCast(index) };
        }
        return null;
    }

    pub fn route(self: *const SharedPaths, entry: Entry) ?[]const u32 {
        const start: usize = entry.route_start;
        const end = std.math.add(usize, start, entry.route_len) catch return null;
        if (end > self.route_indices.len) return null;
        return self.route_indices[start..end];
    }

    pub fn deinit(self: *SharedPaths, allocator: std.mem.Allocator) void {
        allocator.free(self.entries);
        allocator.free(self.route_indices);
        allocator.free(self.blocks);
        allocator.destroy(self);
    }
};

const Candidate = struct {
    reference: ir.CfgEdgeRef,
    blocks: []ir.BlockId,
};

pub fn auditSharedAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    header: ir.BlockId,
    membership: []const bool,
    exit_latches: []const bool,
    exit: ir.BlockId,
) AuditError!?*SharedPaths {
    if (membership.len != analysis.function.blocks.len or exit_latches.len != membership.len) {
        return error.UnsupportedShape;
    }
    const header_index = analysis.blockIndex(header) orelse return error.UnsupportedShape;
    const exit_index = analysis.blockIndex(exit) orelse return error.UnsupportedShape;
    if (!membership[header_index] or membership[exit_index] or
        !analysis.isReachable(header) or !analysis.isReachable(exit)) return error.UnsupportedShape;

    const path_use_counts = try allocator.alloc(usize, membership.len);
    defer allocator.free(path_use_counts);
    @memset(path_use_counts, 0);
    var candidates: std.ArrayList(Candidate) = .empty;
    defer {
        for (candidates.items) |candidate| allocator.free(candidate.blocks);
        candidates.deinit(allocator);
    }

    var latch_count: usize = 0;
    for (analysis.function.blocks, exit_latches, 0..) |source, is_latch, source_index| {
        if (!is_latch) continue;
        if (!membership[source_index] or !analysis.isReachable(source)) return error.UnsupportedShape;
        latch_count += 1;
        const branch = switch (analysis.program.blocks[source.index()].terminator) {
            .branch => |value| value,
            else => return error.UnsupportedShape,
        };
        const then_is_backedge = branch.then_edge.target == header;
        const else_is_backedge = branch.else_edge.target == header;
        if (then_is_backedge == else_is_backedge) return error.UnsupportedShape;
        const kind: ir.CfgEdgeKind = if (then_is_backedge) .branch_else else .branch_then;
        const edge = if (then_is_backedge) branch.else_edge else branch.then_edge;
        const edge_index = analysis.blockIndex(edge.target) orelse return error.UnsupportedShape;
        if (membership[edge_index]) return error.UnsupportedShape;
        if (edge.target == exit) continue;
        const blocks = try replayCanonicalRouteAlloc(allocator, analysis.program, edge, exit);
        errdefer allocator.free(blocks);
        if (blocks.len == 0) return error.UnsupportedShape;
        for (blocks) |block_id| {
            const block_index = analysis.blockIndex(block_id) orelse return error.UnsupportedShape;
            if (membership[block_index] or !analysis.isReachable(block_id)) return error.UnsupportedShape;
            path_use_counts[block_index] += 1;
        }
        try candidates.append(allocator, .{
            .reference = .{ .source = source, .kind = kind, .target = edge.target },
            .blocks = blocks,
        });
    }
    if (latch_count == 0) return error.UnsupportedShape;

    for (candidates.items) |candidate| {
        for (candidate.blocks) |block_id| {
            if (!hasExactPredecessors(analysis, candidates.items, block_id)) return error.UnsupportedShape;
        }
    }

    var shared_candidate_count: usize = 0;
    for (candidates.items) |candidate| {
        if (usesSharedBlock(analysis, candidate, path_use_counts)) shared_candidate_count += 1;
    }
    if (shared_candidate_count == 0) return null;

    var blocks: std.ArrayList(ir.BlockId) = .empty;
    defer blocks.deinit(allocator);
    var route_indices: std.ArrayList(u32) = .empty;
    defer route_indices.deinit(allocator);
    var entries: std.ArrayList(SharedPaths.Entry) = .empty;
    defer entries.deinit(allocator);
    for (candidates.items) |candidate| {
        if (!usesSharedBlock(analysis, candidate, path_use_counts)) continue;
        const route_start = route_indices.items.len;
        for (candidate.blocks) |block_id| {
            const block_index = ownerBlockIndex(blocks.items, block_id) orelse add: {
                try blocks.append(allocator, block_id);
                break :add blocks.items.len - 1;
            };
            try route_indices.append(allocator, @intCast(block_index));
        }
        try entries.append(allocator, .{
            .reference = candidate.reference,
            .route_start = @intCast(route_start),
            .route_len = @intCast(candidate.blocks.len),
        });
    }

    const owned_blocks = try blocks.toOwnedSlice(allocator);
    errdefer allocator.free(owned_blocks);
    const owned_routes = try route_indices.toOwnedSlice(allocator);
    errdefer allocator.free(owned_routes);
    const owned_entries = try entries.toOwnedSlice(allocator);
    errdefer allocator.free(owned_entries);
    const result = try allocator.create(SharedPaths);
    result.* = .{
        .exit = exit,
        .blocks = owned_blocks,
        .route_indices = owned_routes,
        .entries = owned_entries,
    };
    return result;
}

pub fn validateAllAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    shared: *const SharedPaths,
) ValidationError!void {
    if (shared.blocks.len == 0 or shared.entries.len < 2 or shared.exit.index() >= program.blocks.len) {
        return error.UnsupportedControlFlow;
    }
    const used_blocks = try allocator.alloc(bool, shared.blocks.len);
    defer allocator.free(used_blocks);
    @memset(used_blocks, false);
    for (shared.blocks, 0..) |block_id, index| {
        if (block_id.index() >= program.blocks.len) return error.UnsupportedControlFlow;
        for (shared.blocks[0..index]) |previous| if (previous == block_id) return error.UnsupportedControlFlow;
    }
    for (shared.entries, 0..) |entry, index| {
        for (shared.entries[0..index]) |previous| {
            if (std.meta.eql(previous.reference, entry.reference)) return error.UnsupportedControlFlow;
        }
        try validateEntryAlloc(allocator, program, .{ .owner = shared, .index = @intCast(index) });
        const route = shared.route(entry) orelse return error.UnsupportedControlFlow;
        for (route) |block_index| {
            if (block_index >= used_blocks.len) return error.UnsupportedControlFlow;
            used_blocks[block_index] = true;
        }
    }
    for (used_blocks) |used| if (!used) return error.UnsupportedControlFlow;
}

pub fn validateEntryAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    entry_ref: SharedPaths.EntryRef,
) ValidationError!void {
    const entry = entry_ref.value() orelse return error.UnsupportedControlFlow;
    if (cfg_edge.target(program, entry.reference) != entry.reference.target) return error.UnsupportedControlFlow;
    const raw = cfg_edge.value(program, entry.reference) orelse return error.UnsupportedControlFlow;
    const replayed = replayCanonicalRouteAlloc(allocator, program, raw, entry_ref.owner.exit) catch |err| switch (err) {
        error.UnsupportedShape => return error.UnsupportedControlFlow,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer allocator.free(replayed);
    const route = entry_ref.owner.route(entry) orelse return error.UnsupportedControlFlow;
    if (route.len != replayed.len) return error.UnsupportedControlFlow;
    for (route, replayed) |block_index, block_id| {
        if (block_index >= entry_ref.owner.blocks.len or entry_ref.owner.blocks[block_index] != block_id) {
            return error.UnsupportedControlFlow;
        }
    }
}

fn replayCanonicalRouteAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    initial: ir.Edge,
    exit: ir.BlockId,
) AuditError![]ir.BlockId {
    if (initial.arguments.len != 0) return error.UnsupportedShape;
    var blocks: std.ArrayList(ir.BlockId) = .empty;
    defer blocks.deinit(allocator);
    var current = initial.target;
    var remaining = program.blocks.len + 1;
    while (current != exit and remaining != 0) : (remaining -= 1) {
        if (current.index() >= program.blocks.len) return error.UnsupportedShape;
        for (blocks.items) |visited| if (visited == current) return error.UnsupportedShape;
        const block = program.blocks[current.index()];
        if (block.parameters.len != 0 or block.instructions.len != 0) return error.UnsupportedShape;
        const jump = switch (block.terminator) {
            .jump => |value| value,
            else => return error.UnsupportedShape,
        };
        if (jump.arguments.len != 0 or jump.target == current) return error.UnsupportedShape;
        try blocks.append(allocator, current);
        current = jump.target;
    }
    if (current != exit) return error.UnsupportedShape;
    return try blocks.toOwnedSlice(allocator);
}

fn usesSharedBlock(analysis: *const cfg.Analysis, candidate: Candidate, counts: []const usize) bool {
    for (candidate.blocks) |block_id| {
        const block_index = analysis.blockIndex(block_id) orelse return false;
        if (counts[block_index] > 1) return true;
    }
    return false;
}

fn ownerBlockIndex(blocks: []const ir.BlockId, needle: ir.BlockId) ?usize {
    for (blocks, 0..) |block_id, index| if (block_id == needle) return index;
    return null;
}

fn hasExactPredecessors(analysis: *const cfg.Analysis, candidates: []const Candidate, block_id: ir.BlockId) bool {
    const expected_count = expectedPredecessorCount(candidates, block_id);
    if (expected_count == 0 or analysis.predecessorCount(block_id) != expected_count) return false;
    for (0..expected_count) |index| {
        const predecessor = analysis.predecessorAt(block_id, index) orelse return false;
        if (!isExpectedPredecessor(candidates, block_id, predecessor)) return false;
    }
    return true;
}

fn expectedPredecessorCount(candidates: []const Candidate, block_id: ir.BlockId) usize {
    var count: usize = 0;
    for (candidates, 0..) |candidate, candidate_index| {
        for (candidate.blocks, 0..) |candidate_block, route_index| {
            if (candidate_block != block_id) continue;
            const predecessor = if (route_index == 0) candidate.reference.source else candidate.blocks[route_index - 1];
            if (!predecessorAppearedBefore(candidates, block_id, predecessor, candidate_index)) count += 1;
        }
    }
    return count;
}

fn predecessorAppearedBefore(
    candidates: []const Candidate,
    block_id: ir.BlockId,
    predecessor: ir.BlockId,
    before_candidate: usize,
) bool {
    for (candidates[0..before_candidate]) |candidate| {
        for (candidate.blocks, 0..) |candidate_block, route_index| {
            if (candidate_block != block_id) continue;
            const previous = if (route_index == 0) candidate.reference.source else candidate.blocks[route_index - 1];
            if (previous == predecessor) return true;
        }
    }
    return false;
}

fn isExpectedPredecessor(candidates: []const Candidate, block_id: ir.BlockId, predecessor: ir.BlockId) bool {
    for (candidates) |candidate| {
        for (candidate.blocks, 0..) |candidate_block, route_index| {
            if (candidate_block != block_id) continue;
            const expected = if (route_index == 0) candidate.reference.source else candidate.blocks[route_index - 1];
            if (expected == predecessor) return true;
        }
    }
    return false;
}
