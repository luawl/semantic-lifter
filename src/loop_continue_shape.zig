const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const control_flow = @import("control_flow.zig");

pub const AuditError = error{UnsupportedShape} || std.mem.Allocator.Error;

pub const SharedPaths = struct {
    header: ir.BlockId,
    blocks: []ir.BlockId,
    route_indices: []u32,
    entries: []Entry,

    pub const Entry = struct {
        reference: ir.CfgEdgeRef,
        edge: ir.Edge,
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
        const len: usize = entry.route_len;
        const end = std.math.add(usize, start, len) catch return null;
        if (end > self.route_indices.len) return null;
        return self.route_indices[start..end];
    }

    pub fn deinit(self: *SharedPaths, allocator: std.mem.Allocator) void {
        freeEntries(allocator, self.entries);
        allocator.free(self.entries);
        allocator.free(self.route_indices);
        allocator.free(self.blocks);
        allocator.destroy(self);
    }
};

const Candidate = struct {
    reference: ir.CfgEdgeRef,
    path: control_flow.ForwardingPath,
};

pub const Reentry = struct {
    reenters: bool = false,
    edge_override: ?control_flow.ForwardingPath = null,
    shared_reentry: ?SharedPaths.EntryRef = null,

    pub fn takeEdgeOverride(self: *Reentry) ?control_flow.ForwardingPath {
        const path = self.edge_override;
        self.edge_override = null;
        return path;
    }

    pub fn structuredEdge(self: Reentry, raw: ir.Edge) error{UnsupportedShape}!ir.Edge {
        if (self.edge_override) |path| return path.edge;
        if (self.shared_reentry) |reference| {
            const entry = reference.value() orelse return error.UnsupportedShape;
            return entry.edge;
        }
        return raw;
    }

    pub fn deinit(self: *Reentry, allocator: std.mem.Allocator) void {
        if (self.edge_override) |value| {
            var path = value;
            path.deinit(allocator);
        }
        self.edge_override = null;
    }
};

pub fn classifyArmAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    shared: ?*const SharedPaths,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    edge: ir.Edge,
    header: ir.BlockId,
    membership: ?[]const bool,
) AuditError!Reentry {
    if (edge.target == header) return .{ .reenters = true };
    if (shared) |owner| {
        if (owner.entryRef(.{ .source = source, .kind = kind, .target = edge.target })) |entry| {
            const mapped = entry.value() orelse return error.UnsupportedShape;
            if (owner.header != header or mapped.edge.target != header) return error.UnsupportedShape;
            return .{ .reenters = true, .shared_reentry = entry };
        }
    }
    const allowed = membership orelse return .{};
    const target_index = analysis.blockIndex(edge.target) orelse return .{};
    if (!allowed[target_index] or analysis.predecessorCount(edge.target) != 1) return .{};
    const target = analysis.program.blocks[edge.target.index()];
    const jump = switch (target.terminator) {
        .jump => |forwarded| forwarded,
        else => return .{},
    };
    if (target.parameters.len == 0 and target.instructions.len == 0 and
        edge.arguments.len == 0 and jump.target == header) return .{ .reenters = true };

    var path = try control_flow.replayForwardingPathTo(allocator, analysis.program, edge, header) orelse return .{};
    var owns_path = true;
    defer if (owns_path) path.deinit(allocator);
    var previous: ?ir.BlockId = null;
    for (path.blocks) |block_id| {
        const block_index = analysis.blockIndex(block_id) orelse return .{};
        if (!allowed[block_index] or !analysis.isReachable(block_id) or
            analysis.predecessorCount(block_id) != 1) return .{};
        if (previous) |expected| {
            if (analysis.predecessorAt(block_id, 0) != expected) return .{};
        }
        previous = block_id;
    }
    owns_path = false;
    return .{ .reenters = true, .edge_override = path };
}

pub fn auditAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    header: ir.BlockId,
    membership: []const bool,
    exit_latches: []const bool,
) AuditError!?*SharedPaths {
    if (membership.len != analysis.function.blocks.len or exit_latches.len != membership.len) {
        return error.UnsupportedShape;
    }
    if (std.mem.countScalar(bool, exit_latches, true) == 0) return error.UnsupportedShape;
    const direct_sources = try allocator.alloc(bool, analysis.function.blocks.len);
    defer allocator.free(direct_sources);
    @memset(direct_sources, false);
    const claimed_blocks = try allocator.alloc(bool, analysis.function.blocks.len);
    defer allocator.free(claimed_blocks);
    @memset(claimed_blocks, false);
    const path_use_counts = try allocator.alloc(usize, analysis.function.blocks.len);
    defer allocator.free(path_use_counts);
    @memset(path_use_counts, 0);

    var candidates: std.ArrayList(Candidate) = .empty;
    defer {
        for (candidates.items) |*candidate| candidate.path.deinit(allocator);
        candidates.deinit(allocator);
    }

    var continue_count: usize = 0;
    for (analysis.function.blocks) |source| {
        const source_index = analysis.blockIndex(source) orelse return error.UnsupportedShape;
        if (!membership[source_index] or exit_latches[source_index]) continue;
        const branch = switch (analysis.program.blocks[source.index()].terminator) {
            .branch => |value| value,
            else => continue,
        };
        const edges = [_]ir.Edge{ branch.then_edge, branch.else_edge };
        const kinds = [_]ir.CfgEdgeKind{ .branch_then, .branch_else };
        var continue_arm: ?usize = null;
        for (edges, kinds, 0..) |edge, kind, edge_index| {
            if (edge.target == header) {
                if (continue_arm != null or !try siblingReachesLatch(analysis, membership, exit_latches, edges[1 - edge_index], header)) {
                    return error.UnsupportedShape;
                }
                direct_sources[source_index] = true;
                continue_arm = edge_index;
                continue_count += 1;
                continue;
            }

            var path = try control_flow.replayForwardingPathTo(allocator, analysis.program, edge, header) orelse continue;
            if (continue_arm != null or path.blocks.len == 0 or
                !try siblingReachesLatch(analysis, membership, exit_latches, edges[1 - edge_index], header))
            {
                path.deinit(allocator);
                return error.UnsupportedShape;
            }
            candidates.append(allocator, .{
                .reference = .{ .source = source, .kind = kind, .target = edge.target },
                .path = path,
            }) catch |err| {
                path.deinit(allocator);
                return err;
            };
            continue_arm = edge_index;
            continue_count += 1;
        }
    }
    if (continue_count == 0) return error.UnsupportedShape;

    for (candidates.items) |candidate| {
        for (candidate.path.blocks) |block_id| {
            const block_index = analysis.blockIndex(block_id) orelse return error.UnsupportedShape;
            if (!membership[block_index] or !analysis.isReachable(block_id)) return error.UnsupportedShape;
            claimed_blocks[block_index] = true;
            path_use_counts[block_index] += 1;
        }
    }
    for (candidates.items) |candidate| {
        for (candidate.path.blocks) |block_id| {
            if (!hasExactPredecessors(analysis, candidates.items, block_id)) return error.UnsupportedShape;
        }
    }

    for (analysis.function.blocks) |source| {
        const source_index = analysis.blockIndex(source) orelse return error.UnsupportedShape;
        if (!membership[source_index] or exit_latches[source_index]) continue;
        switch (analysis.program.blocks[source.index()].terminator) {
            .jump => |edge| if (edge.target == header and !claimed_blocks[source_index]) return error.UnsupportedShape,
            .branch => |branch| {
                if ((branch.then_edge.target == header or branch.else_edge.target == header) and
                    !direct_sources[source_index]) return error.UnsupportedShape;
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
    }

    var shared_candidate_count: usize = 0;
    for (candidates.items) |candidate| {
        if (candidateUsesSharedBlock(analysis, candidate, path_use_counts)) shared_candidate_count += 1;
    }
    if (shared_candidate_count == 0) return null;

    var blocks: std.ArrayList(ir.BlockId) = .empty;
    defer blocks.deinit(allocator);
    var route_indices: std.ArrayList(u32) = .empty;
    defer route_indices.deinit(allocator);
    var entries: std.ArrayList(SharedPaths.Entry) = .empty;
    defer {
        freeEntries(allocator, entries.items);
        entries.deinit(allocator);
    }

    for (candidates.items) |candidate| {
        if (!candidateUsesSharedBlock(analysis, candidate, path_use_counts)) continue;
        const route_start = route_indices.items.len;
        for (candidate.path.blocks) |block_id| {
            const block_index = ownerBlockIndex(blocks.items, block_id) orelse add: {
                try blocks.append(allocator, block_id);
                break :add blocks.items.len - 1;
            };
            try route_indices.append(allocator, @intCast(block_index));
        }
        const arguments = if (candidate.path.edge.arguments.len == 0)
            &.{}
        else
            try allocator.dupe(ir.ValueId, candidate.path.edge.arguments);
        entries.append(allocator, .{
            .reference = candidate.reference,
            .edge = .{ .target = candidate.path.edge.target, .arguments = arguments },
            .route_start = @intCast(route_start),
            .route_len = @intCast(candidate.path.blocks.len),
        }) catch |err| {
            if (arguments.len != 0) allocator.free(arguments);
            return err;
        };
    }

    const owned_blocks = try blocks.toOwnedSlice(allocator);
    errdefer allocator.free(owned_blocks);
    const owned_routes = try route_indices.toOwnedSlice(allocator);
    errdefer allocator.free(owned_routes);
    const owned_entries = try entries.toOwnedSlice(allocator);
    errdefer {
        freeEntries(allocator, owned_entries);
        allocator.free(owned_entries);
    }
    const result = try allocator.create(SharedPaths);
    result.* = .{
        .header = header,
        .blocks = owned_blocks,
        .route_indices = owned_routes,
        .entries = owned_entries,
    };
    return result;
}

fn siblingReachesLatch(
    analysis: *const cfg.Analysis,
    membership: []const bool,
    exit_latches: []const bool,
    sibling: ir.Edge,
    header: ir.BlockId,
) std.mem.Allocator.Error!bool {
    const sibling_index = analysis.blockIndex(sibling.target) orelse return false;
    if (sibling.target == header or !membership[sibling_index]) return false;
    for (analysis.function.blocks, exit_latches) |latch, is_latch| {
        if (is_latch and try analysis.canReach(sibling.target, latch)) return true;
    }
    return false;
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
        for (candidate.path.blocks, 0..) |candidate_block, route_index| {
            if (candidate_block != block_id) continue;
            const predecessor = if (route_index == 0) candidate.reference.source else candidate.path.blocks[route_index - 1];
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
        for (candidate.path.blocks, 0..) |candidate_block, route_index| {
            if (candidate_block != block_id) continue;
            const previous = if (route_index == 0) candidate.reference.source else candidate.path.blocks[route_index - 1];
            if (previous == predecessor) return true;
        }
    }
    return false;
}

fn isExpectedPredecessor(candidates: []const Candidate, block_id: ir.BlockId, predecessor: ir.BlockId) bool {
    for (candidates) |candidate| {
        for (candidate.path.blocks, 0..) |candidate_block, route_index| {
            if (candidate_block != block_id) continue;
            const expected = if (route_index == 0) candidate.reference.source else candidate.path.blocks[route_index - 1];
            if (expected == predecessor) return true;
        }
    }
    return false;
}

fn candidateUsesSharedBlock(analysis: *const cfg.Analysis, candidate: Candidate, path_use_counts: []const usize) bool {
    for (candidate.path.blocks) |block_id| {
        const block_index = analysis.blockIndex(block_id) orelse return false;
        if (path_use_counts[block_index] > 1) return true;
    }
    return false;
}

fn ownerBlockIndex(blocks: []const ir.BlockId, block_id: ir.BlockId) ?usize {
    for (blocks, 0..) |candidate, index| if (candidate == block_id) return index;
    return null;
}

fn freeEntries(allocator: std.mem.Allocator, entries: []const SharedPaths.Entry) void {
    for (entries) |entry| if (entry.edge.arguments.len != 0) allocator.free(entry.edge.arguments);
}
