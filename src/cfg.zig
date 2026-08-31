const std = @import("std");
const ir = @import("ir.zig");

pub const AnalysisError = error{InvalidCfg} || std.mem.Allocator.Error;

const PartialConvergencePolicy = enum {
    terminal_only,
    non_fallthrough,
};

/// Mark one function's reachable blocks without constructing dominator or
/// postdominator state. Readable-scope construction only needs this subset of
/// CFG analysis, while the full Analysis remains the authority for structure.
pub fn markReachable(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function: ir.Function,
    reachable: []bool,
) AnalysisError!void {
    if (function.blocks.len == 0 or reachable.len < program.blocks.len) return error.InvalidCfg;

    const local_index = try allocator.alloc(?u32, program.blocks.len);
    defer allocator.free(local_index);
    @memset(local_index, null);

    for (function.blocks, 0..) |block_id, index| {
        if (block_id.index() >= program.blocks.len or
            program.blocks[block_id.index()].function != function.id or
            local_index[block_id.index()] != null)
        {
            return error.InvalidCfg;
        }
        local_index[block_id.index()] = @intCast(index);
    }
    if (function.entry_block.index() >= local_index.len or local_index[function.entry_block.index()] == null) {
        return error.InvalidCfg;
    }
    for (function.blocks) |block_id| {
        const outgoing = successors(program.blocks[block_id.index()].terminator);
        for (outgoing.slice()) |target| {
            if (localBlockIndex(local_index, target) == null) return error.InvalidCfg;
        }
    }

    for (function.blocks) |block_id| reachable[block_id.index()] = false;
    const stack = try allocator.alloc(u32, function.blocks.len);
    defer allocator.free(stack);

    const entry_local = local_index[function.entry_block.index()].?;
    var stack_len: usize = 1;
    stack[0] = entry_local;
    reachable[function.entry_block.index()] = true;
    while (stack_len != 0) {
        stack_len -= 1;
        const source_id = function.blocks[stack[stack_len]];
        const outgoing = successors(program.blocks[source_id.index()].terminator);
        for (outgoing.slice()) |target| {
            const target_local = localBlockIndex(local_index, target) orelse return error.InvalidCfg;
            if (reachable[target.index()]) continue;
            reachable[target.index()] = true;
            stack[stack_len] = @intCast(target_local);
            stack_len += 1;
        }
    }
}

pub const Analysis = struct {
    const BlockedReachabilityKey = struct {
        start: usize,
        blocked: usize,
    };

    const ReachabilityCache = struct {
        unrestricted_reachability_rows: std.AutoHashMapUnmanaged(usize, []bool) = .empty,
        blocked_reachability_rows: std.AutoHashMapUnmanaged(BlockedReachabilityKey, []usize) = .empty,
    };

    const blocked_reachability_cache_limit: usize = 1_024;

    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function: ir.Function,
    local_index: []?u32,
    predecessor_offsets: []usize,
    predecessors: []u32,
    reachable: []bool,
    can_reach_exit: []bool,
    dominator_words: []usize,
    postdominator_words: []usize,
    words_per_row: usize,
    immediate_postdominators: []?ir.BlockId,
    immediate_postdominator_computed: []bool,
    reachability_cache: *ReachabilityCache,
    reachability_scratch: []bool,
    reachability_queue: []u32,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program, function: ir.Function) AnalysisError!Analysis {
        const block_count = function.blocks.len;
        if (block_count == 0) return error.InvalidCfg;

        const local_index = try allocator.alloc(?u32, program.blocks.len);
        errdefer allocator.free(local_index);
        @memset(local_index, null);

        for (function.blocks, 0..) |block_id, index| {
            if (block_id.index() >= program.blocks.len) return error.InvalidCfg;
            if (program.blocks[block_id.index()].function != function.id) return error.InvalidCfg;
            if (local_index[block_id.index()] != null) return error.InvalidCfg;
            local_index[block_id.index()] = @intCast(index);
        }
        if (function.entry_block.index() >= local_index.len or local_index[function.entry_block.index()] == null) return error.InvalidCfg;

        const predecessor_counts = try allocator.alloc(usize, block_count);
        defer allocator.free(predecessor_counts);
        @memset(predecessor_counts, 0);

        for (function.blocks) |block_id| {
            const outgoing = successors(program.blocks[block_id.index()].terminator);
            for (outgoing.slice()) |target| {
                const target_local = localBlockIndex(local_index, target) orelse return error.InvalidCfg;
                predecessor_counts[target_local] = std.math.add(usize, predecessor_counts[target_local], 1) catch return error.InvalidCfg;
            }
        }

        const predecessor_offsets = try allocator.alloc(usize, block_count + 1);
        errdefer allocator.free(predecessor_offsets);
        predecessor_offsets[0] = 0;
        for (predecessor_counts, 0..) |count, index| {
            predecessor_offsets[index + 1] = std.math.add(usize, predecessor_offsets[index], count) catch return error.InvalidCfg;
        }

        const predecessors = try allocator.alloc(u32, predecessor_offsets[block_count]);
        errdefer allocator.free(predecessors);
        const cursors = try allocator.dupe(usize, predecessor_offsets[0..block_count]);
        defer allocator.free(cursors);

        for (function.blocks, 0..) |block_id, source_local| {
            const outgoing = successors(program.blocks[block_id.index()].terminator);
            for (outgoing.slice()) |target| {
                const target_local = localBlockIndex(local_index, target).?;
                predecessors[cursors[target_local]] = @intCast(source_local);
                cursors[target_local] += 1;
            }
        }

        const reachable = try allocator.alloc(bool, block_count);
        errdefer allocator.free(reachable);
        @memset(reachable, false);

        const reachability_scratch = try allocator.alloc(bool, block_count);
        errdefer allocator.free(reachability_scratch);
        const reachability_queue = try allocator.alloc(u32, block_count);
        errdefer allocator.free(reachability_queue);

        const can_reach_exit = try allocator.alloc(bool, block_count);
        errdefer allocator.free(can_reach_exit);
        @memset(can_reach_exit, false);

        const word_bits = @bitSizeOf(usize);
        const words_per_row = (block_count + word_bits - 1) / word_bits;
        const dominator_word_count = std.math.mul(usize, block_count, words_per_row) catch return error.InvalidCfg;
        const dominator_words = try allocator.alloc(usize, dominator_word_count);
        errdefer allocator.free(dominator_words);
        @memset(dominator_words, 0);
        const postdominator_words = try allocator.alloc(usize, dominator_word_count);
        errdefer allocator.free(postdominator_words);
        @memset(postdominator_words, 0);

        const immediate_postdominators = try allocator.alloc(?ir.BlockId, block_count);
        errdefer allocator.free(immediate_postdominators);
        @memset(immediate_postdominators, null);
        const immediate_postdominator_computed = try allocator.alloc(bool, block_count);
        errdefer allocator.free(immediate_postdominator_computed);
        @memset(immediate_postdominator_computed, false);

        const reachability_cache = try allocator.create(ReachabilityCache);
        reachability_cache.* = .{};

        var analysis: Analysis = .{
            .allocator = allocator,
            .program = program,
            .function = function,
            .local_index = local_index,
            .predecessor_offsets = predecessor_offsets,
            .predecessors = predecessors,
            .reachable = reachable,
            .can_reach_exit = can_reach_exit,
            .reachability_cache = reachability_cache,
            .reachability_scratch = reachability_scratch,
            .reachability_queue = reachability_queue,
            .dominator_words = dominator_words,
            .postdominator_words = postdominator_words,
            .words_per_row = words_per_row,
            .immediate_postdominators = immediate_postdominators,
            .immediate_postdominator_computed = immediate_postdominator_computed,
        };
        errdefer analysis.deinit();
        try analysis.computeReachability();
        try analysis.computeDominators();
        try analysis.computeExitReachability();
        try analysis.computePostDominators();
        return analysis;
    }

    pub fn deinit(self: *Analysis) void {
        var rows = self.reachability_cache.unrestricted_reachability_rows.valueIterator();
        while (rows.next()) |row| self.allocator.free(row.*);
        self.reachability_cache.unrestricted_reachability_rows.deinit(self.allocator);
        var blocked_rows = self.reachability_cache.blocked_reachability_rows.valueIterator();
        while (blocked_rows.next()) |row| self.allocator.free(row.*);
        self.reachability_cache.blocked_reachability_rows.deinit(self.allocator);
        self.allocator.destroy(self.reachability_cache);
        self.allocator.free(self.reachability_scratch);
        self.allocator.free(self.reachability_queue);
        self.allocator.free(self.local_index);
        self.allocator.free(self.predecessor_offsets);
        self.allocator.free(self.predecessors);
        self.allocator.free(self.reachable);
        self.allocator.free(self.can_reach_exit);
        self.allocator.free(self.dominator_words);
        self.allocator.free(self.postdominator_words);
        self.allocator.free(self.immediate_postdominators);
        self.allocator.free(self.immediate_postdominator_computed);
        self.* = undefined;
    }

    pub fn blockIndex(self: *const Analysis, block_id: ir.BlockId) ?usize {
        return localBlockIndex(self.local_index, block_id);
    }

    pub fn isReachable(self: *const Analysis, block_id: ir.BlockId) bool {
        const index = self.blockIndex(block_id) orelse return false;
        return self.reachable[index];
    }

    pub fn reachableCount(self: *const Analysis) usize {
        var count: usize = 0;
        for (self.reachable) |reachable| if (reachable) {
            count += 1;
        };
        return count;
    }

    pub fn dominates(self: *const Analysis, dominator: ir.BlockId, dominated: ir.BlockId) bool {
        const dominator_index = self.blockIndex(dominator) orelse return false;
        const dominated_index = self.blockIndex(dominated) orelse return false;
        if (!self.reachable[dominator_index] or !self.reachable[dominated_index]) return false;
        return bitIsSet(self.dominatorRow(dominated_index), dominator_index);
    }

    pub fn postDominates(self: *const Analysis, postdominator: ir.BlockId, postdominated: ir.BlockId) bool {
        const postdominator_index = self.blockIndex(postdominator) orelse return false;
        const postdominated_index = self.blockIndex(postdominated) orelse return false;
        if (!self.reachable[postdominator_index] or !self.reachable[postdominated_index]) return false;
        return bitIsSet(self.postdominatorRow(postdominated_index), postdominator_index);
    }

    pub fn immediatePostDominator(self: *const Analysis, block_id: ir.BlockId) ?ir.BlockId {
        const block_index = self.blockIndex(block_id) orelse return null;
        if (!self.reachable[block_index]) return null;
        const mutable = @constCast(self);
        if (mutable.immediate_postdominator_computed[block_index]) {
            return mutable.immediate_postdominators[block_index];
        }
        const row = self.postdominatorRow(block_index);

        for (self.function.blocks, 0..) |candidate_id, candidate_index| {
            if (candidate_index == block_index or !bitIsSet(row, candidate_index)) continue;
            if (postdominatorRowContainsAllExcept(
                self.postdominatorRow(candidate_index),
                row,
                self.words_per_row,
                block_index,
                candidate_index,
            )) {
                mutable.immediate_postdominators[block_index] = candidate_id;
                mutable.immediate_postdominator_computed[block_index] = true;
                return candidate_id;
            }
        }
        mutable.immediate_postdominator_computed[block_index] = true;
        return null;
    }

    pub fn immediateConvergence(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        block_id: ir.BlockId,
        allowed: ?[]const bool,
    ) std.mem.Allocator.Error!?ir.BlockId {
        return self.immediateConvergenceWithPolicy(allocator, block_id, allowed, .terminal_only, &.{});
    }

    pub fn immediateStructuralConvergence(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        block_id: ir.BlockId,
        allowed: ?[]const bool,
    ) std.mem.Allocator.Error!?ir.BlockId {
        return self.immediateConvergenceWithPolicy(allocator, block_id, allowed, .non_fallthrough, &.{});
    }

    pub fn immediateStructuralConvergenceBefore(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        block_id: ir.BlockId,
        boundary: ir.BlockId,
        allowed: ?[]const bool,
    ) std.mem.Allocator.Error!?ir.BlockId {
        const boundaries = [_]ir.BlockId{boundary};
        return self.immediateConvergenceWithPolicy(allocator, block_id, allowed, .non_fallthrough, &boundaries);
    }

    pub fn immediateStructuralConvergenceBeforeAny(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        block_id: ir.BlockId,
        boundaries: []const ir.BlockId,
        allowed: ?[]const bool,
    ) std.mem.Allocator.Error!?ir.BlockId {
        return self.immediateConvergenceWithPolicy(allocator, block_id, allowed, .non_fallthrough, boundaries);
    }

    fn immediateConvergenceWithPolicy(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        block_id: ir.BlockId,
        allowed: ?[]const bool,
        policy: PartialConvergencePolicy,
        boundaries: []const ir.BlockId,
    ) std.mem.Allocator.Error!?ir.BlockId {
        const block_count = self.function.blocks.len;
        if (allowed) |membership| if (membership.len != block_count) return null;
        const block_index = self.blockIndex(block_id) orelse return null;
        if (!self.reachable[block_index]) return null;
        const branch = switch (self.program.blocks[block_id.index()].terminator) {
            .branch => |value| value,
            else => return null,
        };
        const then_index = self.blockIndex(branch.then_edge.target) orelse return null;
        const else_index = self.blockIndex(branch.else_edge.target) orelse return null;
        var boundary_bits: ?[]bool = null;
        defer if (boundary_bits) |bits| allocator.free(bits);
        if (boundaries.len != 0) {
            const bits = try allocator.alloc(bool, block_count);
            @memset(bits, false);
            boundary_bits = bits;
            for (boundaries) |id| bits[self.blockIndex(id) orelse return null] = true;
        }
        if (allowed) |membership| {
            if (!membership[block_index] or !membership[then_index] or !membership[else_index]) return null;
        }

        const no_distance = std.math.maxInt(u32);
        const then_distances = try allocator.alloc(u32, block_count);
        defer allocator.free(then_distances);
        const else_distances = try allocator.alloc(u32, block_count);
        defer allocator.free(else_distances);
        try self.computeForwardDistances(allocator, then_index, block_index, boundary_bits, allowed, then_distances);
        try self.computeForwardDistances(allocator, else_index, block_index, boundary_bits, allowed, else_distances);
        const rejected = try allocator.alloc(bool, block_count);
        defer allocator.free(rejected);
        @memset(rejected, false);

        while (true) {
            var best: ?usize = null;
            var best_max: u32 = no_distance;
            var best_sum: u64 = std.math.maxInt(u64);
            for (0..block_count) |candidate| {
                if (candidate == block_index or (boundary_bits != null and boundary_bits.?[candidate]) or rejected[candidate] or
                    then_distances[candidate] == no_distance or else_distances[candidate] == no_distance) continue;
                // A convergence after both branch arms cannot first occur at
                // a non-arm block with one reachable predecessor.  Preserve
                // the direct arm targets because either arm may enter the
                // other; linear suffix candidates are redundant.
                if (candidate != then_index and candidate != else_index and
                    self.predecessorCount(self.function.blocks[candidate]) < 2) continue;
                const maximum = @max(then_distances[candidate], else_distances[candidate]);
                const sum = @as(u64, then_distances[candidate]) + @as(u64, else_distances[candidate]);
                if (maximum < best_max or (maximum == best_max and sum < best_sum)) {
                    best = candidate;
                    best_max = maximum;
                    best_sum = sum;
                }
            }
            const candidate = best orelse return null;
            rejected[candidate] = true;
            if (try self.immediatePostDominatorWithinPolicy(
                allocator,
                block_id,
                self.function.blocks[candidate],
                allowed,
                policy,
                boundary_bits,
                true,
            )) |join| return join;
        }
    }

    pub fn immediateConvergenceBetween(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        first_id: ir.BlockId,
        second_id: ir.BlockId,
        allowed: ?[]const bool,
    ) std.mem.Allocator.Error!?ir.BlockId {
        return self.immediateConvergenceBetweenWithPolicy(
            allocator,
            first_id,
            second_id,
            allowed,
            .terminal_only,
        );
    }

    pub fn immediateStructuralConvergenceBetween(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        first_id: ir.BlockId,
        second_id: ir.BlockId,
        allowed: ?[]const bool,
    ) std.mem.Allocator.Error!?ir.BlockId {
        return self.immediateConvergenceBetweenWithPolicy(
            allocator,
            first_id,
            second_id,
            allowed,
            .non_fallthrough,
        );
    }

    fn immediateConvergenceBetweenWithPolicy(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        first_id: ir.BlockId,
        second_id: ir.BlockId,
        allowed: ?[]const bool,
        policy: PartialConvergencePolicy,
    ) std.mem.Allocator.Error!?ir.BlockId {
        const block_count = self.function.blocks.len;
        if (allowed) |membership| if (membership.len != block_count) return null;
        const first_index = self.blockIndex(first_id) orelse return null;
        const second_index = self.blockIndex(second_id) orelse return null;
        if (!self.reachable[first_index] or !self.reachable[second_index]) return null;
        if (allowed) |membership| {
            if (!membership[first_index] or !membership[second_index]) return null;
        }

        const no_distance = std.math.maxInt(u32);
        const first_distances = try allocator.alloc(u32, block_count);
        defer allocator.free(first_distances);
        const second_distances = try allocator.alloc(u32, block_count);
        defer allocator.free(second_distances);
        try self.computeForwardDistances(allocator, first_index, block_count, null, allowed, first_distances);
        try self.computeForwardDistances(allocator, second_index, block_count, null, allowed, second_distances);
        const rejected = try allocator.alloc(bool, block_count);
        defer allocator.free(rejected);
        @memset(rejected, false);

        while (true) {
            var best: ?usize = null;
            var best_max: u32 = no_distance;
            var best_sum: u64 = std.math.maxInt(u64);
            for (0..block_count) |candidate| {
                if (rejected[candidate] or
                    first_distances[candidate] == no_distance or second_distances[candidate] == no_distance) continue;
                // A common convergence at a non-start block with one
                // reachable predecessor already passed through that
                // predecessor.  Keep the starts themselves eligible because
                // one arm may enter the other directly; skip only the
                // redundant linear suffix candidates.
                if (candidate != first_index and candidate != second_index and
                    self.predecessorCount(self.function.blocks[candidate]) < 2) continue;
                const maximum = @max(first_distances[candidate], second_distances[candidate]);
                const sum = @as(u64, first_distances[candidate]) + @as(u64, second_distances[candidate]);
                if (maximum < best_max or (maximum == best_max and sum < best_sum)) {
                    best = candidate;
                    best_max = maximum;
                    best_sum = sum;
                }
            }
            const candidate = best orelse return null;
            rejected[candidate] = true;
            const candidate_id = self.function.blocks[candidate];
            const first_valid = first_id == candidate_id or
                try self.immediatePostDominatorWithinPolicy(allocator, first_id, candidate_id, allowed, policy, null, true) != null;
            const second_valid = second_id == candidate_id or
                try self.immediatePostDominatorWithinPolicy(allocator, second_id, candidate_id, allowed, policy, null, true) != null;
            if (first_valid and second_valid) return candidate_id;
        }
    }

    pub fn immediatePostDominatorWithin(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        block_id: ir.BlockId,
        stop_id: ir.BlockId,
        allowed: ?[]const bool,
    ) std.mem.Allocator.Error!?ir.BlockId {
        return self.immediatePostDominatorWithinPolicy(
            allocator,
            block_id,
            stop_id,
            allowed,
            .terminal_only,
            null,
            false,
        );
    }

    pub fn immediateStructuralPostDominatorWithin(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        block_id: ir.BlockId,
        stop_id: ir.BlockId,
        allowed: ?[]const bool,
    ) std.mem.Allocator.Error!?ir.BlockId {
        return self.immediatePostDominatorWithinPolicy(
            allocator,
            block_id,
            stop_id,
            allowed,
            .non_fallthrough,
            null,
            false,
        );
    }

    fn immediatePostDominatorWithinPolicy(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        block_id: ir.BlockId,
        stop_id: ir.BlockId,
        allowed: ?[]const bool,
        policy: PartialConvergencePolicy,
        boundary_bits: ?[]const bool,
        validation_only: bool,
    ) std.mem.Allocator.Error!?ir.BlockId {
        if (validation_only) {
            return self.validatePostDominatorWithin(
                allocator,
                block_id,
                stop_id,
                allowed,
                policy,
                boundary_bits,
            );
        }
        const block_count = self.function.blocks.len;
        if (allowed) |membership| if (membership.len != block_count) return null;
        const block_index = self.blockIndex(block_id) orelse return null;
        const stop_index = self.blockIndex(stop_id) orelse return null;
        if (boundary_bits) |bits| if (bits.len != block_count) return null;
        if (block_index == stop_index or !self.reachable[block_index] or !self.reachable[stop_index]) return null;
        if (allowed) |membership| {
            if (!membership[block_index] or !membership[stop_index]) return null;
        }

        const active = try allocator.alloc(bool, block_count);
        defer allocator.free(active);
        @memset(active, false);
        const stack = try allocator.alloc(u32, block_count);
        defer allocator.free(stack);
        var stack_len: usize = 1;
        stack[0] = @intCast(block_index);
        active[block_index] = true;
        while (stack_len != 0) {
            stack_len -= 1;
            const source_index = stack[stack_len];
            if (source_index == stop_index or (boundary_bits != null and boundary_bits.?[source_index])) continue;
            const source_id = self.function.blocks[source_index];
            const outgoing = successors(self.program.blocks[source_id.index()].terminator);
            for (outgoing.slice()) |target_id| {
                const target_index = self.blockIndex(target_id) orelse return null;
                if (allowed) |membership| {
                    if (!membership[target_index] and target_index != stop_index and
                        (boundary_bits == null or !boundary_bits.?[target_index]) and
                        successors(self.program.blocks[target_id.index()].terminator).len != 0) return null;
                }
                if (active[target_index]) continue;
                active[target_index] = true;
                stack[stack_len] = @intCast(target_index);
                stack_len += 1;
            }
        }
        if (!active[stop_index]) return null;

        const reaches_stop = try allocator.alloc(bool, block_count);
        defer allocator.free(reaches_stop);
        @memset(reaches_stop, false);
        reaches_stop[stop_index] = true;
        var reachability_changed = true;
        while (reachability_changed) {
            reachability_changed = false;
            for (active, 0..) |is_active, source_index| {
                if (!is_active or reaches_stop[source_index]) continue;
                const source_id = self.function.blocks[source_index];
                const outgoing = successors(self.program.blocks[source_id.index()].terminator);
                for (outgoing.slice()) |target_id| {
                    const target_index = self.blockIndex(target_id) orelse return null;
                    if (!active[target_index] or !reaches_stop[target_index]) continue;
                    reaches_stop[source_index] = true;
                    reachability_changed = true;
                    break;
                }
            }
        }
        const must_terminate = try allocator.alloc(bool, block_count);
        defer allocator.free(must_terminate);
        @memset(must_terminate, false);
        for (active, 0..) |is_active, source_index| {
            if (!is_active or reaches_stop[source_index]) continue;
            const source_id = self.function.blocks[source_index];
            if ((boundary_bits != null and boundary_bits.?[source_index]) or
                successors(self.program.blocks[source_id.index()].terminator).len == 0)
            {
                must_terminate[source_index] = true;
            }
        }
        var termination_changed = true;
        while (termination_changed) {
            termination_changed = false;
            for (active, 0..) |is_active, source_index| {
                if (!is_active or reaches_stop[source_index] or must_terminate[source_index]) continue;
                const source_id = self.function.blocks[source_index];
                const outgoing = successors(self.program.blocks[source_id.index()].terminator);
                if (outgoing.len == 0) continue;
                var all_successors_terminate = true;
                for (outgoing.slice()) |target_id| {
                    const target_index = self.blockIndex(target_id) orelse return null;
                    if (!active[target_index] or reaches_stop[target_index] or !must_terminate[target_index]) {
                        all_successors_terminate = false;
                        break;
                    }
                }
                if (all_successors_terminate) {
                    must_terminate[source_index] = true;
                    termination_changed = true;
                }
            }
        }
        var bounded_can_reach_exit: ?[]bool = null;
        defer if (bounded_can_reach_exit) |values| allocator.free(values);
        if (boundary_bits != null) {
            const values = try allocator.alloc(bool, block_count);
            @memset(values, false);
            bounded_can_reach_exit = values;
            for (active, 0..) |is_active, source_index| {
                if (!is_active or boundary_bits.?[source_index]) continue;
                const source_id = self.function.blocks[source_index];
                if (successors(self.program.blocks[source_id.index()].terminator).len == 0) values[source_index] = true;
            }
            var exit_changed = true;
            while (exit_changed) {
                exit_changed = false;
                for (active, 0..) |is_active, source_index| {
                    if (!is_active or boundary_bits.?[source_index] or values[source_index]) continue;
                    const source_id = self.function.blocks[source_index];
                    const outgoing = successors(self.program.blocks[source_id.index()].terminator);
                    for (outgoing.slice()) |target_id| {
                        const target_index = self.blockIndex(target_id) orelse return null;
                        if (!active[target_index] or boundary_bits.?[target_index] or !values[target_index]) continue;
                        values[source_index] = true;
                        exit_changed = true;
                        break;
                    }
                }
            }
        }
        for (active, reaches_stop, must_terminate, self.can_reach_exit, 0..) |is_active, can_reach, terminates, can_exit, index| {
            if (!is_active or can_reach or terminates) continue;
            const reaches_unstructured_exit = if (bounded_can_reach_exit) |values| values[index] else can_exit;
            if (policy == .terminal_only or reaches_unstructured_exit) return null;
        }

        // Convergence search only needs to know whether the bounded partial
        // postdominator relation exists.  The matrix below is required to
        // recover the actual nearest ID for the public within-boundary API,
        // but is redundant for the boolean callers and dominates large CFG
        // cost when many candidates are rejected.
        if (validation_only) return stop_id;

        const word_bits = @bitSizeOf(usize);
        const words_per_row = (block_count + word_bits - 1) / word_bits;
        const word_count = std.math.mul(usize, block_count, words_per_row) catch return null;
        const rows = try allocator.alloc(usize, word_count);
        defer allocator.free(rows);
        @memset(rows, 0);
        const continuing_mask = try allocator.alloc(usize, words_per_row);
        defer allocator.free(continuing_mask);
        @memset(continuing_mask, 0);
        for (reaches_stop, 0..) |can_reach, index| if (can_reach) setBit(continuing_mask, index);
        for (reaches_stop, 0..) |can_reach, index| {
            if (!can_reach) continue;
            const row = rows[index * words_per_row ..][0..words_per_row];
            if (index == stop_index) {
                setBit(row, index);
            } else {
                @memcpy(row, continuing_mask);
            }
        }

        const scratch = try allocator.alloc(usize, words_per_row);
        defer allocator.free(scratch);
        var changed = true;
        while (changed) {
            changed = false;
            for (reaches_stop, 0..) |can_reach, source_index| {
                if (!can_reach or source_index == stop_index) continue;
                const source_id = self.function.blocks[source_index];
                const outgoing = successors(self.program.blocks[source_id.index()].terminator);
                var found_successor = false;
                for (outgoing.slice()) |target_id| {
                    const target_index = self.blockIndex(target_id) orelse return null;
                    if (!active[target_index]) return null;
                    if (!reaches_stop[target_index]) continue;
                    const target_row = rows[target_index * words_per_row ..][0..words_per_row];
                    if (!found_successor) {
                        @memcpy(scratch, target_row);
                        found_successor = true;
                    } else {
                        for (scratch, target_row) |*word, target_word| word.* &= target_word;
                    }
                }
                if (!found_successor) return null;
                setBit(scratch, source_index);
                const source_row = rows[source_index * words_per_row ..][0..words_per_row];
                if (!std.mem.eql(usize, source_row, scratch)) {
                    @memcpy(source_row, scratch);
                    changed = true;
                }
            }
        }

        const block_row = rows[block_index * words_per_row ..][0..words_per_row];
        for (reaches_stop, 0..) |can_reach, candidate_index| {
            if (!can_reach or candidate_index == block_index or !bitIsSet(block_row, candidate_index)) continue;
            const candidate_row = rows[candidate_index * words_per_row ..][0..words_per_row];
            if (postdominatorRowContainsAllExcept(
                candidate_row,
                block_row,
                words_per_row,
                block_index,
                candidate_index,
            )) return self.function.blocks[candidate_index];
        }
        return null;
    }

    fn validatePostDominatorWithin(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        block_id: ir.BlockId,
        stop_id: ir.BlockId,
        allowed: ?[]const bool,
        policy: PartialConvergencePolicy,
        boundary_bits: ?[]const bool,
    ) std.mem.Allocator.Error!?ir.BlockId {
        const block_count = self.function.blocks.len;
        if (allowed) |membership| if (membership.len != block_count) return null;
        const block_index = self.blockIndex(block_id) orelse return null;
        const stop_index = self.blockIndex(stop_id) orelse return null;
        if (boundary_bits) |bits| if (bits.len != block_count) return null;
        if (block_index == stop_index or !self.reachable[block_index] or !self.reachable[stop_index]) return null;
        if (allowed) |membership| {
            if (!membership[block_index] or !membership[stop_index]) return null;
        }

        // Build the same bounded active region as the exact implementation,
        // but use one queue rather than rescanning the whole graph for every
        // fixed-point change.
        const active = try allocator.alloc(bool, block_count);
        defer allocator.free(active);
        @memset(active, false);
        const queue = try allocator.alloc(u32, block_count);
        defer allocator.free(queue);
        var queue_len: usize = 1;
        queue[0] = @intCast(block_index);
        active[block_index] = true;
        while (queue_len != 0) {
            queue_len -= 1;
            const source_index = queue[queue_len];
            if (source_index == stop_index or (boundary_bits != null and boundary_bits.?[source_index])) continue;
            const source_id = self.function.blocks[source_index];
            const outgoing = successors(self.program.blocks[source_id.index()].terminator);
            for (outgoing.slice()) |target_id| {
                const target_index = self.blockIndex(target_id) orelse return null;
                if (allowed) |membership| {
                    if (!membership[target_index] and target_index != stop_index and
                        (boundary_bits == null or !boundary_bits.?[target_index]) and
                        successors(self.program.blocks[target_id.index()].terminator).len != 0) return null;
                }
                if (active[target_index]) continue;
                active[target_index] = true;
                queue[queue_len] = @intCast(target_index);
                queue_len += 1;
            }
        }
        if (!active[stop_index]) return null;

        // A node reaches the stop exactly when it is in the reverse closure
        // of the stop inside the active region.  The forward fixed point in
        // the exact path computes this same predicate.
        const reaches_stop = try allocator.alloc(bool, block_count);
        defer allocator.free(reaches_stop);
        @memset(reaches_stop, false);
        queue_len = 1;
        queue[0] = @intCast(stop_index);
        reaches_stop[stop_index] = true;
        while (queue_len != 0) {
            queue_len -= 1;
            const target_index = queue[queue_len];
            const start = self.predecessor_offsets[target_index];
            const end = self.predecessor_offsets[target_index + 1];
            for (self.predecessors[start..end]) |source_u32| {
                const source_index: usize = @intCast(source_u32);
                if (!active[source_index] or reaches_stop[source_index]) continue;
                reaches_stop[source_index] = true;
                queue[queue_len] = @intCast(source_index);
                queue_len += 1;
            }
        }

        // Compute the all-successors terminal closure with predecessor
        // counts. Nodes that reach the stop are excluded, just as in the
        // exact implementation; boundary nodes count as terminating.
        const must_terminate = try allocator.alloc(bool, block_count);
        defer allocator.free(must_terminate);
        @memset(must_terminate, false);
        const remaining = try allocator.alloc(usize, block_count);
        defer allocator.free(remaining);
        @memset(remaining, 0);
        queue_len = 0;
        for (active, reaches_stop, 0..) |is_active, reaches, source_index| {
            if (!is_active or reaches) continue;
            const source_id = self.function.blocks[source_index];
            const outgoing = successors(self.program.blocks[source_id.index()].terminator);
            if ((boundary_bits != null and boundary_bits.?[source_index]) or outgoing.len == 0) {
                must_terminate[source_index] = true;
                queue[queue_len] = @intCast(source_index);
                queue_len += 1;
            }
        }
        // The initial terminal seeds were already excluded from each
        // predecessor's unresolved successor count.  Only nodes newly proven
        // by that count may decrement their predecessors below.
        queue_len = 0;
        for (active, reaches_stop, must_terminate, 0..) |is_active, reaches, terminates, source_index| {
            if (!is_active or reaches or terminates) continue;
            const source_id = self.function.blocks[source_index];
            const outgoing = successors(self.program.blocks[source_id.index()].terminator);
            var unresolved_targets: [2]usize = undefined;
            var unresolved_len: usize = 0;
            for (outgoing.slice()) |target_id| {
                const target_index = self.blockIndex(target_id) orelse return null;
                if (!active[target_index] or !must_terminate[target_index]) {
                    var already_counted = false;
                    for (unresolved_targets[0..unresolved_len]) |prior_target_index| {
                        if (prior_target_index == target_index) {
                            already_counted = true;
                            break;
                        }
                    }
                    if (!already_counted) {
                        unresolved_targets[unresolved_len] = target_index;
                        unresolved_len += 1;
                    }
                }
            }
            remaining[source_index] = unresolved_len;
            if (remaining[source_index] == 0) {
                must_terminate[source_index] = true;
                queue[queue_len] = @intCast(source_index);
                queue_len += 1;
            }
        }
        while (queue_len != 0) {
            queue_len -= 1;
            const target_index = queue[queue_len];
            const start = self.predecessor_offsets[target_index];
            const end = self.predecessor_offsets[target_index + 1];
            var previous_source: ?usize = null;
            for (self.predecessors[start..end]) |source_u32| {
                const source_index: usize = @intCast(source_u32);
                if (previous_source == source_index) continue;
                previous_source = source_index;
                if (!active[source_index] or reaches_stop[source_index] or must_terminate[source_index]) continue;
                if (remaining[source_index] == 0) continue;
                remaining[source_index] -= 1;
                if (remaining[source_index] == 0) {
                    must_terminate[source_index] = true;
                    queue[queue_len] = @intCast(source_index);
                    queue_len += 1;
                }
            }
        }

        var bounded_can_reach_exit: ?[]bool = null;
        defer if (bounded_can_reach_exit) |values| allocator.free(values);
        if (boundary_bits != null) {
            const values = try allocator.alloc(bool, block_count);
            @memset(values, false);
            bounded_can_reach_exit = values;
            queue_len = 0;
            for (active, 0..) |is_active, source_index| {
                if (!is_active or boundary_bits.?[source_index]) continue;
                const source_id = self.function.blocks[source_index];
                if (successors(self.program.blocks[source_id.index()].terminator).len == 0) {
                    values[source_index] = true;
                    queue[queue_len] = @intCast(source_index);
                    queue_len += 1;
                }
            }
            while (queue_len != 0) {
                queue_len -= 1;
                const target_index = queue[queue_len];
                const start = self.predecessor_offsets[target_index];
                const end = self.predecessor_offsets[target_index + 1];
                for (self.predecessors[start..end]) |source_u32| {
                    const source_index: usize = @intCast(source_u32);
                    if (!active[source_index] or boundary_bits.?[source_index] or values[source_index]) continue;
                    values[source_index] = true;
                    queue[queue_len] = @intCast(source_index);
                    queue_len += 1;
                }
            }
        }

        for (active, reaches_stop, must_terminate, self.can_reach_exit, 0..) |is_active, reaches, terminates, can_exit, index| {
            if (!is_active or reaches or terminates) continue;
            const reaches_unstructured_exit = if (bounded_can_reach_exit) |values| values[index] else can_exit;
            if (policy == .terminal_only or reaches_unstructured_exit) return null;
        }
        return stop_id;
    }

    pub fn predecessorCount(self: *const Analysis, block_id: ir.BlockId) usize {
        const index = self.blockIndex(block_id) orelse return 0;
        if (!self.reachable[index]) return 0;
        const start = self.predecessor_offsets[index];
        const end = self.predecessor_offsets[index + 1];
        var count: usize = 0;
        for (self.predecessors[start..end]) |source_index| {
            if (self.reachable[source_index]) count += 1;
        }
        return count;
    }

    pub fn predecessorAt(self: *const Analysis, block_id: ir.BlockId, predecessor_index: usize) ?ir.BlockId {
        const index = self.blockIndex(block_id) orelse return null;
        if (!self.reachable[index]) return null;
        const start = self.predecessor_offsets[index];
        const end = self.predecessor_offsets[index + 1];
        var reachable_index: usize = 0;
        for (self.predecessors[start..end]) |source_index| {
            if (!self.reachable[source_index]) continue;
            if (reachable_index == predecessor_index) return self.function.blocks[source_index];
            reachable_index += 1;
        }
        return null;
    }

    pub fn successorCount(self: *const Analysis, block_id: ir.BlockId) usize {
        if (!self.isReachable(block_id)) return 0;
        return successors(self.program.blocks[block_id.index()].terminator).len;
    }

    pub fn successorAt(self: *const Analysis, block_id: ir.BlockId, successor_index: usize) ?ir.BlockId {
        if (!self.isReachable(block_id)) return null;
        const outgoing = successors(self.program.blocks[block_id.index()].terminator);
        if (successor_index >= outgoing.len) return null;
        return outgoing.ids[successor_index];
    }

    pub fn canReach(self: *const Analysis, start: ir.BlockId, target: ir.BlockId) std.mem.Allocator.Error!bool {
        const start_index = self.blockIndex(start) orelse return false;
        const target_index = self.blockIndex(target) orelse return false;
        if (!self.reachable[start_index] or !self.reachable[target_index]) return false;

        return self.canReachLocal(start_index, target_index, self.function.blocks.len);
    }

    /// Test reachability through at least one CFG edge.  Unlike canReach,
    /// this distinguishes a genuine cycle from the zero-length path used
    /// when start and target are identical.
    pub fn canReachNonEmptyPath(
        self: *const Analysis,
        start: ir.BlockId,
        target: ir.BlockId,
    ) std.mem.Allocator.Error!bool {
        if (!self.isReachable(start) or !self.isReachable(target)) return false;
        const successor_count = self.successorCount(start);
        for (0..successor_count) |successor_index| {
            const successor = self.successorAt(start, successor_index) orelse return false;
            if (successor == target or try self.canReach(successor, target)) return true;
        }
        return false;
    }

    pub fn canReachAvoiding(
        self: *const Analysis,
        start: ir.BlockId,
        target: ir.BlockId,
        blocked: ir.BlockId,
    ) std.mem.Allocator.Error!bool {
        const start_index = self.blockIndex(start) orelse return false;
        const target_index = self.blockIndex(target) orelse return false;
        const blocked_index = self.blockIndex(blocked) orelse return false;
        if (!self.reachable[start_index] or !self.reachable[target_index] or
            start_index == blocked_index or target_index == blocked_index) return false;

        return self.canReachLocal(start_index, target_index, blocked_index);
    }

    pub fn allPathsReachTargetOrBoundariesAlloc(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        start: ir.BlockId,
        target: ir.BlockId,
        boundaries: []const ir.BlockId,
        allowed: ?[]const bool,
    ) std.mem.Allocator.Error!bool {
        const block_count = self.function.blocks.len;
        if (allowed) |membership| if (membership.len != block_count) return false;
        const start_index = self.blockIndex(start) orelse return false;
        const target_index = self.blockIndex(target) orelse return false;
        if (!self.reachable[start_index] or !self.reachable[target_index]) return false;
        if (allowed) |membership| {
            if (!membership[start_index] or !membership[target_index]) return false;
        }
        if (!try self.canReach(start, target)) return false;

        const boundary_bits = try allocator.alloc(bool, block_count);
        defer allocator.free(boundary_bits);
        @memset(boundary_bits, false);
        for (boundaries) |boundary| {
            const index = self.blockIndex(boundary) orelse return false;
            boundary_bits[index] = true;
        }

        const active = try allocator.alloc(bool, block_count);
        defer allocator.free(active);
        @memset(active, false);
        const pending = try allocator.alloc(u32, block_count);
        defer allocator.free(pending);
        active[start_index] = true;
        pending[0] = @intCast(start_index);
        var read_index: usize = 0;
        var write_index: usize = 1;
        while (read_index < write_index) : (read_index += 1) {
            const source_index = pending[read_index];
            if (source_index == target_index or boundary_bits[source_index]) continue;
            const source = self.function.blocks[source_index];
            const outgoing = successors(self.program.blocks[source.index()].terminator);
            for (outgoing.slice()) |successor| {
                const successor_index = self.blockIndex(successor) orelse return false;
                if (allowed) |membership| {
                    if (!membership[successor_index] and successor_index != target_index and !boundary_bits[successor_index]) {
                        return false;
                    }
                }
                if (!self.reachable[successor_index] or active[successor_index]) continue;
                active[successor_index] = true;
                pending[write_index] = @intCast(successor_index);
                write_index += 1;
            }
        }
        if (!active[target_index]) return false;

        const accepted = try allocator.alloc(bool, block_count);
        defer allocator.free(accepted);
        @memset(accepted, false);
        for (active, 0..) |is_active, index| {
            if (!is_active) continue;
            const block = self.function.blocks[index];
            accepted[index] = index == target_index or boundary_bits[index] or
                successors(self.program.blocks[block.index()].terminator).len == 0;
        }
        var changed = true;
        while (changed) {
            changed = false;
            for (active, 0..) |is_active, source_index| {
                if (!is_active or accepted[source_index]) continue;
                const source = self.function.blocks[source_index];
                const outgoing = successors(self.program.blocks[source.index()].terminator);
                if (outgoing.len == 0) continue;
                var all_accepted = true;
                for (outgoing.slice()) |successor| {
                    const successor_index = self.blockIndex(successor) orelse return false;
                    if (!active[successor_index] or !accepted[successor_index]) {
                        all_accepted = false;
                        break;
                    }
                }
                if (all_accepted) {
                    accepted[source_index] = true;
                    changed = true;
                }
            }
        }
        return accepted[start_index];
    }

    fn canReachLocal(self: *const Analysis, start: usize, target: usize, blocked: usize) std.mem.Allocator.Error!bool {
        const unrestricted = blocked == self.function.blocks.len;
        if (unrestricted) {
            if (self.reachability_cache.unrestricted_reachability_rows.get(start)) |row| return row[target];
        } else {
            const key = BlockedReachabilityKey{ .start = start, .blocked = blocked };
            if (self.reachability_cache.blocked_reachability_rows.get(key)) |row| {
                return bitIsSet(row, target);
            }
        }

        const row = if (unrestricted) blk: {
            const allocated = try self.allocator.alloc(bool, self.function.blocks.len);
            errdefer self.allocator.free(allocated);
            break :blk allocated;
        } else self.reachability_scratch;
        if (!unrestricted) @memset(row, false);
        errdefer if (unrestricted) self.allocator.free(row);
        @memset(row, false);
        if (start == blocked) {
            if (unrestricted) try self.reachability_cache.unrestricted_reachability_rows.put(self.allocator, start, row);
            return false;
        }

        const queue = self.reachability_queue;
        row[start] = true;
        queue[0] = @intCast(start);
        var read_index: usize = 0;
        var write_index: usize = 1;
        while (read_index < write_index) : (read_index += 1) {
            const source_index = queue[read_index];
            const source_id = self.function.blocks[source_index];
            const outgoing = successors(self.program.blocks[source_id.index()].terminator);
            for (outgoing.slice()) |target_id| {
                const target_index = self.blockIndex(target_id) orelse continue;
                if (target_index == blocked or !self.reachable[target_index] or row[target_index]) continue;
                row[target_index] = true;
                queue[write_index] = @intCast(target_index);
                write_index += 1;
            }
        }

        if (unrestricted) {
            try self.reachability_cache.unrestricted_reachability_rows.put(self.allocator, start, row);
        } else if (self.reachability_cache.blocked_reachability_rows.count() < blocked_reachability_cache_limit) {
            if (self.allocator.alloc(usize, self.words_per_row) catch null) |cached_row| {
                @memset(cached_row, 0);
                for (row, 0..) |reaches, index| if (reaches) setBit(cached_row, index);
                const key = BlockedReachabilityKey{ .start = start, .blocked = blocked };
                self.reachability_cache.blocked_reachability_rows.put(self.allocator, key, cached_row) catch {
                    self.allocator.free(cached_row);
                };
            }
        }
        return row[target];
    }

    fn computeForwardDistances(
        self: *const Analysis,
        allocator: std.mem.Allocator,
        start: usize,
        blocked: usize,
        stop_expansion: ?[]const bool,
        allowed: ?[]const bool,
        distances: []u32,
    ) std.mem.Allocator.Error!void {
        const no_distance = std.math.maxInt(u32);
        if (stop_expansion) |bits| if (bits.len != self.function.blocks.len) return;
        @memset(distances, no_distance);
        const queue = try allocator.alloc(u32, self.function.blocks.len);
        defer allocator.free(queue);
        distances[start] = 0;
        var read_index: usize = 0;
        var write_index: usize = 1;
        queue[0] = @intCast(start);
        while (read_index < write_index) : (read_index += 1) {
            const source_index = queue[read_index];
            if (stop_expansion != null and stop_expansion.?[source_index]) continue;
            const source_id = self.function.blocks[source_index];
            const outgoing = successors(self.program.blocks[source_id.index()].terminator);
            for (outgoing.slice()) |target_id| {
                const target_index = self.blockIndex(target_id) orelse continue;
                if (target_index == blocked) continue;
                if (allowed) |membership| {
                    if (!membership[target_index] and (stop_expansion == null or !stop_expansion.?[target_index])) continue;
                }
                if (!self.reachable[target_index] or distances[target_index] != no_distance) continue;
                distances[target_index] = distances[source_index] + 1;
                queue[write_index] = @intCast(target_index);
                write_index += 1;
            }
        }
    }

    fn computeReachability(self: *Analysis) !void {
        const stack = try self.allocator.alloc(u32, self.function.blocks.len);
        defer self.allocator.free(stack);

        const entry_local = self.blockIndex(self.function.entry_block).?;
        var stack_len: usize = 1;
        stack[0] = @intCast(entry_local);
        self.reachable[entry_local] = true;

        while (stack_len != 0) {
            stack_len -= 1;
            const source_local = stack[stack_len];
            const block_id = self.function.blocks[source_local];
            const outgoing = successors(self.program.blocks[block_id.index()].terminator);
            for (outgoing.slice()) |target| {
                const target_local = self.blockIndex(target).?;
                if (self.reachable[target_local]) continue;
                self.reachable[target_local] = true;
                stack[stack_len] = @intCast(target_local);
                stack_len += 1;
            }
        }
    }

    fn computeDominators(self: *Analysis) !void {
        const reachable_mask = try self.allocator.alloc(usize, self.words_per_row);
        defer self.allocator.free(reachable_mask);
        @memset(reachable_mask, 0);
        for (self.reachable, 0..) |is_reachable, index| if (is_reachable) setBit(reachable_mask, index);

        const entry_local = self.blockIndex(self.function.entry_block).?;
        for (self.reachable, 0..) |is_reachable, index| {
            if (!is_reachable) continue;
            const row = self.dominatorRow(index);
            if (index == entry_local) {
                setBit(row, index);
            } else {
                @memcpy(row, reachable_mask);
            }
        }

        const scratch = try self.allocator.alloc(usize, self.words_per_row);
        defer self.allocator.free(scratch);
        var changed = true;
        while (changed) {
            changed = false;
            for (self.reachable, 0..) |is_reachable, target_local| {
                if (!is_reachable or target_local == entry_local) continue;
                var found_predecessor = false;
                const start = self.predecessor_offsets[target_local];
                const end = self.predecessor_offsets[target_local + 1];
                for (self.predecessors[start..end]) |source_local| {
                    if (!self.reachable[source_local]) continue;
                    const source_row = self.dominatorRow(source_local);
                    if (!found_predecessor) {
                        @memcpy(scratch, source_row);
                        found_predecessor = true;
                    } else {
                        for (scratch, source_row) |*word, source_word| word.* &= source_word;
                    }
                }
                if (!found_predecessor) return error.InvalidCfg;
                setBit(scratch, target_local);

                const target_row = self.dominatorRow(target_local);
                if (!std.mem.eql(usize, target_row, scratch)) {
                    @memcpy(target_row, scratch);
                    changed = true;
                }
            }
        }
    }

    fn computeExitReachability(self: *Analysis) !void {
        const stack = try self.allocator.alloc(u32, self.function.blocks.len);
        defer self.allocator.free(stack);
        var stack_len: usize = 0;

        for (self.function.blocks, 0..) |block_id, local_index| {
            if (!self.reachable[local_index]) continue;
            if (successors(self.program.blocks[block_id.index()].terminator).len != 0) continue;
            self.can_reach_exit[local_index] = true;
            stack[stack_len] = @intCast(local_index);
            stack_len += 1;
        }

        while (stack_len != 0) {
            stack_len -= 1;
            const target_local = stack[stack_len];
            const start = self.predecessor_offsets[target_local];
            const end = self.predecessor_offsets[target_local + 1];
            for (self.predecessors[start..end]) |source_local| {
                if (!self.reachable[source_local] or self.can_reach_exit[source_local]) continue;
                self.can_reach_exit[source_local] = true;
                stack[stack_len] = source_local;
                stack_len += 1;
            }
        }
    }

    fn computePostDominators(self: *Analysis) !void {
        const exit_reachable_mask = try self.allocator.alloc(usize, self.words_per_row);
        defer self.allocator.free(exit_reachable_mask);
        @memset(exit_reachable_mask, 0);
        for (self.can_reach_exit, 0..) |can_reach, index| if (can_reach) setBit(exit_reachable_mask, index);

        for (self.reachable, 0..) |is_reachable, index| {
            if (!is_reachable) continue;
            const row = self.postdominatorRow(index);
            const block = self.program.blocks[self.function.blocks[index].index()];
            if (!self.can_reach_exit[index] or successors(block.terminator).len == 0) {
                setBit(row, index);
            } else {
                @memcpy(row, exit_reachable_mask);
            }
        }

        const scratch = try self.allocator.alloc(usize, self.words_per_row);
        defer self.allocator.free(scratch);
        var changed = true;
        while (changed) {
            changed = false;
            for (self.reachable, 0..) |is_reachable, source_local| {
                if (!is_reachable or !self.can_reach_exit[source_local]) continue;
                const block = self.program.blocks[self.function.blocks[source_local].index()];
                const outgoing = successors(block.terminator);
                if (outgoing.len == 0) continue;

                var found_successor = false;
                for (outgoing.slice()) |target_id| {
                    const target_local = self.blockIndex(target_id).?;
                    const target_row = self.postdominatorRow(target_local);
                    if (!found_successor) {
                        @memcpy(scratch, target_row);
                        found_successor = true;
                    } else {
                        for (scratch, target_row) |*word, target_word| word.* &= target_word;
                    }
                }
                if (!found_successor) return error.InvalidCfg;
                setBit(scratch, source_local);

                const source_row = self.postdominatorRow(source_local);
                if (!std.mem.eql(usize, source_row, scratch)) {
                    @memcpy(source_row, scratch);
                    changed = true;
                }
            }
        }
    }

    fn dominatorRow(self: *const Analysis, local_block: usize) []usize {
        const start = local_block * self.words_per_row;
        return self.dominator_words[start .. start + self.words_per_row];
    }

    fn postdominatorRow(self: *const Analysis, local_block: usize) []usize {
        const start = local_block * self.words_per_row;
        return self.postdominator_words[start .. start + self.words_per_row];
    }
};

const Successors = struct {
    ids: [2]ir.BlockId = undefined,
    len: u2 = 0,

    fn slice(self: *const Successors) []const ir.BlockId {
        return self.ids[0..self.len];
    }
};

fn successors(terminator: ir.Terminator) Successors {
    var result: Successors = .{};
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

fn localBlockIndex(local_index: []const ?u32, block_id: ir.BlockId) ?usize {
    if (block_id.index() >= local_index.len) return null;
    const index = local_index[block_id.index()] orelse return null;
    return @intCast(index);
}

fn setBit(words: []usize, index: usize) void {
    const word_bits = @bitSizeOf(usize);
    words[index / word_bits] |= @as(usize, 1) << @intCast(index % word_bits);
}

fn bitIsSet(words: []const usize, index: usize) bool {
    const word_bits = @bitSizeOf(usize);
    return (words[index / word_bits] & (@as(usize, 1) << @intCast(index % word_bits))) != 0;
}

fn postdominatorRowContainsAllExcept(
    candidate_row: []const usize,
    source_row: []const usize,
    words_per_row: usize,
    first_excluded: usize,
    second_excluded: usize,
) bool {
    const word_bits = @bitSizeOf(usize);
    for (candidate_row[0..words_per_row], source_row[0..words_per_row], 0..) |candidate_word, source_word, word_index| {
        var required = source_word;
        if (word_index == first_excluded / word_bits) {
            required &= ~(@as(usize, 1) << @intCast(first_excluded % word_bits));
        }
        if (word_index == second_excluded / word_bits) {
            required &= ~(@as(usize, 1) << @intCast(second_excluded % word_bits));
        }
        if ((required & ~candidate_word) != 0) return false;
    }
    return true;
}

test "diamond reachability and dominance use function-local block identity" {
    const fixtures = @import("fixtures.zig");
    const program = &fixtures.absolute_value_module.program;
    const function = fixtures.absolute_value_module.functions[1];
    var analysis = try Analysis.init(std.testing.allocator, program, function);
    defer analysis.deinit();

    try std.testing.expect(analysis.isReachable(fixtures.absolute_value_module.b_entry));
    try std.testing.expect(analysis.isReachable(fixtures.absolute_value_module.b_join));
    try std.testing.expect(analysis.dominates(fixtures.absolute_value_module.b_entry, fixtures.absolute_value_module.b_join));
    try std.testing.expect(!analysis.dominates(fixtures.absolute_value_module.b_negative, fixtures.absolute_value_module.b_join));
    try std.testing.expectEqual(@as(usize, 2), analysis.predecessorCount(fixtures.absolute_value_module.b_join));
    try std.testing.expectEqual(fixtures.absolute_value_module.b_negative, analysis.predecessorAt(fixtures.absolute_value_module.b_join, 0).?);
    try std.testing.expectEqual(fixtures.absolute_value_module.b_nonnegative, analysis.predecessorAt(fixtures.absolute_value_module.b_join, 1).?);
    try std.testing.expect(analysis.predecessorAt(fixtures.absolute_value_module.b_join, 2) == null);
    try std.testing.expect(analysis.postDominates(fixtures.absolute_value_module.b_join, fixtures.absolute_value_module.b_entry));
    try std.testing.expectEqual(fixtures.absolute_value_module.b_join, analysis.immediatePostDominator(fixtures.absolute_value_module.b_entry).?);
    try std.testing.expectEqual(fixtures.absolute_value_module.b_join, analysis.immediatePostDominator(fixtures.absolute_value_module.b_entry).?);
    try std.testing.expect(analysis.immediate_postdominator_computed[
        analysis.blockIndex(fixtures.absolute_value_module.b_entry).?
    ]);
}
