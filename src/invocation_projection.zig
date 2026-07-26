const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const projection_witness = @import("invocation_projection_witness.zig");

pub const Consumer = union(enum) {
    instruction: ir.InstructionId,
    terminator: ir.BlockId,
};

pub const Reentry = enum {
    none,
    direct_backedge,
    indirect_region,
};

pub const ReentryEdge = struct {
    source: ir.BlockId,
    target: ir.BlockId,
};

pub const Projection = struct {
    producer: ir.InstructionId,
    consumer: Consumer,
    pack: ir.ValuePackId,
    cfg_fingerprint: projection_witness.CfgFingerprint,
    reentry: Reentry,
    blocks: []const ir.BlockId,
    gaps: []const ir.InstructionId,
    moved_edges: []const ReentryEdge,
    reentry_blocks: []const ir.BlockId,
    reentry_edges: []const ReentryEdge,
    exit_edges: []const ReentryEdge,

    pub fn deinit(self: Projection, allocator: std.mem.Allocator) void {
        allocator.free(self.blocks);
        allocator.free(self.gaps);
        allocator.free(self.moved_edges);
        allocator.free(self.reentry_blocks);
        allocator.free(self.reentry_edges);
        allocator.free(self.exit_edges);
    }
};

const ReentryProof = struct {
    kind: Reentry,
    blocks: []const ir.BlockId,
    edges: []const ReentryEdge,
    exit_edges: []const ReentryEdge,

    fn deinit(self: ReentryProof, allocator: std.mem.Allocator) void {
        allocator.free(self.blocks);
        allocator.free(self.edges);
        allocator.free(self.exit_edges);
    }
};

pub fn instructionAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    producer: ir.Instruction,
    consumer: ir.Instruction,
) !?Projection {
    if (!validId(consumer.block, program.blocks.len)) return null;
    const consumer_block = program.blocks[consumer.block.index()];
    const consumer_position = instructionPosition(consumer_block, consumer.id) orelse return null;
    return planAlloc(
        allocator,
        program,
        producer,
        .{ .instruction = consumer.id },
        consumer.block,
        consumer_position,
    );
}

pub fn terminatorAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    producer: ir.Instruction,
    consumer_block: ir.BlockId,
) !?Projection {
    if (!validId(consumer_block, program.blocks.len)) return null;
    return planAlloc(
        allocator,
        program,
        producer,
        .{ .terminator = consumer_block },
        consumer_block,
        program.blocks[consumer_block.index()].instructions.len,
    );
}

fn planAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    producer: ir.Instruction,
    consumer: Consumer,
    consumer_block_id: ir.BlockId,
    consumer_position: usize,
) !?Projection {
    if (!validId(producer.block, program.blocks.len) or !validId(consumer_block_id, program.blocks.len)) return null;
    const producer_block = program.blocks[producer.block.index()];
    const consumer_block = program.blocks[consumer_block_id.index()];
    if (producer_block.function != consumer_block.function) return null;
    const producer_position = instructionPosition(producer_block, producer.id) orelse return null;
    const pack_id = producer.pack_result orelse return null;
    if (!validId(pack_id, program.value_packs.len)) return null;
    const cfg_fingerprint = projection_witness.cfgFingerprint(program, producer_block.function) orelse return null;

    if (producer.block == consumer_block_id) {
        if (consumer_position <= producer_position) return null;
        const gaps = producer_block.instructions[producer_position + 1 .. consumer_position];
        if (!gapSliceIsMovable(program, gaps, producer.block)) return null;
        return @as(?Projection, try allocProjection(
            allocator,
            producer.id,
            consumer,
            pack_id,
            cfg_fingerprint,
            .none,
            &.{producer.block},
            gaps,
            &.{},
            &.{},
            &.{},
            &.{},
            &.{},
        ));
    }

    return regionAlloc(
        allocator,
        program,
        producer,
        producer_position,
        consumer,
        consumer_block_id,
        consumer_position,
        pack_id,
        cfg_fingerprint,
    );
}

fn regionAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    producer: ir.Instruction,
    producer_position: usize,
    consumer: Consumer,
    consumer_block_id: ir.BlockId,
    consumer_position: usize,
    pack_id: ir.ValuePackId,
    cfg_fingerprint: projection_witness.CfgFingerprint,
) std.mem.Allocator.Error!?Projection {
    const producer_block = program.blocks[producer.block.index()];
    if (!validId(producer_block.function, program.functions.len)) return null;
    const function = program.functions[producer_block.function.index()];
    var analysis = cfg.Analysis.init(allocator, program, program.functions[producer_block.function.index()]) catch |err| switch (err) {
        error.InvalidCfg => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    if (!analysis.isReachable(producer.block) or
        !analysis.isReachable(consumer_block_id) or
        !analysis.dominates(producer.block, consumer_block_id) or
        !analysis.postDominates(consumer_block_id, producer.block)) return null;
    const included = try allocator.alloc(bool, program.blocks.len);
    defer allocator.free(included);
    @memset(included, false);
    var pending: std.ArrayList(ir.BlockId) = .empty;
    defer pending.deinit(allocator);
    included[producer.block.index()] = true;
    try pending.append(allocator, producer.block);
    var cursor: usize = 0;
    while (cursor < pending.items.len) : (cursor += 1) {
        const block_id = pending.items[cursor];
        if (block_id == consumer_block_id) continue;
        const successor_count = analysis.successorCount(block_id);
        if (successor_count == 0) return null;
        for (0..successor_count) |successor_index| {
            const successor = analysis.successorAt(block_id, successor_index) orelse return null;
            if (!validId(successor, program.blocks.len) or
                program.blocks[successor.index()].function != function.id or
                !analysis.isReachable(successor)) return null;
            if (included[successor.index()]) continue;
            included[successor.index()] = true;
            try pending.append(allocator, successor);
        }
    }
    if (!included[consumer_block_id.index()]) return null;

    const reentry = (try reentryAlloc(
        allocator,
        &analysis,
        included,
        consumer_block_id,
        producer.block,
    )) orelse return null;
    var keep_reentry = false;
    defer if (!keep_reentry) reentry.deinit(allocator);

    var included_count: usize = 0;
    for (function.blocks) |block_id| {
        if (!included[block_id.index()]) continue;
        included_count += 1;
        if (!analysis.dominates(producer.block, block_id) or
            !analysis.postDominates(consumer_block_id, block_id)) return null;
        const predecessor_count = analysis.predecessorCount(block_id);
        for (0..predecessor_count) |predecessor_index| {
            const predecessor = analysis.predecessorAt(block_id, predecessor_index) orelse return null;
            if (block_id == producer.block) {
                if (included[predecessor.index()] and
                    !(reentry.kind != .none and predecessor == consumer_block_id)) return null;
            } else if (!included[predecessor.index()] or predecessor == consumer_block_id) {
                return null;
            }
        }
    }

    const indegree = try allocator.alloc(usize, program.blocks.len);
    defer allocator.free(indegree);
    @memset(indegree, 0);
    for (function.blocks) |block_id| {
        if (!included[block_id.index()] or block_id == consumer_block_id) continue;
        const successor_count = analysis.successorCount(block_id);
        for (0..successor_count) |successor_index| {
            const successor = analysis.successorAt(block_id, successor_index) orelse return null;
            if (!included[successor.index()] or indegree[successor.index()] == std.math.maxInt(usize)) return null;
            indegree[successor.index()] += 1;
        }
    }

    var ordered_blocks: std.ArrayList(ir.BlockId) = .empty;
    defer ordered_blocks.deinit(allocator);
    for (function.blocks) |block_id| {
        if (!included[block_id.index()] or indegree[block_id.index()] != 0) continue;
        if (block_id != producer.block) return null;
        try ordered_blocks.append(allocator, block_id);
    }
    cursor = 0;
    while (cursor < ordered_blocks.items.len) : (cursor += 1) {
        const block_id = ordered_blocks.items[cursor];
        if (block_id == consumer_block_id) continue;
        const successor_count = analysis.successorCount(block_id);
        for (0..successor_count) |successor_index| {
            const successor = analysis.successorAt(block_id, successor_index) orelse return null;
            if (indegree[successor.index()] == 0) return null;
            indegree[successor.index()] -= 1;
            if (indegree[successor.index()] == 0) try ordered_blocks.append(allocator, successor);
        }
    }
    if (ordered_blocks.items.len != included_count or
        ordered_blocks.items.len == 0 or
        ordered_blocks.items[ordered_blocks.items.len - 1] != consumer_block_id) return null;

    var moved_edges: std.ArrayList(ReentryEdge) = .empty;
    defer moved_edges.deinit(allocator);
    for (ordered_blocks.items) |block_id| {
        if (block_id == consumer_block_id) continue;
        const successor_count = analysis.successorCount(block_id);
        for (0..successor_count) |successor_index| {
            const successor = analysis.successorAt(block_id, successor_index) orelse return null;
            if (!included[successor.index()]) return null;
            try moved_edges.append(allocator, .{ .source = block_id, .target = successor });
        }
    }

    const seen_gaps = try allocator.alloc(bool, program.instructions.len);
    defer allocator.free(seen_gaps);
    @memset(seen_gaps, false);
    var gaps: std.ArrayList(ir.InstructionId) = .empty;
    defer gaps.deinit(allocator);
    for (ordered_blocks.items) |block_id| {
        const block = program.blocks[block_id.index()];
        const block_gaps = if (block_id == producer.block)
            block.instructions[producer_position + 1 ..]
        else if (block_id == consumer_block_id)
            block.instructions[0..consumer_position]
        else
            block.instructions;
        for (block_gaps) |gap_id| {
            if (!validId(gap_id, program.instructions.len) or seen_gaps[gap_id.index()]) return null;
            const gap = program.instructions[gap_id.index()];
            if (gap.block != block_id or !gapIsMovable(gap)) return null;
            seen_gaps[gap_id.index()] = true;
            try gaps.append(allocator, gap_id);
        }
    }

    const owned_blocks = try ordered_blocks.toOwnedSlice(allocator);
    errdefer allocator.free(owned_blocks);
    const owned_gaps = try gaps.toOwnedSlice(allocator);
    errdefer allocator.free(owned_gaps);
    const owned_moved_edges = try moved_edges.toOwnedSlice(allocator);
    const projection: Projection = .{
        .producer = producer.id,
        .consumer = consumer,
        .pack = pack_id,
        .cfg_fingerprint = cfg_fingerprint,
        .reentry = reentry.kind,
        .blocks = owned_blocks,
        .gaps = owned_gaps,
        .moved_edges = owned_moved_edges,
        .reentry_blocks = reentry.blocks,
        .reentry_edges = reentry.edges,
        .exit_edges = reentry.exit_edges,
    };
    keep_reentry = true;
    return projection;
}

fn reentryAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    moved_blocks: []const bool,
    consumer_block: ir.BlockId,
    producer_block: ir.BlockId,
) std.mem.Allocator.Error!?ReentryProof {
    if (!try analysis.canReach(consumer_block, producer_block)) {
        const blocks = try allocator.alloc(ir.BlockId, 0);
        errdefer allocator.free(blocks);
        const edges = try allocator.alloc(ReentryEdge, 0);
        errdefer allocator.free(edges);
        return .{
            .kind = .none,
            .blocks = blocks,
            .edges = edges,
            .exit_edges = try allocator.alloc(ReentryEdge, 0),
        };
    }

    const included = try allocator.alloc(bool, analysis.program.blocks.len);
    defer allocator.free(included);
    @memset(included, false);
    var pending: std.ArrayList(ir.BlockId) = .empty;
    defer pending.deinit(allocator);
    try pending.append(allocator, consumer_block);
    var edges: std.ArrayList(ReentryEdge) = .empty;
    defer edges.deinit(allocator);
    var exit_edges: std.ArrayList(ReentryEdge) = .empty;
    defer exit_edges.deinit(allocator);
    var has_producer_entry = false;
    var cursor: usize = 0;
    while (cursor < pending.items.len) : (cursor += 1) {
        const source = pending.items[cursor];
        const successor_count = analysis.successorCount(source);
        for (0..successor_count) |successor_index| {
            const successor = analysis.successorAt(source, successor_index) orelse return null;
            if (successor == producer_block) {
                has_producer_entry = true;
                try edges.append(allocator, .{ .source = source, .target = successor });
                continue;
            }
            if (!try analysis.canReach(successor, producer_block)) {
                try exit_edges.append(allocator, .{ .source = source, .target = successor });
                continue;
            }
            if (successor == consumer_block or
                successor.index() >= moved_blocks.len or
                moved_blocks[successor.index()]) return null;
            try edges.append(allocator, .{ .source = source, .target = successor });
            if (included[successor.index()]) continue;
            included[successor.index()] = true;
            try pending.append(allocator, successor);
        }
    }
    if (!has_producer_entry) return null;

    var included_count: usize = 0;
    for (analysis.function.blocks) |block_id| {
        if (!included[block_id.index()]) continue;
        included_count += 1;
        const predecessor_count = analysis.predecessorCount(block_id);
        for (0..predecessor_count) |predecessor_index| {
            const predecessor = analysis.predecessorAt(block_id, predecessor_index) orelse return null;
            if (predecessor != consumer_block and !included[predecessor.index()]) return null;
        }
    }

    const indegree = try allocator.alloc(usize, analysis.program.blocks.len);
    defer allocator.free(indegree);
    @memset(indegree, 0);
    for (edges.items) |edge| {
        if (edge.target == producer_block or edge.source == consumer_block) continue;
        if (!included[edge.source.index()] or !included[edge.target.index()] or
            indegree[edge.target.index()] == std.math.maxInt(usize)) return null;
        indegree[edge.target.index()] += 1;
    }

    var ordered: std.ArrayList(ir.BlockId) = .empty;
    defer ordered.deinit(allocator);
    for (analysis.function.blocks) |block_id| {
        if (included[block_id.index()] and indegree[block_id.index()] == 0) {
            try ordered.append(allocator, block_id);
        }
    }
    cursor = 0;
    while (cursor < ordered.items.len) : (cursor += 1) {
        const source = ordered.items[cursor];
        for (edges.items) |edge| {
            if (edge.source != source or edge.target == producer_block) continue;
            if (indegree[edge.target.index()] == 0) return null;
            indegree[edge.target.index()] -= 1;
            if (indegree[edge.target.index()] == 0) try ordered.append(allocator, edge.target);
        }
    }
    if (ordered.items.len != included_count) return null;

    const owned_blocks = try ordered.toOwnedSlice(allocator);
    errdefer allocator.free(owned_blocks);
    const owned_edges = try edges.toOwnedSlice(allocator);
    errdefer allocator.free(owned_edges);
    const owned_exit_edges = try exit_edges.toOwnedSlice(allocator);
    return .{
        .kind = if (owned_blocks.len == 0) .direct_backedge else .indirect_region,
        .blocks = owned_blocks,
        .edges = owned_edges,
        .exit_edges = owned_exit_edges,
    };
}

fn allocProjection(
    allocator: std.mem.Allocator,
    producer: ir.InstructionId,
    consumer: Consumer,
    pack_id: ir.ValuePackId,
    cfg_fingerprint: projection_witness.CfgFingerprint,
    reentry: Reentry,
    block_ids: []const ir.BlockId,
    first_gaps: []const ir.InstructionId,
    second_gaps: []const ir.InstructionId,
    moved_edges: []const ReentryEdge,
    reentry_blocks: []const ir.BlockId,
    reentry_edges: []const ReentryEdge,
    exit_edges: []const ReentryEdge,
) std.mem.Allocator.Error!Projection {
    const blocks = try allocator.dupe(ir.BlockId, block_ids);
    errdefer allocator.free(blocks);
    const gap_count = std.math.add(usize, first_gaps.len, second_gaps.len) catch return error.OutOfMemory;
    const gaps = try allocator.alloc(ir.InstructionId, gap_count);
    errdefer allocator.free(gaps);
    @memcpy(gaps[0..first_gaps.len], first_gaps);
    @memcpy(gaps[first_gaps.len..], second_gaps);
    const owned_moved_edges = try allocator.dupe(ReentryEdge, moved_edges);
    errdefer allocator.free(owned_moved_edges);
    const owned_reentry_blocks = try allocator.dupe(ir.BlockId, reentry_blocks);
    errdefer allocator.free(owned_reentry_blocks);
    const owned_reentry_edges = try allocator.dupe(ReentryEdge, reentry_edges);
    errdefer allocator.free(owned_reentry_edges);
    const owned_exit_edges = try allocator.dupe(ReentryEdge, exit_edges);
    return .{
        .producer = producer,
        .consumer = consumer,
        .pack = pack_id,
        .cfg_fingerprint = cfg_fingerprint,
        .reentry = reentry,
        .blocks = blocks,
        .gaps = gaps,
        .moved_edges = owned_moved_edges,
        .reentry_blocks = owned_reentry_blocks,
        .reentry_edges = owned_reentry_edges,
        .exit_edges = owned_exit_edges,
    };
}

pub fn isMovable(program: *const ir.Program, projection: Projection) bool {
    return projection_witness.isMovable(program, projection);
}

pub fn gapIsMovable(instruction: ir.Instruction) bool {
    return projection_witness.gapIsMovable(instruction);
}

fn gapSliceIsMovable(program: *const ir.Program, gaps: []const ir.InstructionId, owner: ir.BlockId) bool {
    for (gaps) |gap_id| {
        if (!validId(gap_id, program.instructions.len)) return false;
        const gap = program.instructions[gap_id.index()];
        if (gap.block != owner or !gapIsMovable(gap)) return false;
    }
    return true;
}

fn instructionPosition(block: ir.Block, instruction_id: ir.InstructionId) ?usize {
    var position: ?usize = null;
    for (block.instructions, 0..) |listed_id, index| {
        if (listed_id != instruction_id) continue;
        if (position != null) return null;
        position = index;
    }
    return position;
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}
