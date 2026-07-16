const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");

pub const Entry = struct {
    block: ir.BlockId,
    incoming: []ir.CfgEdgeRef,
    is_function_entry: bool,
};

pub const Region = struct {
    blocks: []ir.BlockId,
    entries: []Entry,
};

pub const Analysis = struct {
    allocator: std.mem.Allocator,
    regions: []Region,

    pub fn deinit(self: *Analysis) void {
        for (self.regions) |region| destroyRegion(self.allocator, region);
        self.allocator.free(self.regions);
        self.* = undefined;
    }
};

const DfsFrame = struct {
    local_index: usize,
    next_successor: usize = 0,
};

pub fn analyze(allocator: std.mem.Allocator, graph: *const cfg.Analysis) std.mem.Allocator.Error!Analysis {
    const block_count = graph.function.blocks.len;
    const visited = try allocator.alloc(bool, block_count);
    defer allocator.free(visited);
    @memset(visited, false);
    const finish_order = try allocator.alloc(usize, block_count);
    defer allocator.free(finish_order);
    const frames = try allocator.alloc(DfsFrame, block_count);
    defer allocator.free(frames);

    var finish_len: usize = 0;
    for (graph.function.blocks, 0..) |block_id, start_index| {
        if (!graph.isReachable(block_id) or visited[start_index]) continue;
        visited[start_index] = true;
        var frame_len: usize = 1;
        frames[0] = .{ .local_index = start_index };
        while (frame_len != 0) {
            const frame = &frames[frame_len - 1];
            const source = graph.function.blocks[frame.local_index];
            const outgoing = successorTargets(graph.program.blocks[source.index()].terminator);
            if (frame.next_successor < outgoing.len) {
                const target = outgoing.ids[frame.next_successor];
                frame.next_successor += 1;
                const target_index = graph.blockIndex(target) orelse continue;
                if (!graph.isReachable(target) or visited[target_index]) continue;
                visited[target_index] = true;
                frames[frame_len] = .{ .local_index = target_index };
                frame_len += 1;
                continue;
            }
            finish_order[finish_len] = frame.local_index;
            finish_len += 1;
            frame_len -= 1;
        }
    }

    const unassigned = std.math.maxInt(usize);
    const component_of = try allocator.alloc(usize, block_count);
    defer allocator.free(component_of);
    @memset(component_of, unassigned);
    const reverse_stack = try allocator.alloc(usize, block_count);
    defer allocator.free(reverse_stack);
    var components: std.ArrayList(std.ArrayList(usize)) = .empty;
    defer {
        for (components.items) |*component| component.deinit(allocator);
        components.deinit(allocator);
    }

    var finish_index = finish_len;
    while (finish_index != 0) {
        finish_index -= 1;
        const start_index = finish_order[finish_index];
        if (component_of[start_index] != unassigned) continue;
        const component_id = components.items.len;
        try components.append(allocator, .empty);
        component_of[start_index] = component_id;
        var stack_len: usize = 1;
        reverse_stack[0] = start_index;
        while (stack_len != 0) {
            stack_len -= 1;
            const local_index = reverse_stack[stack_len];
            try components.items[component_id].append(allocator, local_index);
            const block_id = graph.function.blocks[local_index];
            const predecessor_count = graph.predecessorCount(block_id);
            for (0..predecessor_count) |predecessor_index| {
                const predecessor = graph.predecessorAt(block_id, predecessor_index) orelse continue;
                const predecessor_local = graph.blockIndex(predecessor) orelse continue;
                if (!graph.isReachable(predecessor) or component_of[predecessor_local] != unassigned) continue;
                component_of[predecessor_local] = component_id;
                reverse_stack[stack_len] = predecessor_local;
                stack_len += 1;
            }
        }
    }

    var regions: std.ArrayList(Region) = .empty;
    errdefer {
        for (regions.items) |region| destroyRegion(allocator, region);
        regions.deinit(allocator);
    }
    for (components.items, 0..) |component, component_id| {
        if (!isCyclic(graph, component.items)) continue;
        var entry_blocks: std.ArrayList(ir.BlockId) = .empty;
        defer entry_blocks.deinit(allocator);
        for (component.items) |local_index| {
            const block_id = graph.function.blocks[local_index];
            var is_entry = block_id == graph.function.entry_block;
            const predecessor_count = graph.predecessorCount(block_id);
            for (0..predecessor_count) |predecessor_index| {
                const predecessor = graph.predecessorAt(block_id, predecessor_index) orelse continue;
                if (!graph.isReachable(predecessor)) continue;
                const predecessor_local = graph.blockIndex(predecessor) orelse continue;
                if (component_of[predecessor_local] != component_id) {
                    is_entry = true;
                    break;
                }
            }
            if (is_entry) try entry_blocks.append(allocator, block_id);
        }
        if (entry_blocks.items.len <= 1) continue;

        const blocks = try allocator.alloc(ir.BlockId, component.items.len);
        errdefer allocator.free(blocks);
        for (component.items, 0..) |local_index, index| blocks[index] = graph.function.blocks[local_index];
        std.sort.heap(ir.BlockId, blocks, {}, lessBlock);
        std.sort.heap(ir.BlockId, entry_blocks.items, {}, lessBlock);

        const entries = try allocator.alloc(Entry, entry_blocks.items.len);
        errdefer allocator.free(entries);
        var initialized_entries: usize = 0;
        errdefer for (entries[0..initialized_entries]) |entry| allocator.free(entry.incoming);
        for (entry_blocks.items, 0..) |entry_block, entry_index| {
            var incoming: std.ArrayList(ir.CfgEdgeRef) = .empty;
            errdefer incoming.deinit(allocator);
            for (graph.function.blocks) |source| {
                const source_local = graph.blockIndex(source) orelse continue;
                if (!graph.isReachable(source) or component_of[source_local] == component_id) continue;
                try appendEdgesTo(allocator, &incoming, graph.program, source, entry_block);
            }
            std.sort.heap(ir.CfgEdgeRef, incoming.items, {}, lessEdge);
            entries[entry_index] = .{
                .block = entry_block,
                .incoming = try incoming.toOwnedSlice(allocator),
                .is_function_entry = entry_block == graph.function.entry_block,
            };
            initialized_entries += 1;
        }

        const region: Region = .{ .blocks = blocks, .entries = entries };
        regions.append(allocator, region) catch |err| {
            destroyRegion(allocator, region);
            return err;
        };
    }
    std.sort.heap(Region, regions.items, {}, lessRegion);
    return .{ .allocator = allocator, .regions = try regions.toOwnedSlice(allocator) };
}

fn isCyclic(graph: *const cfg.Analysis, component: []const usize) bool {
    if (component.len > 1) return true;
    if (component.len == 0) return false;
    const block_id = graph.function.blocks[component[0]];
    const outgoing = successorTargets(graph.program.blocks[block_id.index()].terminator);
    for (outgoing.ids[0..outgoing.len]) |target| if (target == block_id) return true;
    return false;
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

fn appendEdgesTo(
    allocator: std.mem.Allocator,
    edges: *std.ArrayList(ir.CfgEdgeRef),
    program: *const ir.Program,
    source: ir.BlockId,
    target: ir.BlockId,
) std.mem.Allocator.Error!void {
    switch (program.blocks[source.index()].terminator) {
        .jump => |edge| if (edge.target == target) try edges.append(allocator, .{ .source = source, .kind = .jump, .target = target }),
        .branch => |branch| {
            if (branch.then_edge.target == target) try edges.append(allocator, .{ .source = source, .kind = .branch_then, .target = target });
            if (branch.else_edge.target == target) try edges.append(allocator, .{ .source = source, .kind = .branch_else, .target = target });
        },
        else => {},
    }
}

fn lessBlock(_: void, left: ir.BlockId, right: ir.BlockId) bool {
    return left.index() < right.index();
}

fn lessEdge(_: void, left: ir.CfgEdgeRef, right: ir.CfgEdgeRef) bool {
    if (left.source != right.source) return left.source.index() < right.source.index();
    if (left.kind != right.kind) return @intFromEnum(left.kind) < @intFromEnum(right.kind);
    return left.target.index() < right.target.index();
}

fn lessRegion(_: void, left: Region, right: Region) bool {
    return left.blocks[0].index() < right.blocks[0].index();
}

fn destroyRegion(allocator: std.mem.Allocator, region: Region) void {
    for (region.entries) |entry| allocator.free(entry.incoming);
    allocator.free(region.entries);
    allocator.free(region.blocks);
}

test "irreducible SCC analysis records canonical entry edges" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const first = ir.BlockId.fromIndex(1);
    const second = ir.BlockId.fromIndex(2);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first },
            .else_edge = .{ .target = second },
        } } },
        .{ .id = first, .function = function_id, .terminator = .{ .jump = .{ .target = second } } },
        .{ .id = second, .function = function_id, .terminator = .{ .jump = .{ .target = first } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ second, entry, first },
        .parameters = &.{condition},
        .entry_block = entry,
    }};
    const values = [_]ir.Value{.{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } }};
    const program: ir.Program = .{
        .program_id = "irreducible-region-entries",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var graph = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer graph.deinit();
    var result = try analyze(std.testing.allocator, &graph);
    defer result.deinit();

    try std.testing.expectEqual(@as(usize, 1), result.regions.len);
    const region = result.regions[0];
    try std.testing.expectEqualSlices(ir.BlockId, &.{ first, second }, region.blocks);
    try std.testing.expectEqual(@as(usize, 2), region.entries.len);
    try std.testing.expectEqual(first, region.entries[0].block);
    try std.testing.expectEqual(second, region.entries[1].block);
    try std.testing.expect(!region.entries[0].is_function_entry);
    try std.testing.expectEqualSlices(ir.CfgEdgeRef, &.{.{ .source = entry, .kind = .branch_then, .target = first }}, region.entries[0].incoming);
    try std.testing.expectEqualSlices(ir.CfgEdgeRef, &.{.{ .source = entry, .kind = .branch_else, .target = second }}, region.entries[1].incoming);
}

test "single-entry cycles remain reducible" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ entry, header, body, exit },
        .parameters = &.{condition},
        .entry_block = entry,
    }};
    const values = [_]ir.Value{.{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } }};
    const program: ir.Program = .{
        .program_id = "single-entry-cycle",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var graph = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer graph.deinit();
    var result = try analyze(std.testing.allocator, &graph);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 0), result.regions.len);
}

test "unreachable predecessors do not manufacture SCC entries" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const unreachable_witness = ir.BlockId.fromIndex(1);
    const header = ir.BlockId.fromIndex(2);
    const body = ir.BlockId.fromIndex(3);
    const exit_block = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = unreachable_witness, .function = function_id, .terminator = .{ .jump = .{ .target = body } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit_block },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, unreachable_witness, header, body, exit_block },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{.{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } }};
    const program: ir.Program = .{
        .program_id = "unreachable-scc-entry-witness",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };

    var graph = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer graph.deinit();
    var analysis = try analyze(std.testing.allocator, &graph);
    defer analysis.deinit();
    try std.testing.expectEqual(@as(usize, 0), analysis.regions.len);
}

test "a whole-function cycle has only its function entry" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const next = ir.BlockId.fromIndex(1);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = next } } },
        .{ .id = next, .function = function_id, .terminator = .{ .jump = .{ .target = entry } } },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &.{ next, entry }, .entry_block = entry }};
    const program: ir.Program = .{
        .program_id = "whole-function-cycle",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var graph = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer graph.deinit();
    var result = try analyze(std.testing.allocator, &graph);
    defer result.deinit();
    try std.testing.expectEqual(@as(usize, 0), result.regions.len);
}
