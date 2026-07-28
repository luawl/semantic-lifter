const std = @import("std");
const ir = @import("ir.zig");
const edge_path = @import("edge_path.zig");
const control_flow = @import("control_flow.zig");

pub const Cut = struct {
    edge: ir.Edge,
    prefix_len: usize,
};

pub fn findAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    current: ir.CfgEdgeRef,
    stop: ir.BlockId,
) std.mem.Allocator.Error!?Cut {
    if (current.target == stop) return null;
    const history = try edge_path.historyForCurrentEdgeAlloc(allocator, program, current) orelse return null;
    defer allocator.free(history.rewrites);
    if (history.rewrites.len == 0) return null;

    const first_id = history.rewrites[0];
    if (first_id.index() >= program.edge_rewrites.len) return null;
    var edge = program.edge_rewrites[first_id.index()].from;
    for (0..history.rewrites.len) |prefix_len| {
        if (edge.target == stop and try suffixReplaysAlloc(
            allocator,
            program,
            current,
            edge,
            history.rewrites[prefix_len..],
        )) {
            return .{ .edge = edge, .prefix_len = prefix_len };
        }
        const rewrite_id = history.rewrites[prefix_len];
        if (rewrite_id.index() >= program.edge_rewrites.len) return null;
        edge = program.edge_rewrites[rewrite_id.index()].to;
    }
    return null;
}

fn suffixReplaysAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    current: ir.CfgEdgeRef,
    cut: ir.Edge,
    suffix: []const ir.EdgeRewriteId,
) std.mem.Allocator.Error!bool {
    if (suffix.len == 0) return false;
    var edge = cut;
    for (suffix) |rewrite_id| {
        if (rewrite_id.index() >= program.edge_rewrites.len) return false;
        const rewrite = program.edge_rewrites[rewrite_id.index()];
        if (rewrite.id != rewrite_id or rewrite.source != current.source or rewrite.kind != current.kind or
            rewrite.rule != .forwarding_jump or rewrite.certificate != null or !sameEdge(rewrite.from, edge))
        {
            return false;
        }
        const replayed = try control_flow.replayForwardingJump(allocator, program, edge) orelse return false;
        const matches = sameEdge(replayed, rewrite.to);
        if (replayed.arguments.len != 0) allocator.free(replayed.arguments);
        if (!matches) return false;
        edge = rewrite.to;
    }
    const live = @import("cfg_edge.zig").value(program, current) orelse return false;
    return sameEdge(edge, live);
}

fn sameEdge(left: ir.Edge, right: ir.Edge) bool {
    return left.target == right.target and std.mem.eql(ir.ValueId, left.arguments, right.arguments);
}

test "forwarding history can be cut at an argument-preserving local stop" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const root = ir.BlockId.fromIndex(1);
    const stop = ir.BlockId.fromIndex(2);
    const relay = ir.BlockId.fromIndex(3);
    const live_target = ir.BlockId.fromIndex(4);
    const input = ir.ValueId.fromIndex(0);
    const root_parameter = ir.ValueId.fromIndex(1);
    const stop_parameter = ir.ValueId.fromIndex(2);
    const relay_parameter = ir.ValueId.fromIndex(3);
    const live_parameter = ir.ValueId.fromIndex(4);
    var blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .branch = .{
            .condition = input,
            .then_edge = .{ .target = live_target, .arguments = &.{input} },
            .else_edge = .{ .target = live_target, .arguments = &.{input} },
        } } },
        .{ .id = root, .function = function_id, .parameters = &.{root_parameter}, .terminator = .{ .jump = .{
            .target = stop,
            .arguments = &.{root_parameter},
        } } },
        .{ .id = stop, .function = function_id, .parameters = &.{stop_parameter}, .terminator = .{ .jump = .{
            .target = relay,
            .arguments = &.{stop_parameter},
        } } },
        .{ .id = relay, .function = function_id, .parameters = &.{relay_parameter}, .terminator = .{ .jump = .{
            .target = live_target,
            .arguments = &.{relay_parameter},
        } } },
        .{ .id = live_target, .function = function_id, .parameters = &.{live_parameter}, .terminator = .{ .return_values = &.{live_parameter} } },
    };
    const values = [_]ir.Value{
        .{ .id = input, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = root_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = root, .index = 0 } } },
        .{ .id = stop_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = stop, .index = 0 } } },
        .{ .id = relay_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = relay, .index = 0 } } },
        .{ .id = live_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = live_target, .index = 0 } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{input},
        .blocks = &.{ source, root, stop, relay, live_target },
        .entry_block = source,
    }};
    var rewrites = [_]ir.CfgEdgeRewrite{
        .{ .id = ir.EdgeRewriteId.fromIndex(0), .source = source, .kind = .branch_else, .from = .{ .target = root, .arguments = &.{input} }, .to = .{ .target = stop, .arguments = &.{input} }, .rule = .forwarding_jump },
        .{ .id = ir.EdgeRewriteId.fromIndex(1), .source = source, .kind = .branch_else, .from = .{ .target = stop, .arguments = &.{input} }, .to = .{ .target = relay, .arguments = &.{input} }, .rule = .forwarding_jump },
        .{ .id = ir.EdgeRewriteId.fromIndex(2), .source = source, .kind = .branch_else, .from = .{ .target = relay, .arguments = &.{input} }, .to = .{ .target = live_target, .arguments = &.{input} }, .rule = .forwarding_jump },
    };
    var program: ir.Program = .{
        .program_id = "forwarding-history-cut",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    const reference: ir.CfgEdgeRef = .{ .source = source, .kind = .branch_else, .target = live_target };
    const cut = (try findAlloc(std.testing.allocator, &program, reference, stop)).?;
    try std.testing.expectEqual(@as(usize, 1), cut.prefix_len);
    try std.testing.expectEqual(stop, cut.edge.target);
    try std.testing.expectEqualSlices(ir.ValueId, &.{input}, cut.edge.arguments);

    rewrites[1].rule = .proved_branch;
    try std.testing.expect((try findAlloc(std.testing.allocator, &program, reference, stop)) == null);
    rewrites[1].rule = .forwarding_jump;
    blocks[source.index()].terminator.branch.else_edge.target = relay;
    try std.testing.expect((try findAlloc(std.testing.allocator, &program, reference, stop)) == null);
}
