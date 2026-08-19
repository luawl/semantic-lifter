const std = @import("std");
const ir = @import("ir.zig");

pub const Error = error{UnsupportedControlFlow};

pub const LoopBoundaryBodyExit = enum {
    parent_stop,
    continue_target,
};

pub fn validateEdge(program: *const ir.Program, entry: ir.BlockId, stop: ir.BlockId) Error!ir.Edge {
    if (entry == stop or entry.index() >= program.blocks.len or stop.index() >= program.blocks.len) {
        return error.UnsupportedControlFlow;
    }
    const function = program.blocks[stop.index()].function;
    if (program.blocks[entry.index()].function != function) return error.UnsupportedControlFlow;

    var current = entry;
    var traversed: usize = 0;
    while (current != stop) : (traversed += 1) {
        if (traversed >= program.blocks.len or current.index() >= program.blocks.len) return error.UnsupportedControlFlow;
        const block = program.blocks[current.index()];
        if (block.function != function) return error.UnsupportedControlFlow;
        if (block.parameters.len != 0 or block.instructions.len != 0) return error.UnsupportedControlFlow;
        const edge = switch (block.terminator) {
            .jump => |value| value,
            else => return error.UnsupportedControlFlow,
        };
        if (edge.target.index() >= program.blocks.len or program.blocks[edge.target.index()].function != function) {
            return error.UnsupportedControlFlow;
        }
        if (edge.target == stop) {
            if (edge.arguments.len != program.blocks[stop.index()].parameters.len) return error.UnsupportedControlFlow;
            return edge;
        }
        if (edge.arguments.len != 0) return error.UnsupportedControlFlow;
        current = edge.target;
    }
    return error.UnsupportedControlFlow;
}

pub fn validateLoopBoundaryBody(
    program: *const ir.Program,
    region_stop: ?ir.BlockId,
    region_loop_exit: ?ir.BlockId,
    region_continue_target: ?ir.BlockId,
    body_stop: ?ir.BlockId,
    body_loop_exit: ?ir.BlockId,
    body_continue_target: ?ir.BlockId,
) Error!LoopBoundaryBodyExit {
    const parent = region_stop orelse return error.UnsupportedControlFlow;
    const body = body_stop orelse return error.UnsupportedControlFlow;
    if (body == parent) return .parent_stop;
    if (body_loop_exit != region_loop_exit) return error.UnsupportedControlFlow;
    if (region_continue_target) |continue_target| {
        if (body == continue_target) {
            if (body_continue_target == null or body_continue_target.? != continue_target) {
                return error.UnsupportedControlFlow;
            }
            return .continue_target;
        }
    }
    const forwarding_edge = try validateEdge(program, body, parent);
    if (forwarding_edge.arguments.len != 0) return error.UnsupportedControlFlow;
    return .parent_stop;
}

test "loop boundary body may stop at a transparent route to its parent stop" {
    const function_id = ir.FunctionId.fromIndex(0);
    const relay = ir.BlockId.fromIndex(0);
    const stop = ir.BlockId.fromIndex(1);
    const loop_exit = ir.BlockId.fromIndex(2);
    var blocks = [_]ir.Block{
        .{ .id = relay, .function = function_id, .terminator = .{ .jump = .{ .target = stop } } },
        .{ .id = stop, .function = function_id, .terminator = .{ .jump = .{ .target = loop_exit } } },
        .{ .id = loop_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .blocks = &.{ relay, stop, loop_exit },
        .entry_block = relay,
    };
    const program: ir.Program = .{
        .program_id = "transparent-loop-boundary-stop",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };

    try std.testing.expectEqual(
        LoopBoundaryBodyExit.parent_stop,
        try validateLoopBoundaryBody(&program, stop, loop_exit, null, relay, loop_exit, null),
    );
    try std.testing.expectEqual(
        LoopBoundaryBodyExit.parent_stop,
        try validateLoopBoundaryBody(&program, stop, null, null, stop, loop_exit, null),
    );
    blocks[relay.index()].instructions = &.{ir.InstructionId.fromIndex(0)};
    try std.testing.expectError(
        error.UnsupportedControlFlow,
        validateLoopBoundaryBody(&program, stop, loop_exit, null, relay, loop_exit, null),
    );
}

test "loop boundary body may stop at its authenticated enclosing continue" {
    const function_id = ir.FunctionId.fromIndex(0);
    const parent_stop = ir.BlockId.fromIndex(0);
    const continue_target = ir.BlockId.fromIndex(1);
    const loop_exit = ir.BlockId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = parent_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = continue_target, .function = function_id, .instructions = &.{ir.InstructionId.fromIndex(0)}, .terminator = .{ .jump = .{ .target = parent_stop } } },
        .{ .id = loop_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .blocks = &.{ parent_stop, continue_target, loop_exit },
        .entry_block = continue_target,
    };
    const program: ir.Program = .{
        .program_id = "loop-boundary-enclosing-continue",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };

    try std.testing.expectEqual(
        LoopBoundaryBodyExit.continue_target,
        try validateLoopBoundaryBody(
            &program,
            parent_stop,
            loop_exit,
            continue_target,
            continue_target,
            loop_exit,
            continue_target,
        ),
    );
    try std.testing.expectError(
        error.UnsupportedControlFlow,
        validateLoopBoundaryBody(
            &program,
            parent_stop,
            loop_exit,
            continue_target,
            continue_target,
            loop_exit,
            null,
        ),
    );
}
