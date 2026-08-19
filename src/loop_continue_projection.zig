const std = @import("std");
const ir = @import("ir.zig");
const control_flow = @import("control_flow.zig");

pub const Error = error{UnsupportedControlFlow};

pub fn validateEntry(program: *const ir.Program, target: ir.BlockId, edge: ir.Edge) Error!ir.Edge {
    if (target.index() >= program.blocks.len or edge.target != target) return error.UnsupportedControlFlow;
    if (edge.arguments.len != program.blocks[target.index()].parameters.len) return error.UnsupportedControlFlow;
    return edge;
}

pub fn validateFinal(
    program: *const ir.Program,
    source: ir.BlockId,
    target: ir.BlockId,
    expected: ir.Edge,
) Error!ir.Edge {
    if (source.index() >= program.blocks.len or target.index() >= program.blocks.len) {
        return error.UnsupportedControlFlow;
    }
    const source_block = program.blocks[source.index()];
    if (source_block.function != program.blocks[target.index()].function) return error.UnsupportedControlFlow;
    const live = switch (source_block.terminator) {
        .jump => |edge| edge,
        else => return error.UnsupportedControlFlow,
    };
    if (live.target != expected.target or !std.mem.eql(ir.ValueId, live.arguments, expected.arguments)) {
        return error.UnsupportedControlFlow;
    }
    return validateEntry(program, target, live);
}

pub fn validateStructuredLoopExit(
    program: *const ir.Program,
    header: ir.BlockId,
    body_on_true: bool,
    target: ir.BlockId,
    planned: ir.Edge,
    expected: ir.Edge,
) Error!ir.Edge {
    if (header.index() >= program.blocks.len or target.index() >= program.blocks.len or
        program.blocks[header.index()].function != program.blocks[target.index()].function)
    {
        return error.UnsupportedControlFlow;
    }
    const branch = switch (program.blocks[header.index()].terminator) {
        .branch => |value| value,
        else => return error.UnsupportedControlFlow,
    };
    const live = if (body_on_true) branch.else_edge else branch.then_edge;
    if (!sameEdge(live, planned) or !sameEdge(planned, expected)) return error.UnsupportedControlFlow;
    return validateEntry(program, target, live);
}

pub fn validateForwardingFinalAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source: ir.BlockId,
    target: ir.BlockId,
    expected: control_flow.ForwardingPath,
) (Error || std.mem.Allocator.Error)!ir.Edge {
    if (source.index() >= program.blocks.len or target.index() >= program.blocks.len or expected.blocks.len == 0) {
        return error.UnsupportedControlFlow;
    }
    const source_block = program.blocks[source.index()];
    if (source_block.function != program.blocks[target.index()].function) return error.UnsupportedControlFlow;
    const live = switch (source_block.terminator) {
        .jump => |edge| edge,
        else => return error.UnsupportedControlFlow,
    };
    var replayed = try control_flow.replayForwardingPathTo(allocator, program, live, target) orelse return error.UnsupportedControlFlow;
    defer replayed.deinit(allocator);
    if (!sameEdge(replayed.edge, expected.edge) or
        !std.mem.eql(ir.BlockId, replayed.blocks, expected.blocks))
    {
        return error.UnsupportedControlFlow;
    }
    _ = try validateEntry(program, target, replayed.edge);
    return live;
}

fn sameEdge(left: ir.Edge, right: ir.Edge) bool {
    return left.target == right.target and std.mem.eql(ir.ValueId, left.arguments, right.arguments);
}

test "final continue projection authenticates an effectful source edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const parameter = ir.ValueId.fromIndex(0);
    const argument = ir.ValueId.fromIndex(1);
    const edge: ir.Edge = .{ .target = header, .arguments = &.{argument} };
    var blocks = [_]ir.Block{
        .{
            .id = source,
            .function = function_id,
            .instructions = &.{ir.InstructionId.fromIndex(0)},
            .terminator = .{ .jump = edge },
        },
        .{
            .id = header,
            .function = function_id,
            .parameters = &.{parameter},
            .terminator = .{ .jump = .{ .target = source } },
        },
    };
    const program: ir.Program = .{
        .program_id = "continue-projection-validation",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };

    const validated = try validateFinal(&program, source, header, edge);
    try std.testing.expectEqual(header, validated.target);
    try std.testing.expectEqualSlices(ir.ValueId, &.{argument}, validated.arguments);

    const wrong: ir.Edge = .{ .target = header, .arguments = &.{parameter} };
    try std.testing.expectError(error.UnsupportedControlFlow, validateFinal(&program, source, header, wrong));
    blocks[source.index()].terminator = .{ .branch = .{
        .condition = argument,
        .then_edge = edge,
        .else_edge = edge,
    } };
    try std.testing.expectError(error.UnsupportedControlFlow, validateFinal(&program, source, header, edge));
}

test "structured loop continue projection authenticates the exact exit edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const body = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const condition = ir.ValueId.fromIndex(0);
    const parameter = ir.ValueId.fromIndex(1);
    const argument = ir.ValueId.fromIndex(2);
    const body_edge: ir.Edge = .{ .target = body };
    const exit_edge: ir.Edge = .{ .target = target, .arguments = &.{argument} };
    const blocks = [_]ir.Block{
        .{
            .id = header,
            .function = function_id,
            .terminator = .{ .branch = .{
                .condition = condition,
                .then_edge = body_edge,
                .else_edge = exit_edge,
            } },
        },
        .{
            .id = body,
            .function = function_id,
            .terminator = .{ .jump = .{ .target = header } },
        },
        .{
            .id = target,
            .function = function_id,
            .parameters = &.{parameter},
            .terminator = .{ .return_values = &.{} },
        },
    };
    const program: ir.Program = .{
        .program_id = "structured-loop-continue-projection",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };

    const validated = try validateStructuredLoopExit(&program, header, true, target, exit_edge, exit_edge);
    try std.testing.expectEqual(target, validated.target);
    try std.testing.expectEqualSlices(ir.ValueId, &.{argument}, validated.arguments);

    const wrong: ir.Edge = .{ .target = target, .arguments = &.{parameter} };
    try std.testing.expectError(
        error.UnsupportedControlFlow,
        validateStructuredLoopExit(&program, header, true, target, exit_edge, wrong),
    );
    try std.testing.expectError(
        error.UnsupportedControlFlow,
        validateStructuredLoopExit(&program, header, false, target, exit_edge, exit_edge),
    );
}

test "forwarding continue projection authenticates source route and mapped arguments" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const first = ir.BlockId.fromIndex(1);
    const second = ir.BlockId.fromIndex(2);
    const header = ir.BlockId.fromIndex(3);
    const argument = ir.ValueId.fromIndex(0);
    const first_parameter = ir.ValueId.fromIndex(1);
    const second_parameter = ir.ValueId.fromIndex(2);
    const header_parameter = ir.ValueId.fromIndex(3);
    var blocks = [_]ir.Block{
        .{
            .id = source,
            .function = function_id,
            .terminator = .{ .jump = .{ .target = first, .arguments = &.{argument} } },
        },
        .{
            .id = first,
            .function = function_id,
            .parameters = &.{first_parameter},
            .terminator = .{ .jump = .{ .target = second, .arguments = &.{first_parameter} } },
        },
        .{
            .id = second,
            .function = function_id,
            .parameters = &.{second_parameter},
            .terminator = .{ .jump = .{ .target = header, .arguments = &.{second_parameter} } },
        },
        .{
            .id = header,
            .function = function_id,
            .parameters = &.{header_parameter},
            .terminator = .{ .jump = .{ .target = source } },
        },
    };
    const values = [_]ir.Value{
        .{ .id = argument, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = first_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = first, .index = 0 } } },
        .{ .id = second_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = second, .index = 0 } } },
        .{ .id = header_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
    };
    const program: ir.Program = .{
        .program_id = "forwarding-continue-projection",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var expected_blocks = [_]ir.BlockId{ first, second };
    const expected: control_flow.ForwardingPath = .{
        .edge = .{ .target = header, .arguments = &.{argument} },
        .blocks = &expected_blocks,
    };

    const validated = try validateForwardingFinalAlloc(std.testing.allocator, &program, source, header, expected);
    try std.testing.expectEqual(first, validated.target);
    try std.testing.expectEqualSlices(ir.ValueId, &.{argument}, validated.arguments);

    var wrong_route_blocks = [_]ir.BlockId{ second, first };
    const wrong_route: control_flow.ForwardingPath = .{
        .edge = expected.edge,
        .blocks = &wrong_route_blocks,
    };
    try std.testing.expectError(
        error.UnsupportedControlFlow,
        validateForwardingFinalAlloc(std.testing.allocator, &program, source, header, wrong_route),
    );
    const wrong_arguments: control_flow.ForwardingPath = .{
        .edge = .{ .target = header, .arguments = &.{header_parameter} },
        .blocks = expected.blocks,
    };
    try std.testing.expectError(
        error.UnsupportedControlFlow,
        validateForwardingFinalAlloc(std.testing.allocator, &program, source, header, wrong_arguments),
    );

    blocks[second.index()].terminator = .{ .branch = .{
        .condition = second_parameter,
        .then_edge = .{ .target = header, .arguments = &.{second_parameter} },
        .else_edge = .{ .target = header, .arguments = &.{second_parameter} },
    } };
    try std.testing.expectError(
        error.UnsupportedControlFlow,
        validateForwardingFinalAlloc(std.testing.allocator, &program, source, header, expected),
    );
}
