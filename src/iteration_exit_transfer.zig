const ir = @import("ir.zig");
const cfg = @import("cfg.zig");

pub fn supportsInvariantArguments(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    header_id: ir.BlockId,
    exit_edge: ir.Edge,
) !bool {
    if (!validId(header_id, program.blocks.len) or
        !validId(exit_edge.target, program.blocks.len) or
        header_id == exit_edge.target or
        !analysis.isReachable(header_id) or
        !analysis.isReachable(exit_edge.target)) return false;

    const header = program.blocks[header_id.index()];
    const target = program.blocks[exit_edge.target.index()];
    if (header.id != header_id or target.id != exit_edge.target or
        header.function != target.function or
        exit_edge.arguments.len != target.parameters.len) return false;

    for (target.parameters, exit_edge.arguments, 0..) |parameter, argument, index| {
        if (!canonicalBlockParameter(program, target, parameter, index) or
            !try valueIsStableBeforeHeader(program, analysis, header, exit_edge.target, argument)) return false;
    }
    return true;
}

fn valueIsStableBeforeHeader(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    header: ir.Block,
    exit_target: ir.BlockId,
    value_id: ir.ValueId,
) !bool {
    if (!validId(value_id, program.values.len) or !validId(header.function, program.functions.len)) return false;
    const value = program.values[value_id.index()];
    if (value.id != value_id or value.function != header.function) return false;
    const function = program.functions[header.function.index()];
    if (function.id != header.function) return false;

    return switch (value.origin) {
        .parameter => |parameter_index| blk: {
            const index: usize = @intCast(parameter_index);
            break :blk index < function.parameters.len and function.parameters[index] == value_id;
        },
        .capture => |capture_id| canonicalImmutableCapture(program, function, capture_id, value_id),
        .instruction_result => |origin| blk: {
            if (!validId(origin.instruction, program.instructions.len)) break :blk false;
            const instruction = program.instructions[origin.instruction.index()];
            const result_index: usize = @intCast(origin.index);
            if (instruction.id != origin.instruction or result_index >= instruction.results.len or
                instruction.results[result_index] != value_id or
                !validId(instruction.block, program.blocks.len)) break :blk false;
            break :blk try definitionBlockIsStable(analysis, header, exit_target, program.blocks[instruction.block.index()]);
        },
        .block_parameter => |origin| blk: {
            if (!validId(origin.block, program.blocks.len)) break :blk false;
            const block = program.blocks[origin.block.index()];
            const parameter_index: usize = @intCast(origin.index);
            if (!canonicalBlockParameter(program, block, value_id, parameter_index)) break :blk false;
            break :blk try definitionBlockIsStable(analysis, header, exit_target, block);
        },
    };
}

fn definitionBlockIsStable(
    analysis: *const cfg.Analysis,
    header: ir.Block,
    exit_target: ir.BlockId,
    definition: ir.Block,
) !bool {
    if (definition.function != header.function or definition.id == header.id or
        !analysis.isReachable(definition.id) or
        !analysis.dominates(definition.id, header.id)) return false;
    return !try analysis.canReachAvoiding(header.id, definition.id, exit_target);
}

fn canonicalBlockParameter(
    program: *const ir.Program,
    block: ir.Block,
    value_id: ir.ValueId,
    parameter_index: usize,
) bool {
    if (!validId(block.id, program.blocks.len) or program.blocks[block.id.index()].id != block.id or
        parameter_index >= block.parameters.len or block.parameters[parameter_index] != value_id or
        !validId(value_id, program.values.len)) return false;
    const value = program.values[value_id.index()];
    return value.id == value_id and value.function == block.function and switch (value.origin) {
        .block_parameter => |origin| origin.block == block.id and origin.index == parameter_index,
        else => false,
    };
}

fn canonicalImmutableCapture(
    program: *const ir.Program,
    function: ir.Function,
    capture_id: ir.CaptureId,
    value_id: ir.ValueId,
) bool {
    if (!validId(capture_id, program.captures.len)) return false;
    var listed = false;
    for (function.captures) |candidate| listed = listed or candidate == capture_id;
    if (!listed) return false;
    const capture = program.captures[capture_id.index()];
    if (capture.id != capture_id or capture.function != function.id) return false;
    return switch (capture.kind) {
        .immutable_value => |captured| captured == value_id,
        .shared_place => false,
    };
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}
