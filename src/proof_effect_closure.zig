const std = @import("std");
const ir = @import("ir.zig");

pub const ExpandError = error{InvalidClosureInput} || std.mem.Allocator.Error;

pub fn expand(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    functions: []bool,
    values: []bool,
    instructions: []bool,
    blocks: []bool,
) ExpandError!void {
    const reached = try zeroedBools(allocator, blocks.len);
    defer allocator.free(reached);
    const processed = try zeroedBools(allocator, blocks.len);
    defer allocator.free(processed);
    const boundaries = try allocator.alloc(usize, blocks.len);
    defer allocator.free(boundaries);
    @memset(boundaries, 0);

    for (instructions, 0..) |needed, instruction_index| {
        if (!needed) continue;
        const instruction = program.instructions[instruction_index];
        if (instruction.id.index() != instruction_index or instruction.block.index() >= program.blocks.len) {
            return error.InvalidClosureInput;
        }
        const block = program.blocks[instruction.block.index()];
        if (block.id != instruction.block or block.id.index() >= blocks.len) return error.InvalidClosureInput;
        const position = instructionPosition(block, instruction.id) orelse return error.InvalidClosureInput;
        reached[block.id.index()] = true;
        boundaries[block.id.index()] = @max(boundaries[block.id.index()], position);
    }

    for (values, 0..) |needed, value_index| {
        if (!needed) continue;
        const origin = switch (program.values[value_index].origin) {
            .block_parameter => |origin| origin,
            else => continue,
        };
        if (origin.block.index() >= program.blocks.len) return error.InvalidClosureInput;
        for (program.blocks) |source| {
            if (blockTargets(source, origin.block)) try seedBlockEnd(program, reached, boundaries, source);
        }
    }

    var progressed = true;
    while (progressed) {
        progressed = false;
        for (reached, 0..) |needed, block_index| {
            if (!needed or processed[block_index]) continue;
            processed[block_index] = true;
            progressed = true;

            const block = program.blocks[block_index];
            if (block.id.index() != block_index or block.function.index() >= functions.len or boundaries[block_index] > block.instructions.len) {
                return error.InvalidClosureInput;
            }
            blocks[block_index] = true;
            functions[block.function.index()] = true;
            for (block.instructions[0..boundaries[block_index]]) |instruction_id| {
                if (instruction_id.index() >= program.instructions.len) return error.InvalidClosureInput;
                const instruction = program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id or instruction.block != block.id) return error.InvalidClosureInput;
                if (hasObservableEffects(instruction.effects)) instructions[instruction_id.index()] = true;
            }

            for (program.blocks) |source| {
                if (!blockTargets(source, block.id)) continue;
                if (source.id.index() >= boundaries.len) return error.InvalidClosureInput;
                const previous_boundary = boundaries[source.id.index()];
                try seedBlockEnd(program, reached, boundaries, source);
                if (boundaries[source.id.index()] > previous_boundary) processed[source.id.index()] = false;
                switch (source.terminator) {
                    .branch => |branch| try markEntity(values, branch.condition),
                    .jump, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
                }
            }
        }
    }
}

fn instructionPosition(block: ir.Block, instruction_id: ir.InstructionId) ?usize {
    for (block.instructions, 0..) |candidate, index| {
        if (candidate == instruction_id) return index;
    }
    return null;
}

fn seedBlockEnd(program: *const ir.Program, reached: []bool, boundaries: []usize, block: ir.Block) ExpandError!void {
    if (block.id.index() >= program.blocks.len or block.id.index() >= reached.len) return error.InvalidClosureInput;
    if (program.blocks[block.id.index()].id != block.id) return error.InvalidClosureInput;
    reached[block.id.index()] = true;
    boundaries[block.id.index()] = block.instructions.len;
}

fn blockTargets(block: ir.Block, target: ir.BlockId) bool {
    return switch (block.terminator) {
        .jump => |edge| edge.target == target,
        .branch => |branch| branch.then_edge.target == target or branch.else_edge.target == target,
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => false,
    };
}

pub fn hasObservableEffects(effects: ir.EffectSummary) bool {
    return effects.precision != .exact or
        effects.reads_memory or
        effects.writes_memory or
        effects.may_throw or
        effects.may_yield or
        effects.invokes_unknown_code;
}

fn zeroedBools(allocator: std.mem.Allocator, count: usize) std.mem.Allocator.Error![]bool {
    const values = try allocator.alloc(bool, count);
    @memset(values, false);
    return values;
}

fn markEntity(entities: anytype, id: anytype) ExpandError!void {
    if (id.index() >= entities.len) return error.InvalidClosureInput;
    entities[id.index()] = true;
}
