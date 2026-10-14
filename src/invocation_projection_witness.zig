const std = @import("std");
const ir = @import("ir.zig");

const Sha256 = std.crypto.hash.sha2.Sha256;
pub const CfgFingerprint = [Sha256.digest_length]u8;

pub fn cfgFingerprint(program: *const ir.Program, function_id: ir.FunctionId) ?CfgFingerprint {
    if (!validId(function_id, program.functions.len)) return null;
    const function = program.functions[function_id.index()];
    if (function.id != function_id or !validId(function.entry_block, program.blocks.len) or
        !blockListed(function.blocks, function.entry_block)) return null;

    var hasher = Sha256.init(.{});
    updateU64(&hasher, 0x6c69667465722d63);
    updateU64(&hasher, @intCast(function_id.index()));
    updateU64(&hasher, @intCast(function.entry_block.index()));
    updateU64(&hasher, @intCast(function.blocks.len));
    for (function.blocks) |block_id| {
        if (!validId(block_id, program.blocks.len)) return null;
        const block = program.blocks[block_id.index()];
        if (block.id != block_id or block.function != function_id) return null;
        updateU64(&hasher, @intCast(block_id.index()));
        const outgoing = terminatorSuccessors(block.terminator);
        updateU64(&hasher, @intCast(outgoing.len));
        for (outgoing.slice()) |target| {
            if (!validId(target, program.blocks.len) or
                program.blocks[target.index()].function != function_id or
                !blockListed(function.blocks, target)) return null;
            updateU64(&hasher, @intCast(target.index()));
        }
    }
    var fingerprint: CfgFingerprint = undefined;
    hasher.final(&fingerprint);
    return fingerprint;
}

pub fn isMovable(program: *const ir.Program, projection: anytype) bool {
    if (!validId(projection.producer, program.instructions.len) or projection.blocks.len == 0) return false;
    const producer = program.instructions[projection.producer.index()];
    if (producer.id != projection.producer or projection.blocks[0] != producer.block) return false;
    const consumer_block = switch (projection.consumer) {
        .instruction => |instruction_id| blk: {
            if (!validId(instruction_id, program.instructions.len)) return false;
            const instruction = program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id or !validId(instruction.block, program.blocks.len) or
                instructionPosition(program.blocks[instruction.block.index()], instruction_id) == null) return false;
            break :blk instruction.block;
        },
        .terminator => |block_id| blk: {
            if (!validId(block_id, program.blocks.len)) return false;
            break :blk block_id;
        },
    };
    if (projection.blocks[projection.blocks.len - 1] != consumer_block or
        !validId(producer.block, program.blocks.len)) return false;
    const function_id = program.blocks[producer.block.index()].function;
    if (!endpointsMatchProgram(program, projection, producer, consumer_block, function_id)) return false;
    const current_fingerprint = cfgFingerprint(program, function_id) orelse return false;
    if (!std.mem.eql(u8, &projection.cfg_fingerprint, &current_fingerprint)) return false;
    for (projection.blocks) |block_id| {
        if (!validId(block_id, program.blocks.len) or
            program.blocks[block_id.index()].function != function_id) return false;
    }
    if (!movedEdgesMatchProgram(program, projection)) return false;
    for (projection.reentry_blocks) |block_id| {
        if (!validId(block_id, program.blocks.len) or
            program.blocks[block_id.index()].function != function_id or
            blockListed(projection.blocks, block_id)) return false;
    }
    switch (projection.reentry) {
        .none => if (projection.reentry_blocks.len != 0 or
            projection.reentry_edges.len != 0 or projection.exit_edges.len != 0) return false,
        .direct_backedge => if (projection.reentry_blocks.len != 0 or projection.reentry_edges.len == 0) return false,
        .indirect_region => if (projection.reentry_blocks.len == 0 or projection.reentry_edges.len == 0) return false,
    }
    var has_producer_entry = false;
    for (projection.reentry_edges) |edge| {
        if (!validId(edge.source, program.blocks.len) or !validId(edge.target, program.blocks.len)) return false;
        if (edge.source != consumer_block and !blockListed(projection.reentry_blocks, edge.source)) return false;
        if (edge.target != producer.block and !blockListed(projection.reentry_blocks, edge.target)) return false;
        if (edge.target == producer.block) has_producer_entry = true;
    }
    if (projection.reentry != .none and !has_producer_entry) return false;
    if (!reentryBlocksMatchWitness(projection, consumer_block, producer.block)) return false;
    for (projection.exit_edges) |edge| {
        if (!validId(edge.source, program.blocks.len) or !validId(edge.target, program.blocks.len)) return false;
        if (edge.source != consumer_block and !blockListed(projection.reentry_blocks, edge.source)) return false;
        if (program.blocks[edge.target.index()].function != function_id or
            blockListed(projection.blocks, edge.target) or
            blockListed(projection.reentry_blocks, edge.target)) return false;
    }
    if (projection.reentry != .none and !reentryEdgesMatchProgram(program, projection, consumer_block)) return false;
    if (!gapsMatchProgram(program, projection)) return false;
    for (projection.gaps) |gap_id| {
        if (!validId(gap_id, program.instructions.len)) return false;
        const gap = program.instructions[gap_id.index()];
        if (gap.id != gap_id or !blockListed(projection.blocks, gap.block) or !invocationGapIsMovable(program, gap)) return false;
    }
    return true;
}

pub fn gapIsMovable(instruction: ir.Instruction) bool {
    return instruction.operation != .make_closure and isExactPure(instruction.effects);
}

/// A gap an open invocation may move past: an exact-pure instruction, or an
/// exact read of a frame-local place, which the invoked code cannot write
/// because no closure binds the place and no repeated-call counter mutates it.
pub fn invocationGapIsMovable(program: *const ir.Program, instruction: ir.Instruction) bool {
    if (gapIsMovable(instruction)) return true;
    const place_id = switch (instruction.operation) {
        .place_read => |read_place| read_place,
        else => return false,
    };
    if (!std.meta.eql(instruction.effects, ir.EffectSummary.place_read) or
        !validId(instruction.block, program.blocks.len)) return false;
    return placeIsFrameLocal(program, place_id, program.blocks[instruction.block.index()].function);
}

fn placeIsFrameLocal(program: *const ir.Program, place_id: ir.PlaceId, function_id: ir.FunctionId) bool {
    if (!validId(place_id, program.places.len) or !validId(function_id, program.functions.len)) return false;
    const place = program.places[place_id.index()];
    if (place.id != place_id or place.origin != .local or place.function != function_id) return false;
    var listed: usize = 0;
    for (program.functions[function_id.index()].local_places) |local_place| {
        if (local_place == place_id) listed += 1;
    }
    if (listed != 1) return false;
    for (program.instructions) |candidate| switch (candidate.operation) {
        .make_closure => |closure| for (closure.bindings) |binding| switch (binding) {
            .value => {},
            .place => |bound| if (bound == place_id) return false,
        },
        .call_repeated_table_get => |call| if (call.counter) |counter| {
            if (counter == place_id) return false;
        },
        else => {},
    };
    return true;
}

fn endpointsMatchProgram(
    program: *const ir.Program,
    projection: anytype,
    producer: ir.Instruction,
    consumer_block: ir.BlockId,
    function_id: ir.FunctionId,
) bool {
    if (!validId(projection.pack, program.value_packs.len) or
        producer.pack_result == null or producer.pack_result.? != projection.pack or
        producer.results.len != 0 or !isVariadicInvocation(producer.operation)) return false;
    const pack = program.value_packs[projection.pack.index()];
    if (pack.id != projection.pack or pack.function != function_id) return false;
    switch (pack.origin) {
        .instruction_result => |instruction_id| if (instruction_id != producer.id) return false,
        .varargs => return false,
    }

    return switch (projection.consumer) {
        .instruction => |instruction_id| instructionConsumesPack(
            program.instructions[instruction_id.index()],
            projection.pack,
            projection.blocks.len,
            projection.gaps.len,
        ),
        .terminator => returnedPack(program.blocks[consumer_block.index()].terminator) == projection.pack,
    };
}

fn instructionConsumesPack(instruction: ir.Instruction, pack_id: ir.ValuePackId, block_count: usize, gap_count: usize) bool {
    return switch (instruction.operation) {
        .adjust_pack => |consumed| consumed == pack_id and instruction.pack_result == null and
            isExactPure(instruction.effects) and block_count == 1 and gap_count == 0,
        .make_table_literal => |constructor| constructor.tail_pack == pack_id and
            instruction.pack_result == null and instruction.results.len == 1,
        .table_set_pack => |operation| operation.pack == pack_id and
            instruction.pack_result == null and instruction.results.len == 0,
        else => invocationArgumentPack(instruction.operation) == pack_id,
    };
}

fn invocationArgumentPack(operation: ir.Operation) ?ir.ValuePackId {
    return switch (operation) {
        .call => |value| value.argument_pack,
        .namecall => |value| value.argument_pack,
        .protected_call => |value| value.argument_pack,
        .coroutine_resume => |value| value.argument_pack,
        .coroutine_yield => |value| value.argument_pack,
        else => null,
    };
}

fn isVariadicInvocation(operation: ir.Operation) bool {
    const arity: ir.ResultArity = switch (operation) {
        .call => |value| value.result_arity,
        .namecall => |value| value.result_arity,
        .protected_call => |value| value.result_arity,
        .coroutine_resume => |value| value.result_arity,
        .coroutine_yield => |value| value.result_arity,
        else => return false,
    };
    return arity == .variadic;
}

fn returnedPack(terminator: ir.Terminator) ?ir.ValuePackId {
    return switch (terminator) {
        .return_pack => |pack_id| pack_id,
        .return_expanded => |expanded| expanded.pack,
        else => null,
    };
}

fn gapsMatchProgram(program: *const ir.Program, projection: anytype) bool {
    const producer = program.instructions[projection.producer.index()];
    const producer_block = program.blocks[producer.block.index()];
    const producer_position = instructionPosition(producer_block, producer.id) orelse return false;
    const consumer_block_id = projection.blocks[projection.blocks.len - 1];
    const consumer_block = program.blocks[consumer_block_id.index()];
    const consumer_position = switch (projection.consumer) {
        .instruction => |instruction_id| instructionPosition(consumer_block, instruction_id) orelse return false,
        .terminator => consumer_block.instructions.len,
    };

    var gap_index: usize = 0;
    for (projection.blocks, 0..) |block_id, block_index| {
        for (projection.blocks[0..block_index]) |earlier| if (earlier == block_id) return false;
        const block = program.blocks[block_id.index()];
        const start = if (block_index == 0) producer_position + 1 else 0;
        const end = if (block_index + 1 == projection.blocks.len) consumer_position else block.instructions.len;
        if (start > end) return false;
        for (block.instructions[start..end]) |instruction_id| {
            if (!validId(instruction_id, program.instructions.len)) return false;
            const instruction = program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id or instruction.block != block_id or
                gap_index == projection.gaps.len or projection.gaps[gap_index] != instruction_id) return false;
            gap_index += 1;
        }
    }
    return gap_index == projection.gaps.len;
}

fn movedEdgesMatchProgram(program: *const ir.Program, projection: anytype) bool {
    if (projection.blocks.len == 1) return projection.moved_edges.len == 0;
    for (projection.moved_edges) |edge| {
        if (!validId(edge.source, program.blocks.len) or !validId(edge.target, program.blocks.len)) return false;
        const source_index = blockPosition(projection.blocks, edge.source) orelse return false;
        const target_index = blockPosition(projection.blocks, edge.target) orelse return false;
        if (source_index + 1 >= projection.blocks.len or source_index >= target_index) return false;
    }
    for (projection.blocks[1..]) |block_id| {
        var has_incoming = false;
        for (projection.moved_edges) |edge| if (edge.target == block_id) {
            has_incoming = true;
            break;
        };
        if (!has_incoming) return false;
    }
    for (projection.blocks[0 .. projection.blocks.len - 1]) |block_id| {
        if (!movedSourceEdgesMatchProgram(program, projection, block_id)) return false;
    }
    return true;
}

fn movedSourceEdgesMatchProgram(program: *const ir.Program, projection: anytype, source: ir.BlockId) bool {
    const outgoing = terminatorSuccessors(program.blocks[source.index()].terminator);
    var recorded_count: usize = 0;
    for (projection.moved_edges) |edge| if (edge.source == source) {
        if (recorded_count == outgoing.len) return false;
        recorded_count += 1;
    };
    if (recorded_count != outgoing.len) return false;

    for (outgoing.slice()) |target| {
        var actual_multiplicity: usize = 0;
        for (outgoing.slice()) |candidate| if (candidate == target) {
            actual_multiplicity += 1;
        };
        var recorded_multiplicity: usize = 0;
        for (projection.moved_edges) |edge| if (edge.source == source and edge.target == target) {
            recorded_multiplicity += 1;
        };
        if (recorded_multiplicity != actual_multiplicity) return false;
    }
    return true;
}

fn reentryEdgesMatchProgram(program: *const ir.Program, projection: anytype, consumer_block: ir.BlockId) bool {
    if (!sourceEdgesMatchProgram(program, projection, consumer_block)) return false;
    for (projection.reentry_blocks) |block_id| {
        if (!sourceEdgesMatchProgram(program, projection, block_id)) return false;
    }
    return true;
}

fn reentryBlocksMatchWitness(projection: anytype, consumer_block: ir.BlockId, producer_block: ir.BlockId) bool {
    for (projection.reentry_blocks, 0..) |block_id, block_index| {
        for (projection.reentry_blocks[0..block_index]) |earlier| if (earlier == block_id) return false;
        var has_incoming = false;
        var has_continuation = false;
        for (projection.reentry_edges) |edge| {
            if (edge.target == block_id) {
                if (edge.source != consumer_block) {
                    const source_index = blockPosition(projection.reentry_blocks, edge.source) orelse return false;
                    if (source_index >= block_index) return false;
                }
                has_incoming = true;
            }
            if (edge.source == block_id) {
                if (edge.target != producer_block) {
                    const target_index = blockPosition(projection.reentry_blocks, edge.target) orelse return false;
                    if (target_index <= block_index) return false;
                }
                has_continuation = true;
            }
        }
        if (!has_incoming or !has_continuation) return false;
    }
    return true;
}

fn sourceEdgesMatchProgram(program: *const ir.Program, projection: anytype, source: ir.BlockId) bool {
    if (!validId(source, program.blocks.len)) return false;
    const outgoing = terminatorSuccessors(program.blocks[source.index()].terminator);
    var recorded_count: usize = 0;
    for (projection.reentry_edges) |edge| if (edge.source == source) {
        if (recorded_count == outgoing.len) return false;
        recorded_count += 1;
    };
    for (projection.exit_edges) |edge| if (edge.source == source) {
        if (recorded_count == outgoing.len) return false;
        recorded_count += 1;
    };
    if (recorded_count != outgoing.len) return false;

    for (outgoing.slice()) |target| {
        var actual_multiplicity: usize = 0;
        for (outgoing.slice()) |candidate| if (candidate == target) {
            actual_multiplicity += 1;
        };
        var recorded_multiplicity: usize = 0;
        for (projection.reentry_edges) |edge| if (edge.source == source and edge.target == target) {
            recorded_multiplicity += 1;
        };
        for (projection.exit_edges) |edge| if (edge.source == source and edge.target == target) {
            recorded_multiplicity += 1;
        };
        if (recorded_multiplicity != actual_multiplicity) return false;
    }
    return true;
}

const TerminatorSuccessors = struct {
    ids: [2]ir.BlockId = undefined,
    len: u2 = 0,

    fn slice(self: *const TerminatorSuccessors) []const ir.BlockId {
        return self.ids[0..self.len];
    }
};

fn terminatorSuccessors(terminator: ir.Terminator) TerminatorSuccessors {
    var result: TerminatorSuccessors = .{};
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

fn instructionPosition(block: ir.Block, instruction_id: ir.InstructionId) ?usize {
    var position: ?usize = null;
    for (block.instructions, 0..) |listed_id, index| {
        if (listed_id != instruction_id) continue;
        if (position != null) return null;
        position = index;
    }
    return position;
}

fn blockListed(blocks: []const ir.BlockId, block_id: ir.BlockId) bool {
    for (blocks) |listed| if (listed == block_id) return true;
    return false;
}

fn blockPosition(blocks: []const ir.BlockId, block_id: ir.BlockId) ?usize {
    var position: ?usize = null;
    for (blocks, 0..) |listed, index| {
        if (listed != block_id) continue;
        if (position != null) return null;
        position = index;
    }
    return position;
}

fn isExactPure(effects: ir.EffectSummary) bool {
    return effects.precision == .exact and
        !effects.reads_memory and
        !effects.writes_memory and
        !effects.may_throw and
        !effects.may_yield and
        !effects.invokes_unknown_code;
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}

fn updateU64(hasher: *Sha256, value: u64) void {
    var bytes: [8]u8 = undefined;
    for (&bytes, 0..) |*byte, index| byte.* = @truncate(value >> @intCast(index * 8));
    hasher.update(&bytes);
}
