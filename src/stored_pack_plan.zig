const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const readable_scope = @import("readable_scope.zig");
const pack_closure_safety = @import("pack_closure_safety.zig");

pub const Use = union(enum) {
    adjustment: ir.InstructionId,
    tail: ir.InstructionId,
    returned: ir.BlockId,
};

pub const Match = struct {
    allocator: std.mem.Allocator,
    uses: []Use,

    pub fn deinit(self: *Match) void {
        self.allocator.free(self.uses);
        self.* = undefined;
    }
};

pub fn safeUsesAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    producer: ir.Instruction,
    pack_id: ir.ValuePackId,
    expected_use_count: u32,
) !?Match {
    if (expected_use_count == 0 or
        !scope.instruction(producer.id) or
        producer.pack_result == null or producer.pack_result.? != pack_id or
        !validId(pack_id, program.value_packs.len) or
        !validId(producer.block, program.blocks.len)) return null;

    const pack = program.value_packs[pack_id.index()];
    const origin_matches = switch (pack.origin) {
        .instruction_result => |instruction_id| instruction_id == producer.id,
        .varargs => false,
    };
    const producer_block = program.blocks[producer.block.index()];
    if (!origin_matches or pack.shape.tail != .open or
        producer_block.function != pack.function or
        !validId(pack.function, program.functions.len) or
        instructionPosition(producer_block, producer.id) == null) return null;

    var analysis = cfg.Analysis.init(allocator, program, program.functions[pack.function.index()]) catch |err| switch (err) {
        error.InvalidCfg => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    if (!analysis.isReachable(producer.block)) return null;

    var uses: std.ArrayList(Use) = .empty;
    defer uses.deinit(allocator);
    var tail_count: usize = 0;
    var has_reentry = try pack_closure_safety.blockHasReachableReentry(&analysis, producer.block);

    for (program.instructions) |instruction| {
        if (!scope.instruction(instruction.id)) continue;
        const use = instructionUse(instruction, pack_id) orelse continue;
        if (!validId(instruction.id, program.instructions.len) or
            !validId(instruction.block, program.blocks.len) or
            program.blocks[instruction.block.index()].function != pack.function or
            !analysis.isReachable(instruction.block) or
            !producerPrecedesUse(program, &analysis, producer, instruction.block, instruction.id)) return null;
        has_reentry = has_reentry or try pack_closure_safety.blockHasReachableReentry(&analysis, instruction.block);
        switch (use) {
            .adjustment => if (instruction.pack_result != null or !isExactPure(instruction.effects)) return null,
            .tail => {
                if (!tailShapeIsValid(instruction)) return null;
                tail_count = std.math.add(usize, tail_count, 1) catch return null;
            },
            .returned => unreachable,
        }
        try uses.append(allocator, use);
    }

    for (program.blocks) |block| {
        if (!scope.block(block.id) or returnedPack(block.terminator) != pack_id) continue;
        if (block.function != pack.function or
            !analysis.isReachable(block.id) or
            !producerPrecedesUse(program, &analysis, producer, block.id, null)) return null;
        has_reentry = has_reentry or try pack_closure_safety.blockHasReachableReentry(&analysis, block.id);
        try uses.append(allocator, .{ .returned = block.id });
    }

    if (tail_count == 0 or uses.items.len != @as(usize, @intCast(expected_use_count))) return null;
    if (has_reentry and !directGuardedTailIsSafe(program, scope, &analysis, producer, uses.items)) return null;
    return .{
        .allocator = allocator,
        .uses = try uses.toOwnedSlice(allocator),
    };
}

fn directGuardedTailIsSafe(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    analysis: *const cfg.Analysis,
    producer: ir.Instruction,
    uses: []const Use,
) bool {
    if (uses.len != 1 or !validId(producer.block, program.blocks.len)) return false;
    const consumer_id = switch (uses[0]) {
        .tail => |instruction_id| instruction_id,
        else => return false,
    };
    if (!validId(consumer_id, program.instructions.len)) return false;
    const consumer = program.instructions[consumer_id.index()];
    if (!scope.instruction(consumer.id) or
        !validId(consumer.block, program.blocks.len) or
        consumer.block == producer.block) return false;

    const producer_block = program.blocks[producer.block.index()];
    const consumer_block = program.blocks[consumer.block.index()];
    if (consumer_block.function != producer_block.function or
        !validId(producer_block.function, program.functions.len) or
        program.functions[producer_block.function.index()].entry_block == consumer.block) return false;
    const direct_target = switch (producer_block.terminator) {
        .jump => |edge| edge.target,
        else => return false,
    };
    return direct_target == consumer.block and
        analysis.predecessorCount(consumer.block) == 1 and
        analysis.predecessorAt(consumer.block, 0) == producer.block;
}

fn instructionUse(instruction: ir.Instruction, pack_id: ir.ValuePackId) ?Use {
    switch (instruction.operation) {
        .adjust_pack => |candidate| if (candidate == pack_id) return .{ .adjustment = instruction.id },
        .make_table_literal => |constructor| if (constructor.tail_pack == pack_id) return .{ .tail = instruction.id },
        .table_set_pack => |operation| if (operation.pack == pack_id) return .{ .tail = instruction.id },
        else => {},
    }
    if (invocationArgumentPack(instruction.operation) == pack_id) return .{ .tail = instruction.id };
    return null;
}

fn tailShapeIsValid(instruction: ir.Instruction) bool {
    return switch (instruction.operation) {
        .make_table_literal => instruction.pack_result == null and instruction.results.len == 1,
        .table_set_pack => instruction.pack_result == null and instruction.results.len == 0,
        .call, .namecall, .protected_call, .coroutine_resume, .coroutine_yield => true,
        else => false,
    };
}

fn producerPrecedesUse(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    producer: ir.Instruction,
    use_block: ir.BlockId,
    use_instruction: ?ir.InstructionId,
) bool {
    if (use_block != producer.block) return analysis.dominates(producer.block, use_block);
    const block = program.blocks[producer.block.index()];
    const producer_position = instructionPosition(block, producer.id) orelse return false;
    const instruction_id = use_instruction orelse return true;
    const use_position = instructionPosition(block, instruction_id) orelse return false;
    return producer_position < use_position;
}

fn instructionPosition(block: ir.Block, instruction_id: ir.InstructionId) ?usize {
    for (block.instructions, 0..) |candidate, index| if (candidate == instruction_id) return index;
    return null;
}

fn returnedPack(terminator: ir.Terminator) ?ir.ValuePackId {
    return switch (terminator) {
        .return_pack => |pack_id| pack_id,
        .return_expanded => |expanded| expanded.pack,
        else => null,
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
