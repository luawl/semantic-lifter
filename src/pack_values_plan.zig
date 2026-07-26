const ir = @import("ir.zig");
const normalized_value = @import("normalized_value.zig");

pub const Consumer = union(enum) {
    adjustment: ir.InstructionId,
    table_tail: ir.InstructionId,
    invocation_argument: ir.InstructionId,
    returned: ir.BlockId,
};

pub fn consumer(
    program: *const ir.Program,
    producer: ir.Instruction,
    use_counts: []const u32,
    adjustment_consumers: []const ?ir.InstructionId,
    table_consumers: []const ?ir.InstructionId,
    invocation_argument_consumers: []const ?ir.InstructionId,
    return_consumers: []const ?ir.BlockId,
) ?Consumer {
    if (producer.results.len != 0 or !normalized_value.isExactPure(producer.effects)) return null;
    const packed_values = switch (producer.operation) {
        .pack_values => |values| values,
        else => return null,
    };
    if (packed_values.len == 0) return null;
    const pack_id = producer.pack_result orelse return null;
    if (!validId(pack_id, program.value_packs.len) or
        pack_id.index() >= use_counts.len or
        use_counts[pack_id.index()] != 1) return null;
    const pack = program.value_packs[pack_id.index()];
    const origin_matches = switch (pack.origin) {
        .instruction_result => |instruction_id| instruction_id == producer.id,
        else => false,
    };
    if (!origin_matches or
        !validId(producer.block, program.blocks.len) or
        program.blocks[producer.block.index()].function != pack.function) return null;

    if (optionalAt(ir.InstructionId, adjustment_consumers, pack_id.index())) |consumer_id| {
        if (!validId(consumer_id, program.instructions.len)) return null;
        const adjustment = program.instructions[consumer_id.index()];
        const consumed_pack = switch (adjustment.operation) {
            .adjust_pack => |value| value,
            else => return null,
        };
        if (consumed_pack != pack_id or
            adjustment.pack_result != null or
            !normalized_value.isExactPure(adjustment.effects) or
            !sameFunction(program, producer, adjustment, pack.function) or
            !orderedInstructionConsumer(program, producer, adjustment)) return null;
        return .{ .adjustment = consumer_id };
    }

    if (optionalAt(ir.InstructionId, table_consumers, pack_id.index())) |consumer_id| {
        if (!validId(consumer_id, program.instructions.len)) return null;
        const table = program.instructions[consumer_id.index()];
        const consumed_pack = switch (table.operation) {
            .make_table_literal => |constructor| constructor.tail_pack,
            .table_set_pack => |operation| operation.pack,
            else => null,
        };
        if (consumed_pack == null or
            consumed_pack.? != pack_id or
            table.pack_result != null or
            !validTableConsumerResults(table) or
            !sameFunction(program, producer, table, pack.function) or
            !orderedInstructionConsumer(program, producer, table)) return null;
        return .{ .table_tail = consumer_id };
    }

    if (optionalAt(ir.InstructionId, invocation_argument_consumers, pack_id.index())) |consumer_id| {
        if (!validId(consumer_id, program.instructions.len)) return null;
        const invocation = program.instructions[consumer_id.index()];
        if (invocationArgumentPack(invocation.operation) != pack_id or
            !sameFunction(program, producer, invocation, pack.function) or
            !orderedInstructionConsumer(program, producer, invocation)) return null;
        return .{ .invocation_argument = consumer_id };
    }

    const return_block_id = optionalAt(ir.BlockId, return_consumers, pack_id.index()) orelse return null;
    if (!validId(return_block_id, program.blocks.len)) return null;
    const return_block = program.blocks[return_block_id.index()];
    if (returnedPack(return_block.terminator) != pack_id or
        return_block.function != pack.function or
        (producer.block == return_block_id and !blockListsInstruction(return_block, producer.id))) return null;
    return .{ .returned = return_block_id };
}

fn validTableConsumerResults(instruction: ir.Instruction) bool {
    return switch (instruction.operation) {
        .make_table_literal => instruction.results.len == 1,
        .table_set_pack => instruction.results.len == 0,
        else => false,
    };
}

fn optionalAt(comptime Id: type, values: []const ?Id, index: usize) ?Id {
    if (index >= values.len) return null;
    return values[index];
}

fn sameFunction(program: *const ir.Program, producer: ir.Instruction, consumer_instruction: ir.Instruction, pack_function: ir.FunctionId) bool {
    if (!validId(producer.block, program.blocks.len) or !validId(consumer_instruction.block, program.blocks.len)) return false;
    return program.blocks[producer.block.index()].function == pack_function and
        program.blocks[consumer_instruction.block.index()].function == pack_function;
}

fn precedesInSameBlock(program: *const ir.Program, producer: ir.Instruction, consumer_instruction: ir.Instruction) bool {
    if (producer.block != consumer_instruction.block or !validId(producer.block, program.blocks.len)) return false;
    var producer_position: ?usize = null;
    var consumer_position: ?usize = null;
    for (program.blocks[producer.block.index()].instructions, 0..) |instruction_id, index| {
        if (instruction_id == producer.id) {
            if (producer_position != null) return false;
            producer_position = index;
        }
        if (instruction_id == consumer_instruction.id) {
            if (consumer_position != null) return false;
            consumer_position = index;
        }
    }
    return producer_position != null and consumer_position != null and producer_position.? < consumer_position.?;
}

fn orderedInstructionConsumer(program: *const ir.Program, producer: ir.Instruction, consumer_instruction: ir.Instruction) bool {
    return producer.block != consumer_instruction.block or precedesInSameBlock(program, producer, consumer_instruction);
}

fn blockListsInstruction(block: ir.Block, instruction_id: ir.InstructionId) bool {
    var found = false;
    for (block.instructions) |listed_id| {
        if (listed_id != instruction_id) continue;
        if (found) return false;
        found = true;
    }
    return found;
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

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}
