const std = @import("std");
const ir = @import("ir.zig");
const pack_plan = @import("pack_plan.zig");
const dead_code = @import("dead_code.zig");
const place_write_fusion = @import("place_write_fusion.zig");
const place_read_fusion = @import("place_read_fusion.zig");
const compound_update = @import("compound_update.zig");
const luau_runtime = @import("luau_runtime.zig");
const runtime_uses = @import("runtime_uses.zig");

pub const Consumer = union(enum) {
    instruction: ir.InstructionId,
    terminator: ir.BlockId,
};

pub const Plan = struct {
    allocator: std.mem.Allocator,
    consumers: []?Consumer,

    pub fn init(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        packs: *const pack_plan.Plan,
        dead: *const dead_code.Plan,
        place_writes: *const place_write_fusion.Plan,
        place_reads: *const place_read_fusion.Plan,
    ) !Plan {
        const consumers = try allocator.alloc(?Consumer, program.instructions.len);
        errdefer allocator.free(consumers);
        @memset(consumers, null);

        var uses = try dead.semanticUseCounts(allocator, program);
        defer uses.deinit();

        for (program.blocks) |block| {
            var index = block.instructions.len;
            while (index != 0) {
                index -= 1;
                const producer_id = block.instructions[index];
                if (!validId(producer_id, program.instructions.len)) continue;
                const producer = program.instructions[producer_id.index()];
                const result_id = producerResult(program, packs, dead, place_writes, place_reads, producer) orelse continue;
                if (result_id.index() >= uses.values.len or uses.values[result_id.index()] != 1) continue;

                var cursor = index + 1;
                while (cursor < block.instructions.len) : (cursor += 1) {
                    const consumer_id = block.instructions[cursor];
                    if (!validId(consumer_id, program.instructions.len)) break;
                    const consumer_instruction = program.instructions[consumer_id.index()];
                    if (consumer_instruction.block != block.id) break;
                    if (dead.operationUsesValue(consumer_instruction.operation, result_id)) {
                        if (!dead.contains(consumer_id) and
                            orderedGapsFollowValue(
                                program,
                                packs,
                                dead,
                                place_writes,
                                place_reads,
                                consumers,
                                producer,
                                block.instructions[index + 1 .. cursor],
                                .{ .instruction = consumer_id },
                                result_id,
                            ) and
                            projectedConsumerGapsAllowValueFusion(program, packs, consumer_instruction) and
                            fusionChainHasCapacity(consumers, .{ .instruction = consumer_id }) and
                            instructionConsumerAllows(dead, consumer_instruction.operation, result_id))
                        {
                            consumers[producer_id.index()] = .{ .instruction = consumer_id };
                        }
                        break;
                    }
                    if (canCrossGap(consumer_instruction)) continue;
                    if (!gapIsScheduled(program, packs, dead, place_writes, place_reads, consumers, consumer_instruction)) break;
                }
                if (cursor == block.instructions.len and
                    terminatorConsumerAllows(dead, block.terminator, result_id) and
                    orderedGapsFollowValue(
                        program,
                        packs,
                        dead,
                        place_writes,
                        place_reads,
                        consumers,
                        producer,
                        block.instructions[index + 1 ..],
                        .{ .terminator = block.id },
                        result_id,
                    ))
                {
                    consumers[producer_id.index()] = .{ .terminator = block.id };
                }
            }
        }

        return .{ .allocator = allocator, .consumers = consumers };
    }

    pub fn deinit(self: *Plan) void {
        self.allocator.free(self.consumers);
        self.* = undefined;
    }

    pub fn consumer(self: *const Plan, producer_id: ir.InstructionId) ?Consumer {
        if (!validId(producer_id, self.consumers.len)) return null;
        return self.consumers[producer_id.index()];
    }

    pub fn contains(self: *const Plan, producer_id: ir.InstructionId) bool {
        return self.consumer(producer_id) != null;
    }
};

fn producerResult(
    program: *const ir.Program,
    packs: *const pack_plan.Plan,
    dead: *const dead_code.Plan,
    place_writes: *const place_write_fusion.Plan,
    place_reads: *const place_read_fusion.Plan,
    producer: ir.Instruction,
) ?ir.ValueId {
    if (dead.contains(producer.id) or place_writes.consumerForProducer(producer.id) != null or place_reads.contains(producer.id)) return null;
    if (producer.results.len != 1 or producer.pack_result != null or !operationRendersAsExpression(producer.operation, packs.role(producer.id))) return null;
    const result_id = producer.results[0];
    if (!validId(result_id, program.values.len)) return null;
    const origin_matches = switch (program.values[result_id.index()].origin) {
        .instruction_result => |origin| origin.instruction == producer.id and origin.index == 0,
        else => false,
    };
    return if (origin_matches) result_id else null;
}

fn operationRendersAsExpression(operation: ir.Operation, role: pack_plan.InstructionRole) bool {
    return switch (role) {
        .ordinary => switch (operation) {
            .constant, .copy, .unary, .binary, .environment_get, .table_get, .make_table, .make_table_literal, .string_interpolate, .function_ref => true,
            .call => |value| isSingleResult(value.result_arity),
            .namecall => |value| isSingleResult(value.result_arity),
            .protected_call => |value| isSingleResult(value.result_arity),
            .coroutine_create => true,
            .coroutine_resume => |value| isSingleResult(value.result_arity),
            .coroutine_yield => |value| isSingleResult(value.result_arity),
            else => false,
        },
        .fused_adjustment => operation == .adjust_pack,
        else => false,
    };
}

fn instructionConsumerAllows(dead: *const dead_code.Plan, operation: ir.Operation, result_id: ir.ValueId) bool {
    switch (operation) {
        .place_write, .numeric_for_next, .generic_for_next => return false,
        .binary => |binary| switch (binary.operator) {
            .logical_and, .logical_or => if (dead.resolveValue(binary.right) == result_id) return false,
            else => {},
        },
        else => {},
    }
    return dead.operationUsesValue(operation, result_id);
}

fn canCrossGap(instruction: ir.Instruction) bool {
    return pack_plan.projectionGapIsMovable(instruction);
}

fn projectedConsumerGapsAllowValueFusion(program: *const ir.Program, packs: *const pack_plan.Plan, consumer: ir.Instruction) bool {
    switch (packs.role(consumer.id)) {
        .materialized_pack_values_producer => return false,
        .fused_pack_values_producer, .fused_pack_values_return_producer => {
            const gaps = (packs.packValuesProjection(program, consumer.id) orelse return false).gaps;
            for (gaps) |gap_id| {
                if (!validId(gap_id, program.instructions.len) or
                    !pack_plan.projectionGapIsMovable(program.instructions[gap_id.index()])) return false;
            }
            return true;
        },
        .fused_invocation_producer, .fused_return_producer => {
            const projection = packs.invocationProjection(program, consumer.id) orelse return false;
            return pack_plan.invocationProjectionIsMovable(program, projection);
        },
        else => return true,
    }
}

fn consumersMatch(left: Consumer, right: Consumer) bool {
    return switch (left) {
        .instruction => |left_id| switch (right) {
            .instruction => |right_id| left_id == right_id,
            .terminator => false,
        },
        .terminator => |left_id| switch (right) {
            .instruction => false,
            .terminator => |right_id| left_id == right_id,
        },
    };
}

fn fusionChainHasCapacity(consumers: []const ?Consumer, first_consumer: Consumer) bool {
    var current = first_consumer;
    var depth: usize = 0;
    var remaining = consumers.len + 1;
    while (remaining != 0) : (remaining -= 1) {
        switch (current) {
            .terminator => return true,
            .instruction => |instruction_id| {
                depth += 1;
                if (depth >= luau_runtime.max_fused_expression_operations) return false;
                if (!validId(instruction_id, consumers.len)) return false;
                current = consumers[instruction_id.index()] orelse return true;
            },
        }
    }
    return false;
}

const FusedPackGap = struct {
    pack: ir.ValuePackId,
    consumer: Consumer,
};

fn fusedPackGap(program: *const ir.Program, packs: *const pack_plan.Plan, instruction: ir.Instruction) ?FusedPackGap {
    const pack = instruction.pack_result orelse return null;
    if (!validId(pack, program.value_packs.len)) return null;
    const consumer: Consumer = switch (packs.role(instruction.id)) {
        .fused_invocation_producer => |instruction_id| .{ .instruction = instruction_id },
        .fused_return_producer => |block_id| .{ .terminator = block_id },
        else => return null,
    };
    return .{ .pack = pack, .consumer = consumer };
}

fn fusedReadResult(
    program: *const ir.Program,
    place_reads: *const place_read_fusion.Plan,
    instruction: ir.Instruction,
) ?ir.ValueId {
    if (!place_reads.contains(instruction.id) or instruction.operation != .place_read or instruction.results.len != 1 or instruction.pack_result != null) return null;
    const result_id = instruction.results[0];
    if (!validId(result_id, program.values.len)) return null;
    const origin_matches = switch (program.values[result_id.index()].origin) {
        .instruction_result => |origin| origin.instruction == instruction.id and origin.index == 0,
        else => false,
    };
    return if (origin_matches) result_id else null;
}

const OrderedOperand = union(enum) {
    value: ir.ValueId,
    pack: ir.ValuePackId,
};

const ScheduledGap = struct {
    operand: OrderedOperand,
    consumer: Consumer,
};

fn gapIsScheduled(
    program: *const ir.Program,
    packs: *const pack_plan.Plan,
    dead: *const dead_code.Plan,
    place_writes: *const place_write_fusion.Plan,
    place_reads: *const place_read_fusion.Plan,
    consumers: []const ?Consumer,
    instruction: ir.Instruction,
) bool {
    return initialScheduledGap(program, packs, dead, place_writes, place_reads, consumers, instruction) != null;
}

fn initialScheduledGap(
    program: *const ir.Program,
    packs: *const pack_plan.Plan,
    dead: *const dead_code.Plan,
    place_writes: *const place_write_fusion.Plan,
    place_reads: *const place_read_fusion.Plan,
    consumers: []const ?Consumer,
    instruction: ir.Instruction,
) ?ScheduledGap {
    if (fusedReadResult(program, place_reads, instruction)) |result| {
        const consumer: Consumer = switch (place_reads.consumer(instruction.id) orelse return null) {
            .instruction => |instruction_id| .{ .instruction = instruction_id },
            .terminator => |block_id| .{ .terminator = block_id },
        };
        return .{ .operand = .{ .value = result }, .consumer = consumer };
    }
    if (fusedPackGap(program, packs, instruction)) |gap| {
        return .{ .operand = .{ .pack = gap.pack }, .consumer = gap.consumer };
    }
    const result = producerResult(program, packs, dead, place_writes, place_reads, instruction) orelse return null;
    if (!validId(instruction.id, consumers.len)) return null;
    return .{ .operand = .{ .value = result }, .consumer = consumers[instruction.id.index()] orelse return null };
}

fn gapOperandAtConsumer(
    program: *const ir.Program,
    packs: *const pack_plan.Plan,
    dead: *const dead_code.Plan,
    place_writes: *const place_write_fusion.Plan,
    place_reads: *const place_read_fusion.Plan,
    consumers: []const ?Consumer,
    instruction: ir.Instruction,
    target: Consumer,
) ?OrderedOperand {
    var gap = initialScheduledGap(program, packs, dead, place_writes, place_reads, consumers, instruction) orelse return null;
    var remaining = program.instructions.len + 1;
    while (remaining != 0) : (remaining -= 1) {
        if (consumersMatch(gap.consumer, target)) return gap.operand;
        const consumer_id = switch (gap.consumer) {
            .instruction => |instruction_id| instruction_id,
            .terminator => return null,
        };
        if (!validId(consumer_id, program.instructions.len) or !validId(consumer_id, consumers.len)) return null;
        const consumer = program.instructions[consumer_id.index()];
        const result = producerResult(program, packs, dead, place_writes, place_reads, consumer) orelse return null;
        gap = .{
            .operand = .{ .value = result },
            .consumer = consumers[consumer_id.index()] orelse return null,
        };
    }
    return null;
}

fn orderedGapsFollowValue(
    program: *const ir.Program,
    packs: *const pack_plan.Plan,
    dead: *const dead_code.Plan,
    place_writes: *const place_write_fusion.Plan,
    place_reads: *const place_read_fusion.Plan,
    consumers: []const ?Consumer,
    producer: ir.Instruction,
    gaps: []const ir.InstructionId,
    target: Consumer,
    value_id: ir.ValueId,
) bool {
    for (gaps) |instruction_id| {
        if (!validId(instruction_id, program.instructions.len)) return false;
        const instruction = program.instructions[instruction_id.index()];
        if (canCrossGap(instruction)) continue;
        const operand = gapOperandAtConsumer(program, packs, dead, place_writes, place_reads, consumers, instruction, target) orelse return false;
        if (fusedReadResult(program, place_reads, instruction)) |read_result| {
            const consumer = switch (target) {
                .instruction => |consumer_id| if (validId(consumer_id, program.instructions.len))
                    program.instructions[consumer_id.index()]
                else
                    return false,
                .terminator => null,
            };
            if (consumer) |consumer_instruction| {
                if (compound_update.rhsMayInlineAcrossTargetRead(program, dead, place_writes, place_reads, value_id, read_result, consumer_instruction)) continue;
            }
        }
        if (!producerMayFollowOrderedGap(program, producer) and
            !valuePrecedesOrderedOperand(program, dead, target, value_id, operand)) return false;
    }
    return true;
}

fn valuePrecedesOrderedOperand(
    program: *const ir.Program,
    dead: *const dead_code.Plan,
    consumer: Consumer,
    value: ir.ValueId,
    operand: OrderedOperand,
) bool {
    return switch (operand) {
        .value => |other| valuePrecedesConsumer(program, dead, consumer, value, other),
        .pack => |pack| valuePrecedesPackConsumer(program, dead, consumer, value, pack),
    };
}

fn producerMayFollowOrderedGap(program: *const ir.Program, producer: ir.Instruction) bool {
    return switch (producer.operation) {
        .make_table => true,
        .make_table_literal => |constructor| if (constructor.fields.len != 0)
            false
        else if (constructor.tail_pack) |pack_id|
            validId(pack_id, program.value_packs.len) and program.value_packs[pack_id.index()].origin == .varargs
        else
            true,
        else => false,
    };
}

fn valuePrecedes(dead: *const dead_code.Plan, operation: ir.Operation, first: ir.ValueId, second: ir.ValueId) bool {
    var visitor: ValueOrderVisitor = .{ .dead = dead, .first = first, .second = second };
    runtime_uses.visitOperationUses(operation, &visitor);
    return visitor.first_position != null and visitor.second_position != null and visitor.first_position.? < visitor.second_position.?;
}

fn valuePrecedesTerminator(dead: *const dead_code.Plan, terminator: ir.Terminator, first: ir.ValueId, second: ir.ValueId) bool {
    var visitor: ValueOrderVisitor = .{ .dead = dead, .first = first, .second = second };
    runtime_uses.visitTerminatorUses(terminator, &visitor);
    return visitor.first_position != null and visitor.second_position != null and visitor.first_position.? < visitor.second_position.?;
}

fn valuePrecedesConsumer(program: *const ir.Program, dead: *const dead_code.Plan, consumer: Consumer, first: ir.ValueId, second: ir.ValueId) bool {
    return switch (consumer) {
        .instruction => |instruction_id| validId(instruction_id, program.instructions.len) and
            valuePrecedes(dead, program.instructions[instruction_id.index()].operation, first, second),
        .terminator => |block_id| validId(block_id, program.blocks.len) and
            valuePrecedesTerminator(dead, program.blocks[block_id.index()].terminator, first, second),
    };
}

fn valuePrecedesPackConsumer(program: *const ir.Program, dead: *const dead_code.Plan, consumer: Consumer, value: ir.ValueId, pack: ir.ValuePackId) bool {
    var visitor: ValuePackOrderVisitor = .{ .dead = dead, .value_target = value, .pack_target = pack };
    switch (consumer) {
        .instruction => |instruction_id| {
            if (!validId(instruction_id, program.instructions.len)) return false;
            runtime_uses.visitOperationUses(program.instructions[instruction_id.index()].operation, &visitor);
        },
        .terminator => |block_id| {
            if (!validId(block_id, program.blocks.len)) return false;
            runtime_uses.visitTerminatorUses(program.blocks[block_id.index()].terminator, &visitor);
        },
    }
    return visitor.value_position != null and visitor.pack_position != null and visitor.value_position.? < visitor.pack_position.?;
}

const ValuePackOrderVisitor = struct {
    dead: *const dead_code.Plan,
    value_target: ir.ValueId,
    pack_target: ir.ValuePackId,
    position: usize = 0,
    value_position: ?usize = null,
    pack_position: ?usize = null,

    pub fn value(self: *ValuePackOrderVisitor, value_id: ir.ValueId) void {
        if (self.dead.resolveValue(value_id) == self.value_target and self.value_position == null) self.value_position = self.position;
        self.position += 1;
    }

    pub fn pack(self: *ValuePackOrderVisitor, pack_id: ir.ValuePackId) void {
        if (pack_id == self.pack_target and self.pack_position == null) self.pack_position = self.position;
        self.position += 1;
    }

    pub fn place(_: *ValuePackOrderVisitor, _: ir.PlaceId) void {}
};

const ValueOrderVisitor = struct {
    dead: *const dead_code.Plan,
    first: ir.ValueId,
    second: ir.ValueId,
    position: usize = 0,
    first_position: ?usize = null,
    second_position: ?usize = null,

    pub fn value(self: *ValueOrderVisitor, value_id: ir.ValueId) void {
        const resolved = self.dead.resolveValue(value_id);
        if (resolved == self.first and self.first_position == null) self.first_position = self.position;
        if (resolved == self.second and self.second_position == null) self.second_position = self.position;
        self.position += 1;
    }

    pub fn pack(_: *ValueOrderVisitor, _: ir.ValuePackId) void {}
    pub fn place(_: *ValueOrderVisitor, _: ir.PlaceId) void {}
};

fn terminatorConsumerAllows(dead: *const dead_code.Plan, terminator: ir.Terminator, result_id: ir.ValueId) bool {
    return switch (terminator) {
        .jump, .return_values, .return_expanded, .throw_error => dead.terminatorUsesValue(terminator, result_id),
        .branch => |branch| dead.resolveValue(branch.condition) == result_id,
        .return_pack, .unreachable_block => false,
    };
}

fn isSingleResult(arity: ir.ResultArity) bool {
    return switch (arity) {
        .fixed => |count| count == 1,
        .variadic => false,
    };
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}
