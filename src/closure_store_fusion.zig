const std = @import("std");
const ir = @import("ir.zig");
const dead_code = @import("dead_code.zig");
const pack_plan = @import("pack_plan.zig");

pub const Plan = struct {
    allocator: std.mem.Allocator,
    consumers: []?ir.InstructionId,
    producers: []?ir.InstructionId,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program, dead: *const dead_code.Plan) !Plan {
        const consumers = try allocator.alloc(?ir.InstructionId, program.instructions.len);
        errdefer allocator.free(consumers);
        @memset(consumers, null);
        const producers = try allocator.alloc(?ir.InstructionId, program.instructions.len);
        errdefer allocator.free(producers);
        @memset(producers, null);

        var uses = try dead.semanticUseCounts(allocator, program);
        defer uses.deinit();
        for (program.blocks) |block| {
            for (block.instructions, 0..) |producer_id, index| {
                if (!validId(producer_id, program.instructions.len)) continue;
                const producer = program.instructions[producer_id.index()];
                const result_id = closureResult(program, dead, producer) orelse continue;
                if (result_id.index() >= uses.values.len or uses.values[result_id.index()] != 1) continue;
                var cursor = index + 1;
                while (cursor < block.instructions.len) : (cursor += 1) {
                    const consumer_id = block.instructions[cursor];
                    if (!validId(consumer_id, program.instructions.len)) break;
                    const consumer = program.instructions[consumer_id.index()];
                    if (producer.block != block.id or consumer.block != block.id) break;
                    if (dead.operationUsesValue(consumer.operation, result_id)) {
                        if (!dead.contains(consumer_id) and consumerStoresValue(consumer, result_id)) {
                            consumers[producer_id.index()] = consumer_id;
                            producers[consumer_id.index()] = producer_id;
                        }
                        break;
                    }
                    if (!canCrossGap(producer, consumer)) break;
                }
            }
        }
        return .{ .allocator = allocator, .consumers = consumers, .producers = producers };
    }

    pub fn deinit(self: *Plan) void {
        self.allocator.free(self.producers);
        self.allocator.free(self.consumers);
        self.* = undefined;
    }

    pub fn consumerForProducer(self: *const Plan, producer_id: ir.InstructionId) ?ir.InstructionId {
        if (!validId(producer_id, self.consumers.len)) return null;
        return self.consumers[producer_id.index()];
    }

    pub fn producerForConsumer(self: *const Plan, consumer_id: ir.InstructionId) ?ir.InstructionId {
        if (!validId(consumer_id, self.producers.len)) return null;
        return self.producers[consumer_id.index()];
    }
};

fn closureResult(program: *const ir.Program, dead: *const dead_code.Plan, instruction: ir.Instruction) ?ir.ValueId {
    if (dead.contains(instruction.id) or instruction.operation != .make_closure or instruction.results.len != 1 or instruction.pack_result != null) return null;
    const result_id = instruction.results[0];
    if (!validId(result_id, program.values.len)) return null;
    const origin_matches = switch (program.values[result_id.index()].origin) {
        .instruction_result => |origin| origin.instruction == instruction.id and origin.index == 0,
        else => false,
    };
    return if (origin_matches) result_id else null;
}

fn canCrossGap(producer: ir.Instruction, gap: ir.Instruction) bool {
    const capture_free = switch (producer.operation) {
        .make_closure => |closure| closure.bindings.len == 0,
        else => false,
    };
    return capture_free or pack_plan.isExactPure(gap.effects);
}

fn consumerStoresValue(instruction: ir.Instruction, result_id: ir.ValueId) bool {
    if (instruction.results.len != 0 or instruction.pack_result != null) return false;
    return switch (instruction.operation) {
        .table_set => |store| store.mode == .semantic and store.value == result_id,
        .environment_set => |store| store.mode == .semantic and store.value == result_id,
        else => false,
    };
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}

test "closure stores fuse sole uses and refuse externally reused closures" {
    const function_id = ir.FunctionId.fromIndex(0);
    const child_id = ir.FunctionId.fromIndex(1);
    const block_id = ir.BlockId.fromIndex(0);
    const child_block_id = ir.BlockId.fromIndex(1);
    const closure_id = ir.InstructionId.fromIndex(0);
    const store_id = ir.InstructionId.fromIndex(1);
    const table_value = ir.ValueId.fromIndex(0);
    const key_value = ir.ValueId.fromIndex(1);
    const closure_value = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = table_value, .function = function_id, .type = .{ .kind = .table }, .origin = .{ .parameter = 0 } },
        .{ .id = key_value, .function = function_id, .type = .string, .origin = .{ .parameter = 1 } },
        .{ .id = closure_value, .function = function_id, .type = .function, .origin = .{ .instruction_result = .{ .instruction = closure_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = closure_id, .block = block_id, .operation = .{ .make_closure = .{ .function = child_id, .bindings = &.{} } }, .results = &.{closure_value}, .effects = .pure },
        .{ .id = store_id, .block = block_id, .operation = .{ .table_set = .{ .table = table_value, .key = key_value, .value = closure_value, .mode = .semantic } }, .results = &.{}, .effects = .semantic_table_write },
    };
    var blocks = [_]ir.Block{
        .{ .id = block_id, .function = function_id, .instructions = &.{ closure_id, store_id }, .terminator = .{ .return_values = &.{} } },
        .{ .id = child_block_id, .function = child_id, .instructions = &.{}, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{
        .{ .id = function_id, .parameters = &.{ table_value, key_value }, .blocks = &.{block_id}, .entry_block = block_id },
        .{ .id = child_id, .lexical_parent = function_id, .blocks = &.{child_block_id}, .entry_block = child_block_id },
    };
    var program: ir.Program = .{
        .program_id = "closure-store-fusion",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer packs.deinit();
    var dead = try dead_code.Plan.init(std.testing.allocator, &program, &packs);
    defer dead.deinit();
    var fused = try Plan.init(std.testing.allocator, &program, &dead);
    defer fused.deinit();
    try std.testing.expectEqual(store_id, fused.consumerForProducer(closure_id).?);

    blocks[0].terminator = .{ .return_values = &.{closure_value} };
    program.blocks = &blocks;
    var reused_packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer reused_packs.deinit();
    var reused_dead = try dead_code.Plan.init(std.testing.allocator, &program, &reused_packs);
    defer reused_dead.deinit();
    var reused = try Plan.init(std.testing.allocator, &program, &reused_dead);
    defer reused.deinit();
    try std.testing.expect(reused.consumerForProducer(closure_id) == null);
}
