const std = @import("std");
const ir = @import("ir.zig");
const pack_plan = @import("pack_plan.zig");
const dead_code = @import("dead_code.zig");

pub const Consumer = union(enum) {
    instruction: ir.InstructionId,
    terminator: ir.BlockId,
};

pub const Plan = struct {
    allocator: std.mem.Allocator,
    consumers: []?Consumer,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program, packs: *const pack_plan.Plan, dead: *const dead_code.Plan) !Plan {
        const consumers = try allocator.alloc(?Consumer, program.instructions.len);
        errdefer allocator.free(consumers);
        @memset(consumers, null);

        var uses = try dead.semanticUseCounts(allocator, program);
        defer uses.deinit();

        for (program.blocks) |block| {
            for (block.instructions, 0..) |read_id, index| {
                if (!validId(read_id, program.instructions.len) or dead.contains(read_id)) continue;
                const read = program.instructions[read_id.index()];
                const result_id = readResult(program, read) orelse continue;
                if (result_id.index() >= uses.values.len or uses.values[result_id.index()] != 1) continue;

                var rendered_value = result_id;
                var consumer_index = index + 1;
                while (consumer_index < block.instructions.len) : (consumer_index += 1) {
                    const candidate_id = block.instructions[consumer_index];
                    if (!validId(candidate_id, program.instructions.len)) break;
                    const candidate = program.instructions[candidate_id.index()];
                    if (candidate.block != block.id) break;
                    if (dead.operationUsesValue(candidate.operation, rendered_value)) {
                        if (inlinedResult(program, dead, candidate)) |next_value| {
                            rendered_value = next_value;
                            continue;
                        }
                        if (!dead.contains(candidate_id) and projectedConsumerGapsAllowReadFusion(program, packs, candidate)) {
                            consumers[read_id.index()] = .{ .instruction = candidate_id };
                        }
                        break;
                    }
                    if (!canCross(candidate)) break;
                }

                if (consumer_index == block.instructions.len and dead.terminatorUsesValue(block.terminator, rendered_value)) {
                    consumers[read_id.index()] = .{ .terminator = block.id };
                }
            }
        }

        return .{ .allocator = allocator, .consumers = consumers };
    }

    pub fn deinit(self: *Plan) void {
        self.allocator.free(self.consumers);
        self.* = undefined;
    }

    pub fn consumer(self: *const Plan, read_id: ir.InstructionId) ?Consumer {
        if (!validId(read_id, self.consumers.len)) return null;
        return self.consumers[read_id.index()];
    }

    pub fn contains(self: *const Plan, read_id: ir.InstructionId) bool {
        return self.consumer(read_id) != null;
    }
};

fn readResult(program: *const ir.Program, instruction: ir.Instruction) ?ir.ValueId {
    const place_id = switch (instruction.operation) {
        .place_read => |value| value,
        else => return null,
    };
    if (!validId(place_id, program.places.len) or instruction.results.len != 1 or instruction.pack_result != null) return null;
    const result_id = instruction.results[0];
    if (!validId(result_id, program.values.len)) return null;
    const origin_matches = switch (program.values[result_id.index()].origin) {
        .instruction_result => |origin| origin.instruction == instruction.id and origin.index == 0,
        else => false,
    };
    return if (origin_matches) result_id else null;
}

fn inlinedResult(program: *const ir.Program, dead: *const dead_code.Plan, instruction: ir.Instruction) ?ir.ValueId {
    if (!dead.isInlined(instruction.id) or instruction.results.len != 1 or instruction.pack_result != null) return null;
    const result_id = instruction.results[0];
    if (!validId(result_id, program.values.len)) return null;
    const origin_matches = switch (program.values[result_id.index()].origin) {
        .instruction_result => |origin| origin.instruction == instruction.id and origin.index == 0,
        else => false,
    };
    return if (origin_matches) result_id else null;
}

fn canCross(instruction: ir.Instruction) bool {
    return instruction.effects.precision == .exact and
        !instruction.effects.writes_memory and
        !instruction.effects.may_throw and
        !instruction.effects.may_yield and
        !instruction.effects.invokes_unknown_code;
}

fn projectedConsumerGapsAllowReadFusion(program: *const ir.Program, packs: *const pack_plan.Plan, consumer: ir.Instruction) bool {
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

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}

test "place reads fuse through one-use inlined expressions but not intervening writes" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const then_block = ir.BlockId.fromIndex(1);
    const else_block = ir.BlockId.fromIndex(2);
    const read_id = ir.InstructionId.fromIndex(0);
    const unary_id = ir.InstructionId.fromIndex(1);
    const gap_id = ir.InstructionId.fromIndex(2);
    const write_id = ir.InstructionId.fromIndex(3);
    const replacement = ir.ValueId.fromIndex(0);
    const snapshot = ir.ValueId.fromIndex(1);
    const condition = ir.ValueId.fromIndex(2);
    const gap_value = ir.ValueId.fromIndex(3);
    const place_id = ir.PlaceId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = replacement, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = snapshot, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } } },
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = unary_id, .index = 0 } } },
        .{ .id = gap_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = gap_id, .index = 0 } } },
    };
    const places = [_]ir.Place{.{ .id = place_id, .function = function_id, .type = .boolean, .origin = .{ .local = 0 } }};
    const instructions = [_]ir.Instruction{
        .{ .id = read_id, .block = entry, .operation = .{ .place_read = place_id }, .results = &.{snapshot}, .effects = .place_read },
        .{ .id = unary_id, .block = entry, .operation = .{ .unary = .{ .operator = .logical_not, .operand = snapshot } }, .results = &.{condition}, .effects = .pure },
        .{ .id = gap_id, .block = entry, .operation = .{ .constant = .{ .integer = "7" } }, .results = &.{gap_value}, .effects = .pure },
        .{ .id = write_id, .block = entry, .operation = .{ .place_write = .{ .place = place_id, .value = replacement } }, .results = &.{}, .effects = .place_write },
    };
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{ read_id, gap_id, unary_id }, .terminator = .{ .branch = .{ .condition = condition, .then_edge = .{ .target = then_block, .arguments = &.{gap_value} }, .else_edge = .{ .target = else_block, .arguments = &.{gap_value} } } } },
        .{ .id = then_block, .function = function_id, .instructions = &.{}, .terminator = .{ .return_values = &.{} } },
        .{ .id = else_block, .function = function_id, .instructions = &.{}, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .parameters = &.{replacement}, .local_places = &.{place_id}, .blocks = &.{ entry, then_block, else_block }, .entry_block = entry }};
    var program: ir.Program = .{
        .program_id = "place-read-inlined-expression",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };

    var packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer packs.deinit();
    var dead = try dead_code.Plan.init(std.testing.allocator, &program, &packs);
    defer dead.deinit();
    var fused = try Plan.init(std.testing.allocator, &program, &packs, &dead);
    defer fused.deinit();
    try std.testing.expectEqual(Consumer{ .terminator = entry }, fused.consumer(read_id).?);

    blocks[0].instructions = &.{ read_id, gap_id, unary_id, write_id };
    program.blocks = &blocks;
    var blocked_packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer blocked_packs.deinit();
    var blocked_dead = try dead_code.Plan.init(std.testing.allocator, &program, &blocked_packs);
    defer blocked_dead.deinit();
    var blocked = try Plan.init(std.testing.allocator, &program, &blocked_packs, &blocked_dead);
    defer blocked.deinit();
    try std.testing.expect(blocked.consumer(read_id) == null);
}
