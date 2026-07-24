const std = @import("std");
const ir = @import("ir.zig");
const pack_plan = @import("pack_plan.zig");
const dead_code = @import("dead_code.zig");
const runtime_uses = @import("runtime_uses.zig");

pub const Role = union(enum) {
    ordinary: void,
    producer: ir.InstructionId,
    write: ir.InstructionId,
};

pub const Plan = struct {
    allocator: std.mem.Allocator,
    roles: []Role,

    pub fn init(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        packs: *const pack_plan.Plan,
        dead: *const dead_code.Plan,
    ) !Plan {
        const roles = try allocator.alloc(Role, program.instructions.len);
        errdefer allocator.free(roles);
        @memset(roles, .{ .ordinary = {} });

        var uses = try dead.semanticUseCounts(allocator, program);
        defer uses.deinit();

        for (program.blocks) |block| {
            if (block.instructions.len < 2) continue;
            for (block.instructions[0 .. block.instructions.len - 1], 0..) |producer_id, index| {
                const write_id = block.instructions[index + 1];
                if (!validId(producer_id, program.instructions.len) or !validId(write_id, program.instructions.len)) continue;
                const producer = program.instructions[producer_id.index()];
                const write = program.instructions[write_id.index()];
                if (!isCandidate(program, packs, dead, uses.values, block.id, producer, write)) continue;
                roles[producer_id.index()] = .{ .producer = write_id };
                roles[write_id.index()] = .{ .write = producer_id };
            }
        }

        return .{ .allocator = allocator, .roles = roles };
    }

    pub fn deinit(self: *Plan) void {
        self.allocator.free(self.roles);
        self.* = undefined;
    }

    pub fn role(self: *const Plan, instruction_id: ir.InstructionId) Role {
        if (!validId(instruction_id, self.roles.len)) return .{ .ordinary = {} };
        return self.roles[instruction_id.index()];
    }

    pub fn consumerForProducer(self: *const Plan, instruction_id: ir.InstructionId) ?ir.InstructionId {
        return switch (self.role(instruction_id)) {
            .producer => |consumer| consumer,
            else => null,
        };
    }

    pub fn producerForWrite(self: *const Plan, instruction_id: ir.InstructionId) ?ir.InstructionId {
        return switch (self.role(instruction_id)) {
            .write => |producer| producer,
            else => null,
        };
    }
};

fn isCandidate(
    program: *const ir.Program,
    packs: *const pack_plan.Plan,
    dead: *const dead_code.Plan,
    value_uses: []const usize,
    block_id: ir.BlockId,
    producer: ir.Instruction,
    write: ir.Instruction,
) bool {
    if (producer.block != block_id or write.block != block_id) return false;
    if ((dead.contains(producer.id) and !dead.isInlined(producer.id)) or dead.contains(write.id)) return false;
    if (packs.role(write.id) != .ordinary) return false;
    if (producer.results.len != 1 or producer.pack_result != null or write.results.len != 0 or write.pack_result != null) return false;
    if (!operationRendersAsExpression(producer.operation, packs.role(producer.id))) return false;

    const result_id = producer.results[0];
    if (!validId(result_id, program.values.len) or result_id.index() >= value_uses.len or value_uses[result_id.index()] != 1) return false;
    const origin_matches = switch (program.values[result_id.index()].origin) {
        .instruction_result => |origin| origin.instruction == producer.id and origin.index == 0,
        else => false,
    };
    if (!origin_matches) return false;

    const place_write = switch (write.operation) {
        .place_write => |operation| operation,
        else => return false,
    };
    return place_write.value == result_id;
}

fn operationRendersAsExpression(operation: ir.Operation, pack_role: pack_plan.InstructionRole) bool {
    return switch (pack_role) {
        .ordinary => switch (operation) {
            .constant, .copy, .unary, .binary, .environment_get, .table_get, .make_table, .make_table_literal, .string_interpolate, .make_closure, .function_ref => true,
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

fn isSingleResult(arity: ir.ResultArity) bool {
    return switch (arity) {
        .fixed => |count| count == 1,
        .variadic => false,
    };
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}
