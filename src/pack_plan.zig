const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const readable_scope = @import("readable_scope.zig");
const pack_closure_safety = @import("pack_closure_safety.zig");
const pack_reentry_shape = @import("pack_reentry_shape.zig");
const pack_values_plan = @import("pack_values_plan.zig");
const invocation_projection = @import("invocation_projection.zig");
const stored_pack_plan = @import("stored_pack_plan.zig");

pub const InstructionRole = union(enum) {
    ordinary: void,
    fused_invocation_producer: ir.InstructionId,
    fused_adjustment: ir.InstructionId,
    materialized_invocation_producer: ir.InstructionId,
    materialized_adjustment: ir.InstructionId,
    materialized_adjustment_copy: ir.InstructionId,
    // The optional payload is retained for direct inspection; exact tail ownership lives in the plan map.
    stored_invocation_producer: ?ir.InstructionId,
    stored_adjustment: ir.InstructionId,
    fused_return_producer: ir.BlockId,
    direct_vararg_adjustment: void,
    fused_pack_values_producer: ir.InstructionId,
    materialized_pack_values_producer: void,
    fused_pack_values_adjustment: ir.InstructionId,
    fused_pack_values_return_producer: ir.BlockId,
};

pub const TerminatorRole = union(enum) {
    ordinary: void,
    fused_invocation_return: ir.InstructionId,
    fused_pack_values_return: ir.InstructionId,
    stored_pack_return: ir.InstructionId,
};

pub const ProjectionConsumer = invocation_projection.Consumer;

pub const PackValuesProjection = struct {
    consumer: ProjectionConsumer,
    gaps: []const ir.InstructionId,
};

pub const InvocationProjection = invocation_projection.Projection;
pub const InvocationProjectionMovedEdge = invocation_projection.ReentryEdge;
pub const InvocationProjectionReentry = invocation_projection.Reentry;
pub const InvocationProjectionReentryEdge = invocation_projection.ReentryEdge;
pub const InvocationProjectionExitEdge = invocation_projection.ReentryEdge;

pub const Plan = struct {
    allocator: std.mem.Allocator,
    roles: []InstructionRole,
    terminator_roles: []TerminatorRole,
    invocation_projections: []?InvocationProjection,
    stored_instruction_producers: []?ir.InstructionId,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program) !Plan {
        var scope = try readable_scope.Scope.init(allocator, program);
        defer scope.deinit();
        const roles = try allocator.alloc(InstructionRole, program.instructions.len);
        errdefer allocator.free(roles);
        @memset(roles, .{ .ordinary = {} });
        const terminator_roles = try allocator.alloc(TerminatorRole, program.blocks.len);
        errdefer allocator.free(terminator_roles);
        @memset(terminator_roles, .{ .ordinary = {} });
        const invocation_projections = try allocator.alloc(?InvocationProjection, program.instructions.len);
        errdefer allocator.free(invocation_projections);
        @memset(invocation_projections, null);
        errdefer deinitInvocationProjections(allocator, invocation_projections);
        const stored_instruction_producers = try allocator.alloc(?ir.InstructionId, program.instructions.len);
        errdefer allocator.free(stored_instruction_producers);
        @memset(stored_instruction_producers, null);

        const use_counts = try allocator.alloc(u32, program.value_packs.len);
        defer allocator.free(use_counts);
        @memset(use_counts, 0);
        const adjustment_consumers = try allocator.alloc(?ir.InstructionId, program.value_packs.len);
        defer allocator.free(adjustment_consumers);
        @memset(adjustment_consumers, null);
        const return_consumers = try allocator.alloc(?ir.BlockId, program.value_packs.len);
        defer allocator.free(return_consumers);
        @memset(return_consumers, null);
        const table_consumers = try allocator.alloc(?ir.InstructionId, program.value_packs.len);
        defer allocator.free(table_consumers);
        @memset(table_consumers, null);
        const invocation_argument_consumers = try allocator.alloc(?ir.InstructionId, program.value_packs.len);
        defer allocator.free(invocation_argument_consumers);
        @memset(invocation_argument_consumers, null);

        for (program.instructions) |instruction| {
            if (!scope.instruction(instruction.id)) continue;
            switch (instruction.operation) {
                .adjust_pack => |pack_id| if (validId(pack_id, program.value_packs.len)) {
                    incrementUse(use_counts, pack_id);
                    if (use_counts[pack_id.index()] == 1) adjustment_consumers[pack_id.index()] = instruction.id;
                },
                .make_table_literal => |constructor| if (constructor.tail_pack) |pack_id| {
                    if (validId(pack_id, program.value_packs.len)) {
                        incrementUse(use_counts, pack_id);
                        if (use_counts[pack_id.index()] == 1) table_consumers[pack_id.index()] = instruction.id;
                    }
                },
                .table_set_pack => |operation| if (validId(operation.pack, program.value_packs.len)) {
                    incrementUse(use_counts, operation.pack);
                    if (use_counts[operation.pack.index()] == 1) table_consumers[operation.pack.index()] = instruction.id;
                },
                else => {},
            }
            if (invocationArgumentPack(instruction.operation)) |pack_id| {
                if (validId(pack_id, program.value_packs.len)) {
                    incrementUse(use_counts, pack_id);
                    if (use_counts[pack_id.index()] == 1) invocation_argument_consumers[pack_id.index()] = instruction.id;
                }
            }
        }
        for (program.blocks) |block| {
            if (!scope.block(block.id)) continue;
            const pack_id = returnedPack(block.terminator) orelse continue;
            if (!validId(pack_id, program.value_packs.len)) continue;
            incrementUse(use_counts, pack_id);
            if (return_consumers[pack_id.index()] == null) return_consumers[pack_id.index()] = block.id;
        }

        for (program.instructions) |producer| {
            if (!scope.instruction(producer.id) or !validId(producer.id, roles.len)) continue;
            const consumer = pack_values_plan.consumer(
                program,
                producer,
                use_counts,
                adjustment_consumers,
                table_consumers,
                invocation_argument_consumers,
                return_consumers,
            ) orelse continue;
            if (!try packValuesConsumerIsSafe(allocator, program, &scope, producer, consumer)) continue;
            switch (consumer) {
                .adjustment => |consumer_id| {
                    if (roles[producer.id.index()] != .ordinary or roles[consumer_id.index()] != .ordinary) continue;
                    roles[producer.id.index()] = if (program.instructions[consumer_id.index()].results.len == 0)
                        .{ .materialized_pack_values_producer = {} }
                    else
                        .{ .fused_pack_values_producer = consumer_id };
                    roles[consumer_id.index()] = .{ .fused_pack_values_adjustment = producer.id };
                },
                .table_tail, .invocation_argument => |consumer_id| {
                    if (roles[producer.id.index()] != .ordinary or roles[consumer_id.index()] != .ordinary) continue;
                    roles[producer.id.index()] = .{ .fused_pack_values_producer = consumer_id };
                },
                .returned => |block_id| {
                    if (roles[producer.id.index()] != .ordinary or terminator_roles[block_id.index()] != .ordinary) continue;
                    roles[producer.id.index()] = .{ .fused_pack_values_return_producer = block_id };
                    terminator_roles[block_id.index()] = .{ .fused_pack_values_return = producer.id };
                },
            }
        }

        // Local fusions must be known before closure safety inspects nested open calls.
        for ([_]bool{ false, true }) |allow_materialization| {
            for (program.instructions) |producer| {
                if (!scope.instruction(producer.id)) continue;
                const pack_id = producer.pack_result orelse continue;
                if (!validId(pack_id, program.value_packs.len)) continue;
                if (!isVariadicInvocation(producer.operation) or producer.results.len != 0) continue;

                const pack = program.value_packs[pack_id.index()];
                const origin_matches = switch (pack.origin) {
                    .instruction_result => |instruction_id| instruction_id == producer.id,
                    else => false,
                };
                if (!origin_matches or !validId(producer.block, program.blocks.len) or program.blocks[producer.block.index()].function != pack.function) continue;

                if (use_counts[pack_id.index()] > 1) {
                    if (allow_materialization) {
                        if (try planDominatedAdjustments(allocator, program, &scope, roles, producer, pack_id, use_counts[pack_id.index()])) continue;
                        if (planSameBlockStoredPack(
                            program,
                            &scope,
                            roles,
                            terminator_roles,
                            producer,
                            pack_id,
                            use_counts[pack_id.index()],
                        )) continue;
                        _ = try planCrossBlockStoredPack(
                            allocator,
                            program,
                            &scope,
                            roles,
                            terminator_roles,
                            producer,
                            pack_id,
                            use_counts[pack_id.index()],
                        );
                        if (roles[producer.id.index()] == .ordinary and try planStoredTails(
                            allocator,
                            program,
                            &scope,
                            roles,
                            terminator_roles,
                            stored_instruction_producers,
                            producer,
                            pack_id,
                            use_counts[pack_id.index()],
                        )) continue;
                    }
                    continue;
                }
                if (use_counts[pack_id.index()] != 1) continue;

                if (adjustment_consumers[pack_id.index()]) |consumer_id| {
                    if (!validId(consumer_id, program.instructions.len)) continue;
                    const consumer = program.instructions[consumer_id.index()];
                    const consumed_pack = switch (consumer.operation) {
                        .adjust_pack => |value| value,
                        else => continue,
                    };
                    if (consumed_pack != pack_id or consumer.pack_result != null or !isExactPure(consumer.effects)) continue;
                    if (!sameFunction(program, producer, consumer, pack.function)) continue;
                    if (roles[producer.id.index()] != .ordinary or roles[consumer.id.index()] != .ordinary) continue;

                    if (immediatelyPrecedes(program, producer, consumer)) {
                        const projection = try invocation_projection.instructionAlloc(allocator, program, producer, consumer) orelse continue;
                        invocation_projections[producer.id.index()] = projection;
                        roles[producer.id.index()] = .{ .fused_invocation_producer = consumer.id };
                        roles[consumer.id.index()] = .{ .fused_adjustment = producer.id };
                    } else if (!allow_materialization or
                        !try planDominatedAdjustments(allocator, program, &scope, roles, producer, pack_id, use_counts[pack_id.index()])) continue;
                    continue;
                }

                if (table_consumers[pack_id.index()]) |consumer_id| {
                    if (!validId(consumer_id, program.instructions.len)) continue;
                    const consumer = program.instructions[consumer_id.index()];
                    const consumed_pack = switch (consumer.operation) {
                        .make_table_literal => |constructor| constructor.tail_pack,
                        .table_set_pack => |operation| operation.pack,
                        else => null,
                    };
                    if (consumed_pack == null or consumed_pack.? != pack_id or consumer.pack_result != null or !validTableConsumerResults(consumer)) continue;
                    if (!sameFunction(program, producer, consumer, pack.function)) continue;
                    if (roles[producer.id.index()] != .ordinary or roles[consumer.id.index()] != .ordinary) continue;
                    if (try invocation_projection.instructionAlloc(allocator, program, producer, consumer)) |projection| {
                        invocation_projections[producer.id.index()] = projection;
                        roles[producer.id.index()] = .{ .fused_invocation_producer = consumer.id };
                    } else if (!allow_materialization or !try planStoredTails(
                        allocator,
                        program,
                        &scope,
                        roles,
                        terminator_roles,
                        stored_instruction_producers,
                        producer,
                        pack_id,
                        use_counts[pack_id.index()],
                    )) continue;
                    continue;
                }

                if (invocation_argument_consumers[pack_id.index()]) |consumer_id| {
                    if (!validId(consumer_id, program.instructions.len)) continue;
                    const consumer = program.instructions[consumer_id.index()];
                    const consumed_pack = invocationArgumentPack(consumer.operation);
                    if (consumed_pack == null or consumed_pack.? != pack_id) continue;
                    if (!sameFunction(program, producer, consumer, pack.function)) continue;
                    if (roles[producer.id.index()] != .ordinary) continue;
                    if (roles[consumer.id.index()] == .ordinary) {
                        if (try invocation_projection.instructionAlloc(allocator, program, producer, consumer)) |projection| {
                            invocation_projections[producer.id.index()] = projection;
                            roles[producer.id.index()] = .{ .fused_invocation_producer = consumer.id };
                            continue;
                        }
                    }
                    if (!allow_materialization or !try planStoredTails(
                        allocator,
                        program,
                        &scope,
                        roles,
                        terminator_roles,
                        stored_instruction_producers,
                        producer,
                        pack_id,
                        use_counts[pack_id.index()],
                    )) continue;
                    continue;
                }

                const return_block_id = return_consumers[pack_id.index()] orelse continue;
                if (!validId(return_block_id, program.blocks.len)) continue;
                const return_block = program.blocks[return_block_id.index()];
                const returned_pack = returnedPack(return_block.terminator) orelse continue;
                if (returned_pack != pack_id or return_block.function != pack.function) continue;
                if (roles[producer.id.index()] != .ordinary or terminator_roles[return_block_id.index()] != .ordinary) continue;
                if (try invocation_projection.terminatorAlloc(allocator, program, producer, return_block_id)) |projection| {
                    invocation_projections[producer.id.index()] = projection;
                    roles[producer.id.index()] = .{ .fused_return_producer = return_block_id };
                    terminator_roles[return_block_id.index()] = .{ .fused_invocation_return = producer.id };
                    continue;
                }
                if (!allow_materialization) continue;
                if (planSameBlockStoredPack(
                    program,
                    &scope,
                    roles,
                    terminator_roles,
                    producer,
                    pack_id,
                    use_counts[pack_id.index()],
                )) continue;
                _ = try planCrossBlockStoredPack(
                    allocator,
                    program,
                    &scope,
                    roles,
                    terminator_roles,
                    producer,
                    pack_id,
                    use_counts[pack_id.index()],
                );
            }
        }

        for (program.instructions) |instruction| {
            if (!scope.instruction(instruction.id)) continue;
            if (roles[instruction.id.index()] != .ordinary or !isExactPure(instruction.effects)) continue;
            const pack_id = switch (instruction.operation) {
                .adjust_pack => |value| value,
                else => continue,
            };
            if (!validId(pack_id, program.value_packs.len)) continue;
            const pack = program.value_packs[pack_id.index()];
            const function_id = switch (pack.origin) {
                .varargs => |value| value,
                else => continue,
            };
            if (pack.function != function_id or !validId(function_id, program.functions.len)) continue;
            if (!program.functions[function_id.index()].is_variadic or program.functions[function_id.index()].vararg_pack != pack_id) continue;
            if (!validId(instruction.block, program.blocks.len) or program.blocks[instruction.block.index()].function != function_id) continue;
            roles[instruction.id.index()] = .{ .direct_vararg_adjustment = {} };
        }

        for (program.instructions) |producer| {
            if (!scope.instruction(producer.id) or !validId(producer.id, roles.len)) continue;
            const pack_id = producer.pack_result orelse continue;
            if (!validId(pack_id, use_counts.len) or use_counts[pack_id.index()] <= 1) continue;
            _ = try planMaterializedPackValues(
                allocator,
                program,
                &scope,
                roles,
                terminator_roles,
                producer,
                pack_id,
                use_counts[pack_id.index()],
            );
        }

        return .{
            .allocator = allocator,
            .roles = roles,
            .terminator_roles = terminator_roles,
            .invocation_projections = invocation_projections,
            .stored_instruction_producers = stored_instruction_producers,
        };
    }

    pub fn deinit(self: *Plan) void {
        deinitInvocationProjections(self.allocator, self.invocation_projections);
        self.allocator.free(self.invocation_projections);
        self.allocator.free(self.stored_instruction_producers);
        self.allocator.free(self.roles);
        self.allocator.free(self.terminator_roles);
        self.* = undefined;
    }

    pub fn role(self: *const Plan, instruction_id: ir.InstructionId) InstructionRole {
        if (instruction_id.index() >= self.roles.len) return .{ .ordinary = {} };
        return self.roles[instruction_id.index()];
    }

    pub fn terminatorRole(self: *const Plan, block_id: ir.BlockId) TerminatorRole {
        if (block_id.index() >= self.terminator_roles.len) return .{ .ordinary = {} };
        return self.terminator_roles[block_id.index()];
    }

    pub fn packValuesServesInstruction(self: *const Plan, producer_id: ir.InstructionId, consumer_id: ir.InstructionId) bool {
        return switch (self.role(producer_id)) {
            .fused_pack_values_producer => |planned_consumer| planned_consumer == consumer_id,
            .materialized_pack_values_producer => true,
            else => false,
        };
    }

    pub fn storedPackServesInstruction(self: *const Plan, producer_id: ir.InstructionId, consumer_id: ir.InstructionId) bool {
        if (consumer_id.index() >= self.stored_instruction_producers.len or
            self.stored_instruction_producers[consumer_id.index()] != producer_id) return false;
        return self.role(producer_id) == .stored_invocation_producer;
    }

    pub fn packValuesProjection(self: *const Plan, program: *const ir.Program, producer_id: ir.InstructionId) ?PackValuesProjection {
        if (!validId(producer_id, program.instructions.len)) return null;
        const producer = program.instructions[producer_id.index()];
        switch (producer.operation) {
            .pack_values => {},
            else => return null,
        }
        if (!validId(producer.block, program.blocks.len)) return null;
        const block = program.blocks[producer.block.index()];
        const producer_position = instructionPosition(block, producer_id) orelse return null;

        return switch (self.role(producer_id)) {
            .fused_pack_values_producer => |consumer_id| blk: {
                if (!validId(consumer_id, program.instructions.len)) break :blk null;
                const consumer = program.instructions[consumer_id.index()];
                if (consumer.block != block.id) break :blk null;
                const consumer_position = instructionPosition(block, consumer_id) orelse break :blk null;
                if (consumer_position <= producer_position) break :blk null;
                break :blk .{
                    .consumer = .{ .instruction = consumer_id },
                    .gaps = block.instructions[producer_position + 1 .. consumer_position],
                };
            },
            .fused_pack_values_return_producer => |return_block_id| blk: {
                if (return_block_id != block.id) break :blk null;
                const planned_producer = switch (self.terminatorRole(return_block_id)) {
                    .fused_pack_values_return => |instruction_id| instruction_id,
                    else => break :blk null,
                };
                if (planned_producer != producer_id) break :blk null;
                break :blk .{
                    .consumer = .{ .terminator = return_block_id },
                    .gaps = block.instructions[producer_position + 1 ..],
                };
            },
            else => null,
        };
    }

    pub fn invocationProjection(self: *const Plan, program: *const ir.Program, producer_id: ir.InstructionId) ?InvocationProjection {
        if (!validId(producer_id, program.instructions.len) or producer_id.index() >= self.invocation_projections.len) return null;
        const producer = program.instructions[producer_id.index()];
        if (!isVariadicInvocation(producer.operation) or producer.results.len != 0 or producer.pack_result == null) return null;
        const projection = self.invocation_projections[producer_id.index()] orelse return null;
        if (projection.producer != producer_id) return null;
        return switch (self.role(producer_id)) {
            .fused_invocation_producer => |consumer_id| switch (projection.consumer) {
                .instruction => |planned| if (planned == consumer_id) projection else null,
                .terminator => null,
            },
            .fused_return_producer => |block_id| switch (projection.consumer) {
                .instruction => null,
                .terminator => |planned| if (planned == block_id and
                    self.terminatorRole(block_id) == .fused_invocation_return and
                    self.terminatorRole(block_id).fused_invocation_return == producer_id) projection else null,
            },
            else => null,
        };
    }
};

fn instructionPosition(block: ir.Block, instruction_id: ir.InstructionId) ?usize {
    var position: ?usize = null;
    for (block.instructions, 0..) |listed_id, index| {
        if (listed_id != instruction_id) continue;
        if (position != null) return null;
        position = index;
    }
    return position;
}

pub fn projectionGapIsMovable(instruction: ir.Instruction) bool {
    return invocation_projection.gapIsMovable(instruction);
}

pub fn invocationProjectionIsMovable(program: *const ir.Program, projection: InvocationProjection) bool {
    return invocation_projection.isMovable(program, projection);
}

fn deinitInvocationProjections(allocator: std.mem.Allocator, projections: []?InvocationProjection) void {
    for (projections) |projection| if (projection) |value| value.deinit(allocator);
}

fn sameFunction(program: *const ir.Program, producer: ir.Instruction, consumer: ir.Instruction, pack_function: ir.FunctionId) bool {
    if (!validId(producer.block, program.blocks.len) or !validId(consumer.block, program.blocks.len)) return false;
    return program.blocks[producer.block.index()].function == pack_function and
        program.blocks[consumer.block.index()].function == pack_function;
}

fn packValuesConsumerIsSafe(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    producer: ir.Instruction,
    consumer: pack_values_plan.Consumer,
) !bool {
    if (!validId(producer.block, program.blocks.len)) return false;
    const producer_block = program.blocks[producer.block.index()];
    if (!validId(producer_block.function, program.functions.len)) return false;
    const consumer_block_id = switch (consumer) {
        .adjustment, .table_tail, .invocation_argument => |instruction_id| blk: {
            if (!validId(instruction_id, program.instructions.len)) break :blk null;
            const instruction = program.instructions[instruction_id.index()];
            break :blk if (validId(instruction.block, program.blocks.len)) instruction.block else null;
        },
        .returned => |block_id| if (validId(block_id, program.blocks.len)) block_id else null,
    } orelse return false;
    if (consumer_block_id == producer.block) return switch (consumer) {
        .adjustment, .table_tail, .invocation_argument => |instruction_id| pack_closure_safety.precedesInSameBlock(program, producer, program.instructions[instruction_id.index()]),
        .returned => instructionPosition(program.blocks[consumer_block_id.index()], producer.id) != null,
    };
    if (program.blocks[consumer_block_id.index()].function != producer_block.function) return false;

    var analysis = cfg.Analysis.init(allocator, program, program.functions[producer_block.function.index()]) catch |err| switch (err) {
        error.InvalidCfg => return false,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    if (!analysis.dominates(producer.block, consumer_block_id)) return false;
    return !try pack_closure_safety.hasReachablePath(
        allocator,
        program,
        scope,
        consumer_block_id,
        producer.block,
        producer_block.function,
    );
}

fn planMaterializedPackValues(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    roles: []InstructionRole,
    terminator_roles: []TerminatorRole,
    producer: ir.Instruction,
    pack_id: ir.ValuePackId,
    expected_use_count: u32,
) !bool {
    if (expected_use_count <= 1 or
        !validId(producer.id, roles.len) or
        roles[producer.id.index()] != .ordinary or
        producer.results.len != 0 or
        !isExactPure(producer.effects)) return false;
    const packed_values = switch (producer.operation) {
        .pack_values => |values| values,
        else => return false,
    };
    if (packed_values.len == 0 or !validId(pack_id, program.value_packs.len) or producer.pack_result != pack_id) return false;
    const pack = program.value_packs[pack_id.index()];
    const origin_matches = switch (pack.origin) {
        .instruction_result => |instruction_id| instruction_id == producer.id,
        else => false,
    };
    if (!origin_matches or pack.shape.tail != .closed) return false;

    var found_use_count: u32 = 0;
    for (program.instructions) |instruction| {
        if (!scope.instruction(instruction.id)) continue;
        const consumer = packValuesInstructionConsumer(instruction, pack_id) orelse continue;
        incrementCount(&found_use_count);
        if (!validId(instruction.id, roles.len) or roles[instruction.id.index()] != .ordinary) return false;
        switch (consumer) {
            .adjustment => if (instruction.pack_result != null or !isExactPure(instruction.effects)) return false,
            .table_tail => if (!validTableConsumerResults(instruction) or instruction.pack_result != null) return false,
            .invocation_argument => {},
            .returned => unreachable,
        }
        if (!try packValuesConsumerIsSafe(allocator, program, scope, producer, consumer)) return false;
    }
    for (program.blocks) |block| {
        if (!scope.block(block.id) or returnedPack(block.terminator) != pack_id) continue;
        incrementCount(&found_use_count);
        if (!validId(block.id, terminator_roles.len) or terminator_roles[block.id.index()] != .ordinary) return false;
        if (!try packValuesConsumerIsSafe(allocator, program, scope, producer, .{ .returned = block.id })) return false;
    }
    if (found_use_count != expected_use_count) return false;

    roles[producer.id.index()] = .{ .materialized_pack_values_producer = {} };
    for (program.instructions) |instruction| {
        if (!scope.instruction(instruction.id)) continue;
        switch (packValuesInstructionConsumer(instruction, pack_id) orelse continue) {
            .adjustment => roles[instruction.id.index()] = .{ .fused_pack_values_adjustment = producer.id },
            .table_tail, .invocation_argument => {},
            .returned => unreachable,
        }
    }
    for (program.blocks) |block| {
        if (!scope.block(block.id) or returnedPack(block.terminator) != pack_id) continue;
        terminator_roles[block.id.index()] = .{ .fused_pack_values_return = producer.id };
    }
    return true;
}

fn packValuesInstructionConsumer(instruction: ir.Instruction, pack_id: ir.ValuePackId) ?pack_values_plan.Consumer {
    switch (instruction.operation) {
        .adjust_pack => |consumed| if (consumed == pack_id) return .{ .adjustment = instruction.id },
        .make_table_literal => |constructor| if (constructor.tail_pack) |consumed| {
            if (consumed == pack_id) return .{ .table_tail = instruction.id };
        },
        .table_set_pack => |operation| if (operation.pack == pack_id) return .{ .table_tail = instruction.id },
        else => {},
    }
    if (invocationArgumentPack(instruction.operation)) |consumed| {
        if (consumed == pack_id) return .{ .invocation_argument = instruction.id };
    }
    return null;
}

fn validTableConsumerResults(instruction: ir.Instruction) bool {
    return switch (instruction.operation) {
        .make_table_literal => instruction.results.len == 1,
        .table_set_pack => instruction.results.len == 0,
        else => false,
    };
}

fn planStoredTails(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    roles: []InstructionRole,
    terminator_roles: []TerminatorRole,
    stored_instruction_producers: []?ir.InstructionId,
    producer: ir.Instruction,
    pack_id: ir.ValuePackId,
    use_count: u32,
) !bool {
    if (!validId(producer.id, roles.len) or roles[producer.id.index()] != .ordinary) return false;
    var matched = try stored_pack_plan.safeUsesAlloc(allocator, program, scope, producer, pack_id, use_count) orelse return false;
    defer matched.deinit();

    for (matched.uses) |use| switch (use) {
        .adjustment => |instruction_id| if (!validId(instruction_id, roles.len) or
            !validId(instruction_id, stored_instruction_producers.len) or
            roles[instruction_id.index()] != .ordinary or
            stored_instruction_producers[instruction_id.index()] != null) return false,
        .tail => |instruction_id| if (!validId(instruction_id, roles.len) or
            !validId(instruction_id, program.instructions.len) or
            !validId(instruction_id, stored_instruction_producers.len) or
            !roleCanConsumeStoredTail(program.instructions[instruction_id.index()], roles[instruction_id.index()]) or
            stored_instruction_producers[instruction_id.index()] != null) return false,
        .returned => |block_id| if (!validId(block_id, terminator_roles.len) or
            terminator_roles[block_id.index()] != .ordinary) return false,
    };

    const direct_consumer: ?ir.InstructionId = if (matched.uses.len == 1) switch (matched.uses[0]) {
        .tail => |instruction_id| instruction_id,
        else => null,
    } else null;
    roles[producer.id.index()] = .{ .stored_invocation_producer = direct_consumer };
    for (matched.uses) |use| switch (use) {
        .adjustment => |instruction_id| roles[instruction_id.index()] = .{ .stored_adjustment = producer.id },
        .tail => |instruction_id| stored_instruction_producers[instruction_id.index()] = producer.id,
        .returned => |block_id| terminator_roles[block_id.index()] = .{ .stored_pack_return = producer.id },
    };
    return true;
}

fn roleCanConsumeStoredTail(instruction: ir.Instruction, role: InstructionRole) bool {
    return switch (role) {
        .ordinary => true,
        .fused_invocation_producer,
        .materialized_invocation_producer,
        .stored_invocation_producer,
        .fused_return_producer,
        => isVariadicInvocation(instruction.operation) and
            instruction.results.len == 0 and
            instruction.pack_result != null,
        else => false,
    };
}

fn immediatelyPrecedes(program: *const ir.Program, producer: ir.Instruction, consumer: ir.Instruction) bool {
    if (producer.block != consumer.block or !validId(producer.block, program.blocks.len)) return false;
    const instructions = program.blocks[producer.block.index()].instructions;
    if (instructions.len < 2) return false;
    for (instructions[0 .. instructions.len - 1], 0..) |instruction_id, index| {
        if (instruction_id == producer.id) return instructions[index + 1] == consumer.id;
    }
    return false;
}

fn planDominatedAdjustments(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    roles: []InstructionRole,
    producer: ir.Instruction,
    pack_id: ir.ValuePackId,
    use_count: u32,
) !bool {
    if (use_count == 0 or
        !validId(producer.block, program.blocks.len) or
        !validId(producer.id, roles.len) or
        roles[producer.id.index()] != .ordinary) return false;
    const producer_block = program.blocks[producer.block.index()];
    if (!validId(producer_block.function, program.functions.len)) return false;
    var analysis = cfg.Analysis.init(allocator, program, program.functions[producer_block.function.index()]) catch |err| switch (err) {
        error.InvalidCfg => return false,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();

    const expected_count: usize = @intCast(use_count);
    var adjustments: std.ArrayList(ir.InstructionId) = .empty;
    defer adjustments.deinit(allocator);

    var primary_index: usize = 0;
    var primary_arity: usize = 0;
    var has_reentry = false;
    for (program.instructions) |instruction| {
        if (!scope.instruction(instruction.id)) continue;
        const consumed_pack = switch (instruction.operation) {
            .adjust_pack => |value| value,
            else => continue,
        };
        if (consumed_pack != pack_id) continue;
        if (!validId(instruction.id, roles.len) or
            !validId(instruction.block, program.blocks.len) or
            program.blocks[instruction.block.index()].function != producer_block.function or
            instruction.pack_result != null or
            !isExactPure(instruction.effects) or
            roles[instruction.id.index()] != .ordinary) return false;
        if (instruction.block == producer.block) {
            if (!pack_closure_safety.precedesInSameBlock(program, producer, instruction)) return false;
        } else {
            if (!analysis.dominates(producer.block, instruction.block)) return false;
            has_reentry = has_reentry or
                try pack_closure_safety.hasReachablePath(allocator, program, scope, instruction.block, producer.block, producer_block.function);
        }
        if (adjustments.items.len == 0 or instruction.results.len > primary_arity) {
            primary_index = adjustments.items.len;
            primary_arity = instruction.results.len;
        }
        try adjustments.append(allocator, instruction.id);
    }
    if (adjustments.items.len != expected_count) return false;
    if (has_reentry and try pack_closure_safety.functionHasReachableUnsafeClosure(
        allocator,
        program,
        scope,
        roles,
        &analysis,
        producer.block,
        producer_block.function,
    )) return false;

    const primary = adjustments.items[primary_index];
    roles[producer.id.index()] = .{ .materialized_invocation_producer = primary };
    for (adjustments.items) |instruction_id| {
        roles[instruction_id.index()] = if (instruction_id == primary)
            .{ .materialized_adjustment = producer.id }
        else
            .{ .materialized_adjustment_copy = primary };
    }
    return true;
}

fn planSameBlockStoredPack(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    roles: []InstructionRole,
    terminator_roles: []TerminatorRole,
    producer: ir.Instruction,
    pack_id: ir.ValuePackId,
    use_count: u32,
) bool {
    if (use_count == 0 or
        !validId(producer.id, roles.len) or
        roles[producer.id.index()] != .ordinary or
        !validId(producer.block, program.blocks.len) or
        !validId(producer.block, terminator_roles.len) or
        terminator_roles[producer.block.index()] != .ordinary or
        !validId(pack_id, program.value_packs.len) or
        producer.pack_result != pack_id) return false;

    const pack = program.value_packs[pack_id.index()];
    const origin_matches = switch (pack.origin) {
        .instruction_result => |instruction_id| instruction_id == producer.id,
        .varargs => false,
    };
    if (!origin_matches or pack.shape.tail != .open) return false;

    const block = program.blocks[producer.block.index()];
    if (block.function != pack.function or returnedPack(block.terminator) != pack_id) return false;
    const producer_position = instructionPosition(block, producer.id) orelse return false;

    var adjustment_count: usize = 0;
    for (program.instructions) |instruction| {
        if (!scope.instruction(instruction.id)) continue;
        const consumed = switch (instruction.operation) {
            .adjust_pack => |candidate| candidate,
            else => continue,
        };
        if (consumed != pack_id) continue;
        if (!validId(instruction.id, roles.len) or
            roles[instruction.id.index()] != .ordinary or
            instruction.block != block.id or
            instruction.pack_result != null or
            !isExactPure(instruction.effects)) return false;
        const position = instructionPosition(block, instruction.id) orelse return false;
        if (position <= producer_position) return false;
        adjustment_count = std.math.add(usize, adjustment_count, 1) catch return false;
    }
    if (adjustment_count + 1 != @as(usize, @intCast(use_count))) return false;

    roles[producer.id.index()] = .{ .stored_invocation_producer = null };
    for (program.instructions) |instruction| {
        if (!scope.instruction(instruction.id)) continue;
        const consumed = switch (instruction.operation) {
            .adjust_pack => |candidate| candidate,
            else => continue,
        };
        if (consumed == pack_id) roles[instruction.id.index()] = .{ .stored_adjustment = producer.id };
    }
    terminator_roles[block.id.index()] = .{ .stored_pack_return = producer.id };
    return true;
}

fn planCrossBlockStoredPack(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    roles: []InstructionRole,
    terminator_roles: []TerminatorRole,
    producer: ir.Instruction,
    pack_id: ir.ValuePackId,
    use_count: u32,
) !bool {
    if (use_count == 0 or
        !validId(producer.id, roles.len) or
        roles[producer.id.index()] != .ordinary or
        !validId(producer.block, program.blocks.len) or
        !validId(pack_id, program.value_packs.len) or
        producer.pack_result != pack_id) return false;

    const pack = program.value_packs[pack_id.index()];
    const origin_matches = switch (pack.origin) {
        .instruction_result => |instruction_id| instruction_id == producer.id,
        .varargs => false,
    };
    const producer_block = program.blocks[producer.block.index()];
    if (!origin_matches or pack.shape.tail != .open or producer_block.function != pack.function or
        !validId(producer_block.function, program.functions.len)) return false;

    var analysis = cfg.Analysis.init(allocator, program, program.functions[producer_block.function.index()]) catch |err| switch (err) {
        error.InvalidCfg => return false,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    const producer_has_reentry = try pack_closure_safety.blockHasReachableReentry(&analysis, producer.block);

    var adjustment_count: usize = 0;
    var has_cross_block_consumer = false;
    for (program.instructions) |instruction| {
        if (!scope.instruction(instruction.id)) continue;
        const consumed = switch (instruction.operation) {
            .adjust_pack => |candidate| candidate,
            else => continue,
        };
        if (consumed != pack_id) continue;
        if (!validId(instruction.id, roles.len) or
            roles[instruction.id.index()] != .ordinary or
            !validId(instruction.block, program.blocks.len) or
            program.blocks[instruction.block.index()].function != producer_block.function or
            instruction.pack_result != null or
            !isExactPure(instruction.effects)) return false;
        if (instruction.block == producer.block) {
            if (!pack_closure_safety.precedesInSameBlock(program, producer, instruction)) return false;
        } else {
            if (!analysis.dominates(producer.block, instruction.block)) return false;
            has_cross_block_consumer = true;
        }
        adjustment_count = std.math.add(usize, adjustment_count, 1) catch return false;
    }

    var return_block: ?ir.Block = null;
    for (program.blocks) |block| {
        if (!scope.block(block.id) or returnedPack(block.terminator) != pack_id) continue;
        if (return_block != null or
            block.function != producer_block.function or
            !validId(block.id, terminator_roles.len) or
            terminator_roles[block.id.index()] != .ordinary) return false;
        if (block.id == producer.block) {
            if (instructionPosition(block, producer.id) == null) return false;
        } else {
            if (!analysis.dominates(producer.block, block.id)) return false;
            has_cross_block_consumer = true;
        }
        return_block = block;
    }
    const expanded_consumer = return_block orelse return false;
    if (adjustment_count + 1 != @as(usize, @intCast(use_count)) or
        !has_cross_block_consumer) return false;
    if (producer_has_reentry and !try storedPackReentryIsSafe(
        allocator,
        program,
        scope,
        roles,
        &analysis,
        producer,
        pack_id,
        expanded_consumer.id,
        producer_block.function,
    )) return false;

    roles[producer.id.index()] = .{ .stored_invocation_producer = null };
    for (program.instructions) |instruction| {
        if (!scope.instruction(instruction.id)) continue;
        const consumed = switch (instruction.operation) {
            .adjust_pack => |candidate| candidate,
            else => continue,
        };
        if (consumed == pack_id) roles[instruction.id.index()] = .{ .stored_adjustment = producer.id };
    }
    terminator_roles[expanded_consumer.id.index()] = .{ .stored_pack_return = producer.id };
    return true;
}

fn storedPackReentryIsSafe(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    roles: []InstructionRole,
    analysis: *const cfg.Analysis,
    producer: ir.Instruction,
    pack_id: ir.ValuePackId,
    return_block: ir.BlockId,
    function_id: ir.FunctionId,
) !bool {
    var membership = try pack_reentry_shape.collectSupportedPostTestedLoop(
        allocator,
        analysis,
        producer.block,
        return_block,
    ) orelse return false;
    defer membership.deinit();

    const return_index = analysis.blockIndex(return_block) orelse return false;
    if (membership.bits[return_index]) return false;
    for (program.instructions) |instruction| {
        if (!scope.instruction(instruction.id)) continue;
        const consumed = switch (instruction.operation) {
            .adjust_pack => |candidate| candidate,
            else => continue,
        };
        if (consumed != pack_id) continue;
        const block_index = analysis.blockIndex(instruction.block) orelse return false;
        if (!membership.bits[block_index]) return false;
    }
    return !try pack_closure_safety.functionHasReachableUnsafeClosure(
        allocator,
        program,
        scope,
        roles,
        analysis,
        producer.block,
        function_id,
    );
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

pub fn isExactPure(effects: ir.EffectSummary) bool {
    return effects.precision == .exact and
        !effects.reads_memory and
        !effects.writes_memory and
        !effects.may_throw and
        !effects.may_yield and
        !effects.invokes_unknown_code;
}

fn incrementUse(counts: []u32, pack_id: ir.ValuePackId) void {
    if (counts[pack_id.index()] != std.math.maxInt(u32)) counts[pack_id.index()] += 1;
}

fn incrementCount(count: *u32) void {
    if (count.* != std.math.maxInt(u32)) count.* += 1;
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}
