const std = @import("std");
const ir = @import("ir.zig");
const dead_code = @import("dead_code.zig");
const place_write_fusion = @import("place_write_fusion.zig");
const place_read_fusion = @import("place_read_fusion.zig");

pub const PlaceUpdate = struct {
    operator: ir.BinaryOperator,
    right: ir.ValueId,
    read: ir.InstructionId,
};

pub const MemoryAddress = union(enum) {
    table: struct {
        table: ir.ValueId,
        key: ir.ValueId,
    },
    environment: struct {
        target: ir.EnvironmentTarget,
        name: []const u8,
    },
};

pub const MemoryUpdate = struct {
    operator: ir.BinaryOperator,
    address: MemoryAddress,
    right: ir.ValueId,
};

pub fn matchPlace(
    program: *const ir.Program,
    dead: *const dead_code.Plan,
    place_writes: *const place_write_fusion.Plan,
    place_reads: *const place_read_fusion.Plan,
    producer: ir.Instruction,
    write: ir.Instruction,
) ?PlaceUpdate {
    if (place_writes.producerForWrite(write.id) != producer.id) return null;
    const write_operation = switch (write.operation) {
        .place_write => |value| value,
        else => return null,
    };
    const binary = switch (producer.operation) {
        .binary => |value| value,
        else => return null,
    };
    if (binary.mode != .semantic or !supportsOperator(binary.operator)) return null;

    const left = dead.resolveValue(binary.left);
    if (left.index() >= program.values.len) return null;
    const origin = switch (program.values[left.index()].origin) {
        .instruction_result => |value| value,
        else => return null,
    };
    if (origin.index != 0 or origin.instruction.index() >= program.instructions.len) return null;
    const read = program.instructions[origin.instruction.index()];
    const read_place = switch (read.operation) {
        .place_read => |value| value,
        else => return null,
    };
    if (read_place != write_operation.place) return null;
    const consumer = place_reads.consumer(read.id) orelse return null;
    switch (consumer) {
        .instruction => |instruction_id| {
            const direct_consumer = instruction_id == producer.id;
            const inlined_into_write = dead.isInlined(producer.id) and instruction_id == write.id;
            if (!direct_consumer and !inlined_into_write) return null;
        },
        .terminator => return null,
    }
    return .{ .operator = binary.operator, .right = binary.right, .read = read.id };
}

pub fn rhsMayInlineAcrossTargetRead(
    program: *const ir.Program,
    dead: *const dead_code.Plan,
    place_writes: *const place_write_fusion.Plan,
    place_reads: *const place_read_fusion.Plan,
    rhs: ir.ValueId,
    read_result: ir.ValueId,
    binary: ir.Instruction,
) bool {
    const write_id = place_writes.consumerForProducer(binary.id) orelse return false;
    if (write_id.index() >= program.instructions.len) return false;
    _ = matchPlace(program, dead, place_writes, place_reads, binary, program.instructions[write_id.index()]) orelse return false;
    const operation = binary.operation.binary;
    return dead.resolveValue(operation.right) == dead.resolveValue(rhs) and
        dead.resolveValue(operation.left) == dead.resolveValue(read_result);
}

pub fn matchTable(
    program: *const ir.Program,
    dead: *const dead_code.Plan,
    fused_values: anytype,
    instruction: ir.Instruction,
) ?MemoryUpdate {
    const store = switch (instruction.operation) {
        .table_set => |value| value,
        else => return null,
    };
    if (store.mode != .semantic) return null;
    const binary_match = matchStoredBinary(program, dead, fused_values, store.value, instruction.id) orelse return null;
    const get_instruction = valueProducer(program, dead, binary_match.operation.left) orelse return null;
    if (!instructionConsumerIs(fused_values, get_instruction.id, binary_match.instruction.id)) return null;
    const get = switch (get_instruction.operation) {
        .table_get => |value| value,
        else => return null,
    };
    if (get.mode != .semantic or dead.resolveValue(get.table) != dead.resolveValue(store.table) or
        dead.resolveValue(get.key) != dead.resolveValue(store.key)) return null;
    return .{
        .operator = binary_match.operation.operator,
        .address = .{ .table = .{ .table = store.table, .key = store.key } },
        .right = binary_match.operation.right,
    };
}

pub fn matchEnvironment(
    program: *const ir.Program,
    dead: *const dead_code.Plan,
    fused_values: anytype,
    instruction: ir.Instruction,
) ?MemoryUpdate {
    const store = switch (instruction.operation) {
        .environment_set => |value| value,
        else => return null,
    };
    if (store.mode != .semantic) return null;
    const binary_match = matchStoredBinary(program, dead, fused_values, store.value, instruction.id) orelse return null;
    const get_instruction = valueProducer(program, dead, binary_match.operation.left) orelse return null;
    if (!instructionConsumerIs(fused_values, get_instruction.id, binary_match.instruction.id)) return null;
    const get = switch (get_instruction.operation) {
        .environment_get => |value| value,
        else => return null,
    };
    if (get.mode != .semantic or !sameEnvironmentTarget(dead, get.target, store.target) or !std.mem.eql(u8, get.name, store.name)) return null;
    return .{
        .operator = binary_match.operation.operator,
        .address = .{ .environment = .{ .target = store.target, .name = store.name } },
        .right = binary_match.operation.right,
    };
}

const BinaryMatch = struct {
    instruction: ir.Instruction,
    operation: ir.Binary,
};

fn matchStoredBinary(
    program: *const ir.Program,
    dead: *const dead_code.Plan,
    fused_values: anytype,
    stored_value: ir.ValueId,
    store_instruction: ir.InstructionId,
) ?BinaryMatch {
    const instruction = valueProducer(program, dead, stored_value) orelse return null;
    if (!instructionConsumerIs(fused_values, instruction.id, store_instruction)) return null;
    const operation = switch (instruction.operation) {
        .binary => |value| value,
        else => return null,
    };
    if (operation.mode != .semantic or !supportsOperator(operation.operator)) return null;
    return .{ .instruction = instruction, .operation = operation };
}

fn valueProducer(program: *const ir.Program, dead: *const dead_code.Plan, value: ir.ValueId) ?ir.Instruction {
    const resolved = dead.resolveValue(value);
    if (resolved.index() >= program.values.len) return null;
    const origin = switch (program.values[resolved.index()].origin) {
        .instruction_result => |item| item,
        else => return null,
    };
    if (origin.index != 0 or origin.instruction.index() >= program.instructions.len) return null;
    return program.instructions[origin.instruction.index()];
}

fn sameEnvironmentTarget(dead: *const dead_code.Plan, left: ir.EnvironmentTarget, right: ir.EnvironmentTarget) bool {
    return switch (left) {
        .ambient => right == .ambient,
        .value => |left_value| switch (right) {
            .ambient => false,
            .value => |right_value| dead.resolveValue(left_value) == dead.resolveValue(right_value),
        },
    };
}

fn instructionConsumerIs(fused_values: anytype, producer: ir.InstructionId, expected: ir.InstructionId) bool {
    const consumer = fused_values.consumer(producer) orelse return false;
    return switch (consumer) {
        .instruction => |instruction_id| instruction_id == expected,
        .terminator => false,
    };
}

pub fn supportsOperator(operator: ir.BinaryOperator) bool {
    return switch (operator) {
        .add, .subtract, .multiply, .divide, .floor_divide, .modulo, .power, .concat => true,
        else => false,
    };
}

test "memory compound matching requires semantic access and exact address identity" {
    const Consumer = union(enum) {
        instruction: ir.InstructionId,
        terminator: ir.BlockId,
    };
    const Fusion = struct {
        consumers: []const ?Consumer,

        fn consumer(self: *const @This(), instruction: ir.InstructionId) ?Consumer {
            if (instruction.index() >= self.consumers.len) return null;
            return self.consumers[instruction.index()];
        }
    };

    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const get_id = ir.InstructionId.fromIndex(0);
    const binary_id = ir.InstructionId.fromIndex(1);
    const set_id = ir.InstructionId.fromIndex(2);
    const table = ir.ValueId.fromIndex(0);
    const key = ir.ValueId.fromIndex(1);
    const other_key = ir.ValueId.fromIndex(2);
    const right = ir.ValueId.fromIndex(3);
    const current = ir.ValueId.fromIndex(4);
    const updated = ir.ValueId.fromIndex(5);
    const values = [_]ir.Value{
        .{ .id = table, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = key, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = other_key, .function = function_id, .origin = .{ .parameter = 2 } },
        .{ .id = right, .function = function_id, .origin = .{ .parameter = 3 } },
        .{ .id = current, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = get_id, .index = 0 } } },
        .{ .id = updated, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = binary_id, .index = 0 } } },
    };
    var instructions = [_]ir.Instruction{
        .{ .id = get_id, .block = block_id, .operation = .{ .table_get = .{ .table = table, .key = key } }, .results = &.{current}, .effects = .semantic_table_read },
        .{ .id = binary_id, .block = block_id, .operation = .{ .binary = .{ .operator = .add, .left = current, .right = right } }, .results = &.{updated}, .effects = .dynamic_call },
        .{ .id = set_id, .block = block_id, .operation = .{ .table_set = .{ .table = table, .key = key, .value = updated } }, .results = &.{}, .effects = .semantic_table_write },
    };
    const aliases = [_]ir.ValueId{ table, key, other_key, right, current, updated };
    const eliminated = [_]bool{ false, false, false };
    const inlined = [_]bool{ false, false, false };
    const dead: dead_code.Plan = .{
        .allocator = std.testing.allocator,
        .eliminated = @constCast(&eliminated),
        .aliases = @constCast(&aliases),
        .inlined = @constCast(&inlined),
    };
    const consumers = [_]?Consumer{
        .{ .instruction = binary_id },
        .{ .instruction = set_id },
        null,
    };
    const fused: Fusion = .{ .consumers = &consumers };
    var program: ir.Program = .{
        .program_id = "table-compound-match",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };

    const update = matchTable(&program, &dead, &fused, instructions[set_id.index()]) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(ir.BinaryOperator.add, update.operator);
    const address = switch (update.address) {
        .table => |value| value,
        .environment => return error.TestUnexpectedResult,
    };
    try std.testing.expectEqual(table, address.table);
    try std.testing.expectEqual(key, address.key);
    try std.testing.expectEqual(right, update.right);

    instructions[get_id.index()].operation.table_get.mode = .raw;
    try std.testing.expect(matchTable(&program, &dead, &fused, instructions[set_id.index()]) == null);
    instructions[get_id.index()].operation.table_get.mode = .semantic;
    instructions[get_id.index()].operation.table_get.key = other_key;
    try std.testing.expect(matchTable(&program, &dead, &fused, instructions[set_id.index()]) == null);
    instructions[get_id.index()].operation.table_get.key = key;
    instructions[set_id.index()].operation.table_set.mode = .raw;
    try std.testing.expect(matchTable(&program, &dead, &fused, instructions[set_id.index()]) == null);

    instructions[get_id.index()].operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "probe" } };
    instructions[set_id.index()].operation = .{ .environment_set = .{ .target = .{ .ambient = {} }, .name = "probe", .value = updated } };
    const environment_update = matchEnvironment(&program, &dead, &fused, instructions[set_id.index()]) orelse return error.TestUnexpectedResult;
    const environment_address = switch (environment_update.address) {
        .table => return error.TestUnexpectedResult,
        .environment => |value| value,
    };
    try std.testing.expect(environment_address.target == .ambient);
    try std.testing.expectEqualStrings("probe", environment_address.name);

    instructions[get_id.index()].operation.environment_get.name = "other";
    try std.testing.expect(matchEnvironment(&program, &dead, &fused, instructions[set_id.index()]) == null);
    instructions[get_id.index()].operation.environment_get = .{ .target = .{ .value = table }, .name = "probe" };
    instructions[set_id.index()].operation.environment_set.target = .{ .value = table };
    try std.testing.expect(matchEnvironment(&program, &dead, &fused, instructions[set_id.index()]) != null);
    instructions[get_id.index()].operation.environment_get.target = .{ .value = other_key };
    try std.testing.expect(matchEnvironment(&program, &dead, &fused, instructions[set_id.index()]) == null);
    instructions[get_id.index()].operation.environment_get.target = .{ .value = table };
    instructions[set_id.index()].operation.environment_set.mode = .raw;
    try std.testing.expect(matchEnvironment(&program, &dead, &fused, instructions[set_id.index()]) == null);
}
