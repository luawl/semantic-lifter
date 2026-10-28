const std = @import("std");
const ir = @import("ir.zig");
const value_fusion = @import("value_fusion.zig");
const pack_plan = @import("pack_plan.zig");
const dead_code = @import("dead_code.zig");
const place_write_fusion = @import("place_write_fusion.zig");
const place_read_fusion = @import("place_read_fusion.zig");
const compound_update = @import("compound_update.zig");
const luau_runtime = @import("luau_runtime.zig");

const Plan = value_fusion.Plan;
const Consumer = value_fusion.Consumer;
fn planForTest(allocator: std.mem.Allocator, program: *const ir.Program) !Plan {
    var packs = try pack_plan.Plan.init(allocator, program);
    defer packs.deinit();
    var dead = try dead_code.Plan.init(allocator, program, &packs);
    defer dead.deinit();
    var place_writes = try place_write_fusion.Plan.init(allocator, program, &packs, &dead);
    defer place_writes.deinit();
    var place_reads = try place_read_fusion.Plan.init(allocator, program, &packs, &dead);
    defer place_reads.deinit();
    return Plan.init(allocator, program, &packs, &dead, &place_writes, &place_reads);
}

fn fusedOperationDepth(plan: *const Plan, start: ir.InstructionId) usize {
    var depth: usize = 1;
    var current = start;
    var remaining = plan.consumers.len + 1;
    while (remaining != 0) : (remaining -= 1) {
        const consumer = plan.consumer(current) orelse return depth;
        switch (consumer) {
            .terminator => return depth,
            .instruction => |instruction_id| {
                depth += 1;
                current = instruction_id;
            },
        }
    }
    return std.math.maxInt(usize);
}

test "value fusion bounds transitive emitted expression depth" {
    const operation_count = luau_runtime.max_fused_expression_operations + 3;
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const initial = ir.ValueId.fromIndex(0);
    const increment = ir.ValueId.fromIndex(1);
    var values: [operation_count + 2]ir.Value = undefined;
    var instructions: [operation_count]ir.Instruction = undefined;
    var instruction_ids: [operation_count]ir.InstructionId = undefined;
    var result_ids: [operation_count][1]ir.ValueId = undefined;
    values[initial.index()] = .{ .id = initial, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } };
    values[increment.index()] = .{ .id = increment, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } };

    var left = initial;
    for (0..operation_count) |index| {
        const instruction_id = ir.InstructionId.fromIndex(index);
        const result = ir.ValueId.fromIndex(index + 2);
        instruction_ids[index] = instruction_id;
        result_ids[index] = .{result};
        values[result.index()] = .{
            .id = result,
            .function = function_id,
            .type = .integer,
            .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } },
        };
        instructions[index] = .{
            .id = instruction_id,
            .block = block_id,
            .operation = .{ .binary = .{ .operator = .add, .left = left, .right = increment } },
            .results = &result_ids[index],
            .effects = .dynamic_call,
        };
        left = result;
    }

    const returned = [_]ir.ValueId{left};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &instruction_ids,
        .terminator = .{ .return_values = &returned },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ initial, increment },
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    var program: ir.Program = .{
        .program_id = "bounded-value-fusion-depth",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var plan = try planForTest(std.testing.allocator, &program);
    defer plan.deinit();
    var maximum_depth: usize = 0;
    var materialized_breaks: usize = 0;
    for (instruction_ids) |instruction_id| {
        maximum_depth = @max(maximum_depth, fusedOperationDepth(&plan, instruction_id));
        if (plan.consumer(instruction_id) == null) materialized_breaks += 1;
    }
    try std.testing.expectEqual(luau_runtime.max_fused_expression_operations, maximum_depth);
    try std.testing.expect(materialized_breaks > 0);

    for (&instructions) |*instruction| instruction.effects = .pure;
    program.instructions = &instructions;
    var packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer packs.deinit();
    var dead = try dead_code.Plan.init(std.testing.allocator, &program, &packs);
    defer dead.deinit();
    var inlined_run: usize = 0;
    var maximum_inlined_run: usize = 0;
    var inline_breaks: usize = 0;
    for (instruction_ids) |instruction_id| {
        if (dead.isInlined(instruction_id)) {
            inlined_run += 1;
            maximum_inlined_run = @max(maximum_inlined_run, inlined_run);
        } else {
            inlined_run = 0;
            inline_breaks += 1;
        }
    }
    try std.testing.expectEqual(luau_runtime.max_fused_expression_operations - 1, maximum_inlined_run);
    try std.testing.expect(inline_breaks > 0);
}

test "sole adjacent effectful values fuse into branch and return terminators" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const then_block = ir.BlockId.fromIndex(1);
    const else_block = ir.BlockId.fromIndex(2);
    const call_id = ir.InstructionId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(0);
    const result = ir.ValueId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = result, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = call_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = call_id,
        .block = entry,
        .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } },
        .results = &.{result},
        .effects = .dynamic_call,
    }};
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{call_id}, .terminator = .{ .branch = .{ .condition = result, .then_edge = .{ .target = then_block }, .else_edge = .{ .target = else_block } } } },
        .{ .id = then_block, .function = function_id, .instructions = &.{}, .terminator = .{ .return_values = &.{} } },
        .{ .id = else_block, .function = function_id, .instructions = &.{}, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .parameters = &.{callee}, .blocks = &.{ entry, then_block, else_block }, .entry_block = entry }};
    var program: ir.Program = .{
        .program_id = "value-fusion-terminators",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var branch_plan = try planForTest(std.testing.allocator, &program);
    defer branch_plan.deinit();
    try std.testing.expectEqual(Consumer{ .terminator = entry }, branch_plan.consumer(call_id).?);

    blocks[0].terminator = .{ .return_values = &.{result} };
    program.blocks = &blocks;
    var return_plan = try planForTest(std.testing.allocator, &program);
    defer return_plan.deinit();
    try std.testing.expectEqual(Consumer{ .terminator = entry }, return_plan.consumer(call_id).?);
}

test "effectful values cross terminator place snapshots only in operand order" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const table_get_id = ir.InstructionId.fromIndex(0);
    const place_read_id = ir.InstructionId.fromIndex(1);
    const table = ir.ValueId.fromIndex(0);
    const key = ir.ValueId.fromIndex(1);
    const table_result = ir.ValueId.fromIndex(2);
    const place_result = ir.ValueId.fromIndex(3);
    const place_id = ir.PlaceId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = table, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = key, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = table_result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = table_get_id, .index = 0 } } },
        .{ .id = place_result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = place_read_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = table_get_id, .block = block_id, .operation = .{ .table_get = .{ .table = table, .key = key } }, .results = &.{table_result}, .effects = .semantic_table_read },
        .{ .id = place_read_id, .block = block_id, .operation = .{ .place_read = place_id }, .results = &.{place_result}, .effects = .place_read },
    };
    const places = [_]ir.Place{.{ .id = place_id, .function = function_id, .origin = .{ .local = 0 } }};
    var blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ table_get_id, place_read_id },
        .terminator = .{ .return_values = &.{ table_result, place_result } },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ table, key },
        .local_places = &.{place_id},
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    var program: ir.Program = .{
        .program_id = "value-fusion-ordered-terminator-reads",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };

    var ordered = try planForTest(std.testing.allocator, &program);
    defer ordered.deinit();
    try std.testing.expectEqual(Consumer{ .terminator = block_id }, ordered.consumer(table_get_id).?);

    blocks[0].terminator = .{ .return_values = &.{ place_result, table_result } };
    program.blocks = &blocks;
    var reversed = try planForTest(std.testing.allocator, &program);
    defer reversed.deinit();
    try std.testing.expect(reversed.consumer(table_get_id) == null);
}

test "effectful sibling producers fuse only in consumer operand order" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const first_call_id = ir.InstructionId.fromIndex(0);
    const second_call_id = ir.InstructionId.fromIndex(1);
    const binary_id = ir.InstructionId.fromIndex(2);
    const first_callee = ir.ValueId.fromIndex(0);
    const second_callee = ir.ValueId.fromIndex(1);
    const first_result = ir.ValueId.fromIndex(2);
    const second_result = ir.ValueId.fromIndex(3);
    const binary_result = ir.ValueId.fromIndex(4);
    const values = [_]ir.Value{
        .{ .id = first_callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = second_callee, .function = function_id, .type = .function, .origin = .{ .parameter = 1 } },
        .{ .id = first_result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = first_call_id, .index = 0 } } },
        .{ .id = second_result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = second_call_id, .index = 0 } } },
        .{ .id = binary_result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = binary_id, .index = 0 } } },
    };
    var instructions = [_]ir.Instruction{
        .{ .id = first_call_id, .block = block_id, .operation = .{ .call = .{ .callee = first_callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{first_result}, .effects = .dynamic_call },
        .{ .id = second_call_id, .block = block_id, .operation = .{ .call = .{ .callee = second_callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{second_result}, .effects = .dynamic_call },
        .{ .id = binary_id, .block = block_id, .operation = .{ .binary = .{ .operator = .add, .left = first_result, .right = second_result } }, .results = &.{binary_result}, .effects = .dynamic_call },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ first_call_id, second_call_id, binary_id },
        .terminator = .{ .return_values = &.{binary_result} },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ first_callee, second_callee },
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    var program: ir.Program = .{
        .program_id = "value-fusion-ordered-siblings",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var ordered = try planForTest(std.testing.allocator, &program);
    defer ordered.deinit();
    try std.testing.expectEqual(Consumer{ .instruction = binary_id }, ordered.consumer(first_call_id).?);
    try std.testing.expectEqual(Consumer{ .instruction = binary_id }, ordered.consumer(second_call_id).?);
    try std.testing.expectEqual(Consumer{ .terminator = block_id }, ordered.consumer(binary_id).?);

    instructions[binary_id.index()].operation.binary = .{ .operator = .add, .left = second_result, .right = first_result };
    program.instructions = &instructions;
    var reversed = try planForTest(std.testing.allocator, &program);
    defer reversed.deinit();
    try std.testing.expect(reversed.consumer(first_call_id) == null);
    try std.testing.expectEqual(Consumer{ .instruction = binary_id }, reversed.consumer(second_call_id).?);
}

test "effectful producers cross ordered nested fusion chains" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const first_call_id = ir.InstructionId.fromIndex(0);
    const second_call_id = ir.InstructionId.fromIndex(1);
    const unary_id = ir.InstructionId.fromIndex(2);
    const binary_id = ir.InstructionId.fromIndex(3);
    const first_callee = ir.ValueId.fromIndex(0);
    const second_callee = ir.ValueId.fromIndex(1);
    const first_result = ir.ValueId.fromIndex(2);
    const second_result = ir.ValueId.fromIndex(3);
    const unary_result = ir.ValueId.fromIndex(4);
    const binary_result = ir.ValueId.fromIndex(5);
    const values = [_]ir.Value{
        .{ .id = first_callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = second_callee, .function = function_id, .type = .function, .origin = .{ .parameter = 1 } },
        .{ .id = first_result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = first_call_id, .index = 0 } } },
        .{ .id = second_result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = second_call_id, .index = 0 } } },
        .{ .id = unary_result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = unary_id, .index = 0 } } },
        .{ .id = binary_result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = binary_id, .index = 0 } } },
    };
    var instructions = [_]ir.Instruction{
        .{ .id = first_call_id, .block = block_id, .operation = .{ .call = .{ .callee = first_callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{first_result}, .effects = .dynamic_call },
        .{ .id = second_call_id, .block = block_id, .operation = .{ .call = .{ .callee = second_callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{second_result}, .effects = .dynamic_call },
        .{ .id = unary_id, .block = block_id, .operation = .{ .unary = .{ .operator = .negate, .operand = second_result } }, .results = &.{unary_result}, .effects = .dynamic_call },
        .{ .id = binary_id, .block = block_id, .operation = .{ .binary = .{ .operator = .add, .left = first_result, .right = unary_result } }, .results = &.{binary_result}, .effects = .dynamic_call },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ first_call_id, second_call_id, unary_id, binary_id },
        .terminator = .{ .return_values = &.{binary_result} },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ first_callee, second_callee },
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    var program: ir.Program = .{
        .program_id = "value-fusion-transitive-ordered-gap",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var ordered = try planForTest(std.testing.allocator, &program);
    defer ordered.deinit();
    try std.testing.expectEqual(Consumer{ .instruction = binary_id }, ordered.consumer(first_call_id).?);
    try std.testing.expectEqual(Consumer{ .instruction = unary_id }, ordered.consumer(second_call_id).?);
    try std.testing.expectEqual(Consumer{ .instruction = binary_id }, ordered.consumer(unary_id).?);

    instructions[binary_id.index()].operation.binary = .{ .operator = .add, .left = unary_result, .right = first_result };
    program.instructions = &instructions;
    var reversed = try planForTest(std.testing.allocator, &program);
    defer reversed.deinit();
    try std.testing.expect(reversed.consumer(first_call_id) == null);
}

test "effectful receiver crosses a fused variadic argument pack" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const receiver_call_id = ir.InstructionId.fromIndex(0);
    const argument_call_id = ir.InstructionId.fromIndex(1);
    const namecall_id = ir.InstructionId.fromIndex(2);
    const receiver_callee = ir.ValueId.fromIndex(0);
    const argument_callee = ir.ValueId.fromIndex(1);
    const receiver = ir.ValueId.fromIndex(2);
    const result = ir.ValueId.fromIndex(3);
    const argument_pack = ir.ValuePackId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = receiver_callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = argument_callee, .function = function_id, .type = .function, .origin = .{ .parameter = 1 } },
        .{ .id = receiver, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = receiver_call_id, .index = 0 } } },
        .{ .id = result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = namecall_id, .index = 0 } } },
    };
    const value_packs = [_]ir.ValuePack{.{
        .id = argument_pack,
        .function = function_id,
        .origin = .{ .instruction_result = argument_call_id },
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = receiver_call_id, .block = block_id, .operation = .{ .call = .{ .callee = receiver_callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{receiver}, .effects = .dynamic_call },
        .{ .id = argument_call_id, .block = block_id, .operation = .{ .call = .{ .callee = argument_callee, .arguments = &.{}, .result_arity = .{ .variadic = {} } } }, .results = &.{}, .pack_result = argument_pack, .effects = .dynamic_call },
        .{ .id = namecall_id, .block = block_id, .operation = .{ .namecall = .{ .receiver = receiver, .method = "apply", .arguments = &.{}, .argument_pack = argument_pack, .result_arity = .{ .fixed = 1 } } }, .results = &.{result}, .effects = .namecall },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ receiver_call_id, argument_call_id, namecall_id },
        .terminator = .{ .return_values = &.{result} },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ receiver_callee, argument_callee },
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "value-fusion-ordered-pack-gap",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &value_packs,
    };

    var plan = try planForTest(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqual(Consumer{ .instruction = namecall_id }, plan.consumer(receiver_call_id).?);
}

test "value fusion refuses direct multi-use and branch edge-only uses" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const then_block = ir.BlockId.fromIndex(1);
    const else_block = ir.BlockId.fromIndex(2);
    const call_id = ir.InstructionId.fromIndex(0);
    const condition = ir.ValueId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(1);
    const result = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 1 } },
        .{ .id = result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = call_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = call_id,
        .block = entry,
        .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } },
        .results = &.{result},
        .effects = .dynamic_call,
    }};
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{call_id}, .terminator = .{ .return_values = &.{ result, result } } },
        .{ .id = then_block, .function = function_id, .parameters = &.{result}, .instructions = &.{}, .terminator = .{ .return_values = &.{} } },
        .{ .id = else_block, .function = function_id, .instructions = &.{}, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .parameters = &.{ condition, callee }, .blocks = &.{ entry, then_block, else_block }, .entry_block = entry }};
    var program: ir.Program = .{
        .program_id = "value-fusion-refusals",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var multi_use = try planForTest(std.testing.allocator, &program);
    defer multi_use.deinit();
    try std.testing.expect(multi_use.consumer(call_id) == null);

    blocks[0].terminator = .{ .branch = .{
        .condition = condition,
        .then_edge = .{ .target = then_block, .arguments = &.{result} },
        .else_edge = .{ .target = else_block },
    } };
    program.blocks = &blocks;
    var edge_use = try planForTest(std.testing.allocator, &program);
    defer edge_use.deinit();
    try std.testing.expect(edge_use.consumer(call_id) == null);
}

test "value fusion keeps unconditional effects out of short-circuit right operands" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const call_id = ir.InstructionId.fromIndex(0);
    const binary_id = ir.InstructionId.fromIndex(1);
    const condition = ir.ValueId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(1);
    const effect_result = ir.ValueId.fromIndex(2);
    const binary_result = ir.ValueId.fromIndex(3);
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 1 } },
        .{ .id = effect_result, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = call_id, .index = 0 } } },
        .{ .id = binary_result, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = binary_id, .index = 0 } } },
    };
    var instructions = [_]ir.Instruction{
        .{ .id = call_id, .block = block_id, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{effect_result}, .effects = .dynamic_call },
        .{ .id = binary_id, .block = block_id, .operation = .{ .binary = .{ .operator = .logical_and, .left = condition, .right = effect_result } }, .results = &.{binary_result}, .effects = .pure },
    };
    const blocks = [_]ir.Block{.{ .id = block_id, .function = function_id, .instructions = &.{ call_id, binary_id }, .terminator = .{ .return_values = &.{ binary_result, binary_result } } }};
    const functions = [_]ir.Function{.{ .id = function_id, .parameters = &.{ condition, callee }, .blocks = &.{block_id}, .entry_block = block_id }};
    var program: ir.Program = .{
        .program_id = "value-fusion-short-circuit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var right_operand = try planForTest(std.testing.allocator, &program);
    defer right_operand.deinit();
    try std.testing.expect(right_operand.consumer(call_id) == null);

    instructions[1].operation = .{ .binary = .{ .operator = .logical_and, .left = effect_result, .right = condition } };
    program.instructions = &instructions;
    var left_operand = try planForTest(std.testing.allocator, &program);
    defer left_operand.deinit();
    try std.testing.expectEqual(Consumer{ .instruction = binary_id }, left_operand.consumer(call_id).?);
}

test "value fusion crosses pure gaps and only evaluation-ordered fused reads" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const call_id = ir.InstructionId.fromIndex(0);
    const gap_id = ir.InstructionId.fromIndex(1);
    const binary_id = ir.InstructionId.fromIndex(2);
    const callee = ir.ValueId.fromIndex(0);
    const call_result = ir.ValueId.fromIndex(1);
    const gap_result = ir.ValueId.fromIndex(2);
    const binary_result = ir.ValueId.fromIndex(3);
    const place_id = ir.PlaceId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = call_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = call_id, .index = 0 } } },
        .{ .id = gap_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = gap_id, .index = 0 } } },
        .{ .id = binary_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = binary_id, .index = 0 } } },
    };
    var instructions = [_]ir.Instruction{
        .{ .id = call_id, .block = block_id, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{call_result}, .effects = .dynamic_call },
        .{ .id = gap_id, .block = block_id, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{gap_result}, .effects = .pure },
        .{ .id = binary_id, .block = block_id, .operation = .{ .binary = .{ .operator = .add, .left = call_result, .right = gap_result } }, .results = &.{binary_result}, .effects = .dynamic_call },
    };
    const places = [_]ir.Place{.{ .id = place_id, .function = function_id, .type = .integer, .origin = .{ .local = 0 } }};
    const blocks = [_]ir.Block{.{ .id = block_id, .function = function_id, .instructions = &.{ call_id, gap_id, binary_id }, .terminator = .{ .return_values = &.{ binary_result, binary_result } } }};
    const functions = [_]ir.Function{.{ .id = function_id, .parameters = &.{callee}, .local_places = &.{place_id}, .blocks = &.{block_id}, .entry_block = block_id }};
    var program: ir.Program = .{
        .program_id = "value-fusion-pure-gap",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };

    var pure_gap = try planForTest(std.testing.allocator, &program);
    defer pure_gap.deinit();
    try std.testing.expectEqual(Consumer{ .instruction = binary_id }, pure_gap.consumer(call_id).?);

    instructions[gap_id.index()].operation = .{ .place_read = place_id };
    instructions[gap_id.index()].effects = .place_read;
    program.instructions = &instructions;
    var memory_gap = try planForTest(std.testing.allocator, &program);
    defer memory_gap.deinit();
    try std.testing.expectEqual(Consumer{ .instruction = binary_id }, memory_gap.consumer(call_id).?);

    instructions[binary_id.index()].operation = .{ .binary = .{ .operator = .add, .left = gap_result, .right = call_result } };
    program.instructions = &instructions;
    var reordered_read = try planForTest(std.testing.allocator, &program);
    defer reordered_read.deinit();
    try std.testing.expect(reordered_read.consumer(call_id) == null);

    instructions[call_id.index()].operation = .{ .make_table_literal = .{ .fields = &.{}, .tail_pack = null } };
    instructions[call_id.index()].effects = .table_constructor;
    program.instructions = &instructions;
    var fresh_table = try planForTest(std.testing.allocator, &program);
    defer fresh_table.deinit();
    try std.testing.expectEqual(Consumer{ .instruction = binary_id }, fresh_table.consumer(call_id).?);
}

test "compound RHS fusion follows Luau RHS-before-target-read order" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const rhs_id = ir.InstructionId.fromIndex(0);
    const read_id = ir.InstructionId.fromIndex(1);
    const binary_id = ir.InstructionId.fromIndex(2);
    const write_id = ir.InstructionId.fromIndex(3);
    const callee = ir.ValueId.fromIndex(0);
    const rhs = ir.ValueId.fromIndex(1);
    const current = ir.ValueId.fromIndex(2);
    const updated = ir.ValueId.fromIndex(3);
    const place_id = ir.PlaceId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = rhs, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = rhs_id, .index = 0 } } },
        .{ .id = current, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } } },
        .{ .id = updated, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = binary_id, .index = 0 } } },
    };
    const places = [_]ir.Place{.{ .id = place_id, .function = function_id, .type = .integer, .origin = .{ .local = 0 } }};
    var instructions = [_]ir.Instruction{
        .{ .id = rhs_id, .block = block_id, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{rhs}, .effects = .dynamic_call },
        .{ .id = read_id, .block = block_id, .operation = .{ .place_read = place_id }, .results = &.{current}, .effects = .place_read },
        .{ .id = binary_id, .block = block_id, .operation = .{ .binary = .{ .operator = .add, .left = current, .right = rhs } }, .results = &.{updated}, .effects = .dynamic_call },
        .{ .id = write_id, .block = block_id, .operation = .{ .place_write = .{ .place = place_id, .value = updated } }, .results = &.{}, .effects = .place_write },
    };
    var blocks = [_]ir.Block{.{ .id = block_id, .function = function_id, .instructions = &.{ rhs_id, read_id, binary_id, write_id }, .terminator = .{ .return_values = &.{} } }};
    const functions = [_]ir.Function{.{ .id = function_id, .parameters = &.{callee}, .local_places = &.{place_id}, .blocks = &.{block_id}, .entry_block = block_id }};
    var program: ir.Program = .{
        .program_id = "compound-rhs-order",
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
    var writes = try place_write_fusion.Plan.init(std.testing.allocator, &program, &packs, &dead);
    defer writes.deinit();
    var reads = try place_read_fusion.Plan.init(std.testing.allocator, &program, &packs, &dead);
    defer reads.deinit();
    var fused = try Plan.init(std.testing.allocator, &program, &packs, &dead, &writes, &reads);
    defer fused.deinit();
    try std.testing.expectEqual(Consumer{ .instruction = binary_id }, fused.consumer(rhs_id).?);
    try std.testing.expect(compound_update.matchPlace(&program, &dead, &writes, &reads, instructions[binary_id.index()], instructions[write_id.index()]) != null);

    instructions[binary_id.index()].effects = .pure;
    program.instructions = &instructions;
    var exact_packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer exact_packs.deinit();
    var exact_dead = try dead_code.Plan.init(std.testing.allocator, &program, &exact_packs);
    defer exact_dead.deinit();
    var exact_writes = try place_write_fusion.Plan.init(std.testing.allocator, &program, &exact_packs, &exact_dead);
    defer exact_writes.deinit();
    var exact_reads = try place_read_fusion.Plan.init(std.testing.allocator, &program, &exact_packs, &exact_dead);
    defer exact_reads.deinit();
    try std.testing.expect(exact_dead.isInlined(binary_id));
    try std.testing.expectEqual(binary_id, exact_writes.producerForWrite(write_id).?);
    try std.testing.expectEqual(place_read_fusion.Consumer{ .instruction = write_id }, exact_reads.consumer(read_id).?);
    try std.testing.expect(compound_update.matchPlace(&program, &exact_dead, &exact_writes, &exact_reads, instructions[binary_id.index()], instructions[write_id.index()]) != null);

    instructions[binary_id.index()].effects = .dynamic_call;
    blocks[0].instructions = &.{ read_id, rhs_id, binary_id, write_id };
    program.instructions = &instructions;
    program.blocks = &blocks;
    var read_first_packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer read_first_packs.deinit();
    var read_first_dead = try dead_code.Plan.init(std.testing.allocator, &program, &read_first_packs);
    defer read_first_dead.deinit();
    var read_first_writes = try place_write_fusion.Plan.init(std.testing.allocator, &program, &read_first_packs, &read_first_dead);
    defer read_first_writes.deinit();
    var read_first_reads = try place_read_fusion.Plan.init(std.testing.allocator, &program, &read_first_packs, &read_first_dead);
    defer read_first_reads.deinit();
    var read_first_fused = try Plan.init(std.testing.allocator, &program, &read_first_packs, &read_first_dead, &read_first_writes, &read_first_reads);
    defer read_first_fused.deinit();
    try std.testing.expectEqual(Consumer{ .instruction = binary_id }, read_first_fused.consumer(rhs_id).?);
    try std.testing.expect(compound_update.matchPlace(&program, &read_first_dead, &read_first_writes, &read_first_reads, instructions[binary_id.index()], instructions[write_id.index()]) == null);
}

test "effectful producers cross a fused open pack at a later hop of the gap walk" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);

    // `h(t(g()), x)` with `x` called first: the gap chain `g()`, `t(...)` reaches `h` at an earlier operand than
    // `x`, so `x` would run after both calls if it fused, and it stays a local.
    {
        const x_call = ir.InstructionId.fromIndex(0);
        const g_call = ir.InstructionId.fromIndex(1);
        const t_call = ir.InstructionId.fromIndex(2);
        const h_call = ir.InstructionId.fromIndex(3);
        const ph = ir.ValueId.fromIndex(0);
        const pt = ir.ValueId.fromIndex(1);
        const pg = ir.ValueId.fromIndex(2);
        const px = ir.ValueId.fromIndex(3);
        const x = ir.ValueId.fromIndex(4);
        const t = ir.ValueId.fromIndex(5);
        const result = ir.ValueId.fromIndex(6);
        const g_pack = ir.ValuePackId.fromIndex(0);
        const values = [_]ir.Value{
            .{ .id = ph, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
            .{ .id = pt, .function = function_id, .type = .function, .origin = .{ .parameter = 1 } },
            .{ .id = pg, .function = function_id, .type = .function, .origin = .{ .parameter = 2 } },
            .{ .id = px, .function = function_id, .type = .function, .origin = .{ .parameter = 3 } },
            .{ .id = x, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = x_call, .index = 0 } } },
            .{ .id = t, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = t_call, .index = 0 } } },
            .{ .id = result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = h_call, .index = 0 } } },
        };
        const value_packs = [_]ir.ValuePack{
            .{ .id = g_pack, .function = function_id, .origin = .{ .instruction_result = g_call } },
        };
        const instructions = [_]ir.Instruction{
            .{ .id = x_call, .block = block_id, .operation = .{ .call = .{ .callee = px, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{x}, .effects = .dynamic_call },
            .{ .id = g_call, .block = block_id, .operation = .{ .call = .{ .callee = pg, .arguments = &.{}, .result_arity = .{ .variadic = {} } } }, .results = &.{}, .pack_result = g_pack, .effects = .dynamic_call },
            .{ .id = t_call, .block = block_id, .operation = .{ .call = .{ .callee = pt, .arguments = &.{}, .argument_pack = g_pack, .result_arity = .{ .fixed = 1 } } }, .results = &.{t}, .effects = .dynamic_call },
            .{ .id = h_call, .block = block_id, .operation = .{ .call = .{ .callee = ph, .arguments = &.{ t, x }, .result_arity = .{ .fixed = 1 } } }, .results = &.{result}, .effects = .dynamic_call },
        };
        const blocks = [_]ir.Block{.{
            .id = block_id,
            .function = function_id,
            .instructions = &.{ x_call, g_call, t_call, h_call },
            .terminator = .{ .return_values = &.{result} },
        }};
        const functions = [_]ir.Function{.{
            .id = function_id,
            .parameters = &.{ ph, pt, pg, px },
            .blocks = &.{block_id},
            .entry_block = block_id,
        }};
        const program: ir.Program = .{
            .program_id = "value-fusion-pack-chain-operand-order",
            .entry_function = function_id,
            .functions = &functions,
            .blocks = &blocks,
            .instructions = &instructions,
            .values = &values,
            .value_packs = &value_packs,
        };

        var plan = try planForTest(std.testing.allocator, &program);
        defer plan.deinit();
        try std.testing.expect(plan.consumer(x_call) == null);
    }

    // `h(f(k(g())), x)` with `x` called first: the gap walk passes the fused open pack of `k(...)` and reaches `h`
    // at `f`'s operand, which comes before `x`, so `x` still stays a local.
    {
        const x_call = ir.InstructionId.fromIndex(0);
        const g_call = ir.InstructionId.fromIndex(1);
        const k_call = ir.InstructionId.fromIndex(2);
        const f_call = ir.InstructionId.fromIndex(3);
        const h_call = ir.InstructionId.fromIndex(4);
        const ph = ir.ValueId.fromIndex(0);
        const pf = ir.ValueId.fromIndex(1);
        const pk = ir.ValueId.fromIndex(2);
        const pg = ir.ValueId.fromIndex(3);
        const px = ir.ValueId.fromIndex(4);
        const x = ir.ValueId.fromIndex(5);
        const f = ir.ValueId.fromIndex(6);
        const result = ir.ValueId.fromIndex(7);
        const g_pack = ir.ValuePackId.fromIndex(0);
        const k_pack = ir.ValuePackId.fromIndex(1);
        const values = [_]ir.Value{
            .{ .id = ph, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
            .{ .id = pf, .function = function_id, .type = .function, .origin = .{ .parameter = 1 } },
            .{ .id = pk, .function = function_id, .type = .function, .origin = .{ .parameter = 2 } },
            .{ .id = pg, .function = function_id, .type = .function, .origin = .{ .parameter = 3 } },
            .{ .id = px, .function = function_id, .type = .function, .origin = .{ .parameter = 4 } },
            .{ .id = x, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = x_call, .index = 0 } } },
            .{ .id = f, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = f_call, .index = 0 } } },
            .{ .id = result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = h_call, .index = 0 } } },
        };
        const value_packs = [_]ir.ValuePack{
            .{ .id = g_pack, .function = function_id, .origin = .{ .instruction_result = g_call } },
            .{ .id = k_pack, .function = function_id, .origin = .{ .instruction_result = k_call } },
        };
        const instructions = [_]ir.Instruction{
            .{ .id = x_call, .block = block_id, .operation = .{ .call = .{ .callee = px, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{x}, .effects = .dynamic_call },
            .{ .id = g_call, .block = block_id, .operation = .{ .call = .{ .callee = pg, .arguments = &.{}, .result_arity = .{ .variadic = {} } } }, .results = &.{}, .pack_result = g_pack, .effects = .dynamic_call },
            .{ .id = k_call, .block = block_id, .operation = .{ .call = .{ .callee = pk, .arguments = &.{}, .argument_pack = g_pack, .result_arity = .{ .variadic = {} } } }, .results = &.{}, .pack_result = k_pack, .effects = .dynamic_call },
            .{ .id = f_call, .block = block_id, .operation = .{ .call = .{ .callee = pf, .arguments = &.{}, .argument_pack = k_pack, .result_arity = .{ .fixed = 1 } } }, .results = &.{f}, .effects = .dynamic_call },
            .{ .id = h_call, .block = block_id, .operation = .{ .call = .{ .callee = ph, .arguments = &.{ f, x }, .result_arity = .{ .fixed = 1 } } }, .results = &.{result}, .effects = .dynamic_call },
        };
        const blocks = [_]ir.Block{.{
            .id = block_id,
            .function = function_id,
            .instructions = &.{ x_call, g_call, k_call, f_call, h_call },
            .terminator = .{ .return_values = &.{result} },
        }};
        const functions = [_]ir.Function{.{
            .id = function_id,
            .parameters = &.{ ph, pf, pk, pg, px },
            .blocks = &.{block_id},
            .entry_block = block_id,
        }};
        const program: ir.Program = .{
            .program_id = "value-fusion-later-pack-hop-operand-order",
            .entry_function = function_id,
            .functions = &functions,
            .blocks = &blocks,
            .instructions = &instructions,
            .values = &values,
            .value_packs = &value_packs,
        };

        var plan = try planForTest(std.testing.allocator, &program);
        defer plan.deinit();
        try std.testing.expect(plan.consumer(x_call) == null);
    }

    // `callee(inner_callee())` where `callee` and `inner_callee` come from two calls in that order: the gap
    // `inner_callee`'s call fuses into the open-pack call `inner`, whose pack fuses into `outer`. Luau evaluates the
    // callee before the arguments, so the walk continues through the pack at its second hop and `callee` fuses.
    {
        const producer = ir.InstructionId.fromIndex(0);
        const gap = ir.InstructionId.fromIndex(1);
        const inner = ir.InstructionId.fromIndex(2);
        const outer = ir.InstructionId.fromIndex(3);
        const p0 = ir.ValueId.fromIndex(0);
        const p1 = ir.ValueId.fromIndex(1);
        const callee = ir.ValueId.fromIndex(2);
        const inner_callee = ir.ValueId.fromIndex(3);
        const result = ir.ValueId.fromIndex(4);
        const inner_pack = ir.ValuePackId.fromIndex(0);
        const values = [_]ir.Value{
            .{ .id = p0, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
            .{ .id = p1, .function = function_id, .type = .function, .origin = .{ .parameter = 1 } },
            .{ .id = callee, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = producer, .index = 0 } } },
            .{ .id = inner_callee, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = gap, .index = 0 } } },
            .{ .id = result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = outer, .index = 0 } } },
        };
        const value_packs = [_]ir.ValuePack{
            .{ .id = inner_pack, .function = function_id, .origin = .{ .instruction_result = inner } },
        };
        const instructions = [_]ir.Instruction{
            .{ .id = producer, .block = block_id, .operation = .{ .call = .{ .callee = p0, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{callee}, .effects = .dynamic_call },
            .{ .id = gap, .block = block_id, .operation = .{ .call = .{ .callee = p1, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } }, .results = &.{inner_callee}, .effects = .dynamic_call },
            .{ .id = inner, .block = block_id, .operation = .{ .call = .{ .callee = inner_callee, .arguments = &.{}, .result_arity = .{ .variadic = {} } } }, .results = &.{}, .pack_result = inner_pack, .effects = .dynamic_call },
            .{ .id = outer, .block = block_id, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .argument_pack = inner_pack, .result_arity = .{ .fixed = 1 } } }, .results = &.{result}, .effects = .dynamic_call },
        };
        const blocks = [_]ir.Block{.{
            .id = block_id,
            .function = function_id,
            .instructions = &.{ producer, gap, inner, outer },
            .terminator = .{ .return_values = &.{result} },
        }};
        const functions = [_]ir.Function{.{
            .id = function_id,
            .parameters = &.{ p0, p1 },
            .blocks = &.{block_id},
            .entry_block = block_id,
        }};
        const program: ir.Program = .{
            .program_id = "value-fusion-later-pack-hop",
            .entry_function = function_id,
            .functions = &functions,
            .blocks = &blocks,
            .instructions = &instructions,
            .values = &values,
            .value_packs = &value_packs,
        };

        var packs = try pack_plan.Plan.init(std.testing.allocator, &program);
        defer packs.deinit();
        try std.testing.expectEqual(pack_plan.InstructionRole{ .fused_invocation_producer = outer }, packs.role(inner));
        var plan = try planForTest(std.testing.allocator, &program);
        defer plan.deinit();
        try std.testing.expectEqual(@as(?Consumer, Consumer{ .instruction = inner }), plan.consumer(gap));
        try std.testing.expectEqual(@as(?Consumer, Consumer{ .instruction = outer }), plan.consumer(producer));
    }
}
