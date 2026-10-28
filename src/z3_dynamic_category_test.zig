const std = @import("std");
const lifter = @import("semantic_lifter");
const ir = lifter.ir;
const defaultBackend = lifter.z3_backend.defaultBackend;

fn dynamicIdentity(binding: ir.SolverModelBinding) u32 {
    return switch (binding.value) {
        .dynamic_identity => |identity| identity,
        else => unreachable,
    };
}

test "Z3 preserves equality of independently defined exact strings" {
    const fixture = lifter.fixtures.automatic_promotion_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_unreachable.index()].operation = .{ .constant = .{ .string = "matched" } };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_matched } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_unreachable } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) };

    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqual(@as(usize, 0), result.model.items.len);

    const model_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    var model_result = try defaultBackend().solve(std.testing.allocator, &program, model_query);
    defer model_result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, model_result.resolution);
    try std.testing.expectEqual(@as(usize, 2), model_result.model.items.len);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(model_result.model.items[0]));
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(model_result.model.items[1]));
}

test "Z3 preserves exact concatenated string length identity" {
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const concatenated = ir.ValueId.fromIndex(2);
    const length = ir.ValueId.fromIndex(3);
    const expected = ir.ValueId.fromIndex(4);
    const values = [_]ir.Value{
        .{ .id = left, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = right, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = concatenated, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = length, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = expected, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "ab" } }, .results = &.{left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "cd" } }, .results = &.{right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .concat, .left = left, .right = right } }, .results = &.{concatenated}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .length, .operand = concatenated } }, .results = &.{length}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "4" } }, .results = &.{expected}, .effects = .pure },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = length } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = expected } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
    };
    const program: ir.Program = .{
        .program_id = "z3-exact-string-length-identity",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) };
    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);

    const model_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    var model_result = try defaultBackend().solve(std.testing.allocator, &program, model_query);
    defer model_result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, model_result.resolution);
    try std.testing.expectEqual(@as(usize, 2), model_result.model.items.len);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(model_result.model.items[0]));
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(model_result.model.items[1]));
}

test "Z3 preserves exact primitive bitwise result identity" {
    const fixture = lifter.fixtures.arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };
    var values = fixture.values;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation = .{ .constant = .{ .integer = "305419896" } };
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .bit_and,
        .left = fixture.v_sum,
        .right = fixture.v_sum,
        .mode = .primitive,
    } };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_result } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_sum } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
    };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) };
    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);

    const model_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    var model_result = try defaultBackend().solve(std.testing.allocator, &program, model_query);
    defer model_result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, model_result.resolution);
    try std.testing.expectEqual(@as(usize, 2), model_result.model.items.len);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(model_result.model.items[0]));
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(model_result.model.items[1]));
    try std.testing.expectEqual(
        lifter.solver_model.Replay.satisfied,
        try lifter.solver_model.replayAlloc(std.testing.allocator, &program, model_query, model_result.model.items),
    );
}

test "Z3 preserves inequality of distinct exact strings" {
    const fixture = lifter.fixtures.automatic_promotion_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_matched } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_unreachable } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_false, .goal = ir.SolverTermId.fromIndex(2) };

    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqual(@as(usize, 0), result.model.items.len);

    const countermodel_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) };
    var countermodel = try defaultBackend().solve(std.testing.allocator, &program, countermodel_query);
    defer countermodel.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.disproved, countermodel.resolution);
    try std.testing.expectEqual(@as(usize, 2), countermodel.model.items.len);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(countermodel.model.items[0]));
    try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(countermodel.model.items[1]));
}

test "Z3 separates static dynamic categories without constraining possible aliases" {
    const nil_value = ir.ValueId.fromIndex(0);
    const table_left = ir.ValueId.fromIndex(1);
    const function_value = ir.ValueId.fromIndex(2);
    const table_right = ir.ValueId.fromIndex(3);
    const unknown_value = ir.ValueId.fromIndex(4);
    const thread_left = ir.ValueId.fromIndex(5);
    const thread_right = ir.ValueId.fromIndex(6);
    const function_right = ir.ValueId.fromIndex(7);
    const values = [_]ir.Value{
        .{ .id = nil_value, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .nil_value }, .origin = .{ .parameter = 0 } },
        .{ .id = table_left, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .table }, .origin = .{ .parameter = 1 } },
        .{ .id = function_value, .function = ir.FunctionId.fromIndex(0), .type = .function, .origin = .{ .parameter = 2 } },
        .{ .id = table_right, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .table }, .origin = .{ .parameter = 3 } },
        .{ .id = unknown_value, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .parameter = 4 } },
        .{ .id = thread_left, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .thread }, .origin = .{ .parameter = 5 } },
        .{ .id = thread_right, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .thread }, .origin = .{ .parameter = 6 } },
        .{ .id = function_right, .function = ir.FunctionId.fromIndex(0), .type = .function, .origin = .{ .parameter = 7 } },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = nil_value } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = table_left } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = function_value } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = table_right } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = unknown_value } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(4),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = thread_left } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = thread_right } },
        .{ .id = ir.SolverTermId.fromIndex(11), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(9),
            .right = ir.SolverTermId.fromIndex(10),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(12), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = function_right } },
        .{ .id = ir.SolverTermId.fromIndex(13), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(2),
            .right = ir.SolverTermId.fromIndex(12),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "z3-dynamic-static-categories",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
    };

    const nil_table_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_false, .goal = ir.SolverTermId.fromIndex(5) };
    var nil_table = try defaultBackend().solve(std.testing.allocator, &program, nil_table_query);
    defer nil_table.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, nil_table.resolution);

    const table_function_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_false, .goal = ir.SolverTermId.fromIndex(6) };
    var table_function = try defaultBackend().solve(std.testing.allocator, &program, table_function_query);
    defer table_function.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, table_function.resolution);

    const table_alias_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(7) };
    var table_alias = try defaultBackend().solve(std.testing.allocator, &program, table_alias_query);
    defer table_alias.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, table_alias.resolution);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(table_alias.model.items[0]));
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(table_alias.model.items[1]));

    const table_distinct_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(7) };
    var table_distinct = try defaultBackend().solve(std.testing.allocator, &program, table_distinct_query);
    defer table_distinct.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.disproved, table_distinct.resolution);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(table_distinct.model.items[0]));
    try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(table_distinct.model.items[1]));

    const unknown_alias_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(8) };
    var unknown_alias = try defaultBackend().solve(std.testing.allocator, &program, unknown_alias_query);
    defer unknown_alias.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, unknown_alias.resolution);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(unknown_alias.model.items[0]));
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(unknown_alias.model.items[1]));

    const unknown_distinct_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(8) };
    var unknown_distinct = try defaultBackend().solve(std.testing.allocator, &program, unknown_distinct_query);
    defer unknown_distinct.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.disproved, unknown_distinct.resolution);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(unknown_distinct.model.items[0]));
    try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(unknown_distinct.model.items[1]));

    const thread_alias_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(11) };
    var thread_alias = try defaultBackend().solve(std.testing.allocator, &program, thread_alias_query);
    defer thread_alias.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, thread_alias.resolution);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(thread_alias.model.items[0]));
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(thread_alias.model.items[1]));

    const thread_distinct_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(11) };
    var thread_distinct = try defaultBackend().solve(std.testing.allocator, &program, thread_distinct_query);
    defer thread_distinct.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.disproved, thread_distinct.resolution);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(thread_distinct.model.items[0]));
    try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(thread_distinct.model.items[1]));

    const function_alias_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(13) };
    var function_alias = try defaultBackend().solve(std.testing.allocator, &program, function_alias_query);
    defer function_alias.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, function_alias.resolution);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(function_alias.model.items[0]));
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(function_alias.model.items[1]));

    const function_distinct_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(13) };
    var function_distinct = try defaultBackend().solve(std.testing.allocator, &program, function_distinct_query);
    defer function_distinct.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.disproved, function_distinct.resolution);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(function_distinct.model.items[0]));
    try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(function_distinct.model.items[1]));
}

test "Z3 preserves canonical function reference identities" {
    const fixture = lifter.fixtures.function_reference_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_left_a } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_left_b } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_left_copy } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_right } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = .{ .kind = .dynamic_value }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(8),
            .then_term = ir.SolverTermId.fromIndex(0),
            .else_term = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(9),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(11), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = false } },
        .{ .id = ir.SolverTermId.fromIndex(12), .sort = .{ .kind = .dynamic_value }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(11),
            .then_term = ir.SolverTermId.fromIndex(0),
            .else_term = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(13), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(12),
            .right = ir.SolverTermId.fromIndex(3),
        } } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    var report = try lifter.validate.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());

    for ([_]usize{ 4, 5, 7, 10, 13 }) |goal_index| {
        var result = try defaultBackend().solve(std.testing.allocator, &program, .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .goal = ir.SolverTermId.fromIndex(goal_index),
        });
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    }

    var different = try defaultBackend().solve(std.testing.allocator, &program, .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_false,
        .goal = ir.SolverTermId.fromIndex(6),
    });
    defer different.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, different.resolution);

    var same_model = try defaultBackend().solve(std.testing.allocator, &program, .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .find_model,
        .goal = ir.SolverTermId.fromIndex(4),
    });
    defer same_model.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, same_model.resolution);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(same_model.model.items[0]));
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(same_model.model.items[1]));

    var different_model = try defaultBackend().solve(std.testing.allocator, &program, .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .find_model,
        .goal = ir.SolverTermId.fromIndex(7),
    });
    defer different_model.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, different_model.resolution);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(different_model.model.items[0]));
    try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(different_model.model.items[1]));
}

test "Z3 preserves dynamic copy identity and copied static category" {
    const source_table = ir.ValueId.fromIndex(0);
    const copied_table = ir.ValueId.fromIndex(1);
    const nil_value = ir.ValueId.fromIndex(2);
    const copy_instruction = ir.InstructionId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = source_table, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .table }, .origin = .{ .parameter = 0 } },
        .{ .id = copied_table, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = copy_instruction, .index = 0 } } },
        .{ .id = nil_value, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .nil_value }, .origin = .{ .parameter = 1 } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = copy_instruction,
        .block = ir.BlockId.fromIndex(0),
        .operation = .{ .copy = source_table },
        .results = &.{copied_table},
        .effects = .pure,
    }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = source_table } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = copied_table } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = nil_value } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "z3-dynamic-copy-category",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };

    const identity_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(3) };
    var identity = try defaultBackend().solve(std.testing.allocator, &program, identity_query);
    defer identity.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, identity.resolution);

    const model_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(3) };
    var model = try defaultBackend().solve(std.testing.allocator, &program, model_query);
    defer model.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, model.resolution);
    try std.testing.expectEqual(@as(usize, 2), model.model.items.len);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(model.model.items[0]));
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(model.model.items[1]));
    try std.testing.expectEqual(
        lifter.solver_model.Replay.satisfied,
        try lifter.solver_model.replayAlloc(std.testing.allocator, &program, model_query, model.model.items),
    );

    const category_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_false, .goal = ir.SolverTermId.fromIndex(4) };
    var category = try defaultBackend().solve(std.testing.allocator, &program, category_query);
    defer category.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, category.resolution);
}

test "Z3 interns statically nil values into one identity" {
    const left_value = ir.ValueId.fromIndex(0);
    const right_value = ir.ValueId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = left_value, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .nil_value }, .origin = .{ .parameter = 0 } },
        .{ .id = right_value, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .nil_value }, .origin = .{ .parameter = 1 } },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = left_value } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = right_value } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "z3-static-nil-identity",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
    };
    const proof_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) };
    var proof = try defaultBackend().solve(std.testing.allocator, &program, proof_query);
    defer proof.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, proof.resolution);

    const model_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    var model = try defaultBackend().solve(std.testing.allocator, &program, model_query);
    defer model.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, model.resolution);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(model.model.items[0]));
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(model.model.items[1]));
}

test "Z3 preserves exact dynamic Boolean and numeric relations" {
    const values = [_]ir.Value{
        .{ .id = ir.ValueId.fromIndex(0), .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = ir.ValueId.fromIndex(1), .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = ir.ValueId.fromIndex(2), .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = ir.ValueId.fromIndex(3), .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = ir.ValueId.fromIndex(4), .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = ir.ValueId.fromIndex(5), .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
        .{ .id = ir.ValueId.fromIndex(6), .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(6), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .boolean = true } }, .results = &.{ir.ValueId.fromIndex(0)}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .boolean = true } }, .results = &.{ir.ValueId.fromIndex(1)}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .boolean = false } }, .results = &.{ir.ValueId.fromIndex(2)}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "7" } }, .results = &.{ir.ValueId.fromIndex(3)}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 7.0 } }, .results = &.{ir.ValueId.fromIndex(4)}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(5), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 7.5 } }, .results = &.{ir.ValueId.fromIndex(5)}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(6), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "7" } }, .results = &.{ir.ValueId.fromIndex(6)}, .effects = .pure },
    };
    var terms: [13]ir.SolverTerm = undefined;
    for (values, 0..) |value, index| {
        terms[index] = .{ .id = ir.SolverTermId.fromIndex(index), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = value.id } };
    }
    const pairs = [_][2]usize{ .{ 0, 1 }, .{ 0, 2 }, .{ 3, 4 }, .{ 3, 5 }, .{ 0, 3 }, .{ 3, 6 } };
    for (pairs, values.len..) |pair, term_index| {
        terms[term_index] = .{ .id = ir.SolverTermId.fromIndex(term_index), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(pair[0]),
            .right = ir.SolverTermId.fromIndex(pair[1]),
        } } };
    }
    const program: ir.Program = .{
        .program_id = "z3-exact-dynamic-scalars",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };

    for ([_]usize{ 8, 10, 11, 12 }) |goal_index| {
        const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_false, .goal = ir.SolverTermId.fromIndex(goal_index) };
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    }

    for ([_]usize{ 7, 9 }) |goal_index| {
        const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(goal_index) };
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
        try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(result.model.items[0]));
        try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(result.model.items[1]));
    }

    for ([_]usize{ 7, 9 }) |goal_index| {
        const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(goal_index) };
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    }
}

test "Z3 constrains symbolic dynamic Booleans to two identities" {
    const boolean_values = [_]ir.ValueId{ ir.ValueId.fromIndex(0), ir.ValueId.fromIndex(1), ir.ValueId.fromIndex(2) };
    const copied_values = [_]ir.ValueId{ ir.ValueId.fromIndex(3), ir.ValueId.fromIndex(4), ir.ValueId.fromIndex(5) };
    const copy_results = [_][1]ir.ValueId{ .{copied_values[0]}, .{copied_values[1]}, .{copied_values[2]} };
    var values: [6]ir.Value = undefined;
    var instructions: [3]ir.Instruction = undefined;
    for (boolean_values, copied_values, 0..) |source, copied, index| {
        values[index] = .{ .id = source, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .parameter = @intCast(index) } };
        values[index + 3] = .{ .id = copied, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(index), .index = 0 } } };
        instructions[index] = .{ .id = ir.InstructionId.fromIndex(index), .block = ir.BlockId.fromIndex(0), .operation = .{ .copy = source }, .results = &copy_results[index], .effects = .pure };
    }
    var terms: [11]ir.SolverTerm = undefined;
    for (copied_values, 0..) |value, index| {
        terms[index] = .{ .id = ir.SolverTermId.fromIndex(index), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = value } };
    }
    const pairs = [_][2]usize{ .{ 0, 1 }, .{ 0, 2 }, .{ 1, 2 } };
    for (pairs, 3..) |pair, index| {
        terms[index] = .{ .id = ir.SolverTermId.fromIndex(index), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(pair[0]),
            .right = ir.SolverTermId.fromIndex(pair[1]),
        } } };
    }
    terms[6] = .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .logical_and, .left = ir.SolverTermId.fromIndex(3), .right = ir.SolverTermId.fromIndex(4) } } };
    terms[7] = .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .logical_and, .left = ir.SolverTermId.fromIndex(6), .right = ir.SolverTermId.fromIndex(5) } } };
    const block_id = ir.BlockId.fromIndex(0);
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = ir.FunctionId.fromIndex(0),
        .instructions = &.{ ir.InstructionId.fromIndex(0), ir.InstructionId.fromIndex(1), ir.InstructionId.fromIndex(2) },
        .terminator = .{ .return_values = &.{} },
    }};
    const functions = [_]ir.Function{.{
        .id = ir.FunctionId.fromIndex(0),
        .parameters = &boolean_values,
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "z3-symbolic-dynamic-booleans",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .solver_terms = terms[0..8],
    };

    const impossible_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_false, .goal = ir.SolverTermId.fromIndex(7) };
    var impossible = try defaultBackend().solve(std.testing.allocator, &program, impossible_query);
    defer impossible.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, impossible.resolution);

    const two_class_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(3) };
    var two_class = try defaultBackend().solve(std.testing.allocator, &program, two_class_query);
    defer two_class.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, two_class.resolution);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(two_class.model.items[0]));
    try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(two_class.model.items[1]));
}

test "Z3 preserves copied symbolic numeric identity and category" {
    const source = ir.ValueId.fromIndex(0);
    const first_copy = ir.ValueId.fromIndex(1);
    const second_copy = ir.ValueId.fromIndex(2);
    const string_value = ir.ValueId.fromIndex(3);
    const values = [_]ir.Value{
        .{ .id = source, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = first_copy, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = second_copy, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = string_value, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .copy = source }, .results = &.{first_copy}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .copy = source }, .results = &.{second_copy}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "numeric" } }, .results = &.{string_value}, .effects = .pure },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = first_copy } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = second_copy } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = string_value } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(2) } } },
    };
    const block_id = ir.BlockId.fromIndex(0);
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = ir.FunctionId.fromIndex(0),
        .instructions = &.{ ir.InstructionId.fromIndex(0), ir.InstructionId.fromIndex(1), ir.InstructionId.fromIndex(2) },
        .terminator = .{ .return_values = &.{} },
    }};
    const functions = [_]ir.Function{.{
        .id = ir.FunctionId.fromIndex(0),
        .parameters = &.{source},
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "z3-copied-symbolic-numeric",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };

    const identity_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(3) };
    var identity = try defaultBackend().solve(std.testing.allocator, &program, identity_query);
    defer identity.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, identity.resolution);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(identity.model.items[0]));
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(identity.model.items[1]));
    try std.testing.expectEqual(
        lifter.solver_model.Replay.satisfied,
        try lifter.solver_model.replayAlloc(std.testing.allocator, &program, identity_query, identity.model.items),
    );

    const category_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_false, .goal = ir.SolverTermId.fromIndex(4) };
    var category = try defaultBackend().solve(std.testing.allocator, &program, category_query);
    defer category.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, category.resolution);
}

test "Z3 refuses unresolved exact dynamic numeric models" {
    const values = [_]ir.Value{
        .{ .id = ir.ValueId.fromIndex(0), .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = ir.ValueId.fromIndex(1), .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "9007199254740992" } }, .results = &.{ir.ValueId.fromIndex(0)}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .special_number = .nan } }, .results = &.{ir.ValueId.fromIndex(1)}, .effects = .pure },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = ir.ValueId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = ir.ValueId.fromIndex(1) } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "z3-unresolved-dynamic-numerics",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };
    for ([_]ir.QueryKind{ .prove_true, .prove_false, .find_model }) |kind| {
        const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = kind, .goal = ir.SolverTermId.fromIndex(2) };
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.unknown, result.resolution);
        try std.testing.expectEqual(@as(usize, 0), result.model.items.len);
        try std.testing.expectEqual(@as(usize, 0), result.unsat_core.items.len);
    }
}

test "Z3 preserves fresh table and thread allocation identities" {
    const fixture = lifter.fixtures.fresh_reference_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_table_a } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_table_b } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_table_copy } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_thread_a } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_thread_b } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(3),
            .right = ir.SolverTermId.fromIndex(4),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(3),
            .right = ir.SolverTermId.fromIndex(4),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(11), .sort = .{ .kind = .dynamic_value }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(10),
            .then_term = ir.SolverTermId.fromIndex(0),
            .else_term = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(12), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(11),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(13), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = false } },
        .{ .id = ir.SolverTermId.fromIndex(14), .sort = .{ .kind = .dynamic_value }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(13),
            .then_term = ir.SolverTermId.fromIndex(0),
            .else_term = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(15), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(14),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    var report = try lifter.validate.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());

    for ([_]usize{ 5, 7 }) |goal_index| {
        const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_false, .goal = ir.SolverTermId.fromIndex(goal_index) };
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
        try std.testing.expectEqual(@as(usize, 0), result.model.items.len);
    }

    for ([_]usize{ 12, 15 }) |goal_index| {
        const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(goal_index) };
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    }

    const copy_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(6) };
    var copy_result = try defaultBackend().solve(std.testing.allocator, &program, copy_query);
    defer copy_result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, copy_result.resolution);
    try std.testing.expectEqual(@as(usize, 2), copy_result.model.items.len);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(copy_result.model.items[0]));
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(copy_result.model.items[1]));
    try std.testing.expectEqual(
        lifter.solver_model.Replay.satisfied,
        try lifter.solver_model.replayAlloc(std.testing.allocator, &program, copy_query, copy_result.model.items),
    );

    for ([_]usize{ 8, 9 }) |goal_index| {
        const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(goal_index) };
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
        try std.testing.expectEqual(@as(usize, 2), result.model.items.len);
        try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(result.model.items[0]));
        try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(result.model.items[1]));
        try std.testing.expectEqual(
            lifter.solver_model.Replay.satisfied,
            try lifter.solver_model.replayAlloc(std.testing.allocator, &program, query, result.model.items),
        );
    }
}
