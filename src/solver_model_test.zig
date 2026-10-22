const std = @import("std");
const ir = @import("ir.zig");
const solver_model = @import("solver_model.zig");
const validation = @import("validate.zig");

test "dynamic model replay preserves equality inequality and conditional selection" {
    const condition_value = ir.ValueId.fromIndex(0);
    const left_value = ir.ValueId.fromIndex(1);
    const right_value = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = condition_value, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = left_value, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = right_value, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .parameter = 2 } },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = left_value } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = right_value } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .value = condition_value } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .dynamic_value }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(2),
            .then_term = ir.SolverTermId.fromIndex(0),
            .else_term = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(5),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "dynamic-model-replay",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
    };
    const equal_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(3) };
    const unequal_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(4) };
    const selected_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(6) };
    const same = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 0 } },
    };
    const distinct_reordered = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 1 } },
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
    };

    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, equal_query, &same));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, equal_query, &distinct_reordered));
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, unequal_query, &distinct_reordered));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, unequal_query, &same));

    const selected_left = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .boolean = true } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 1 } },
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
    };
    const selected_right = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 1 } },
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .boolean = false } },
    };
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, selected_query, &selected_left));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, selected_query, &selected_right));
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, selected_query, &same));
}

test "dynamic model replay rejects noncanonical identity classes" {
    const left_value = ir.ValueId.fromIndex(0);
    const right_value = ir.ValueId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = left_value, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = right_value, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .parameter = 1 } },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = left_value } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = right_value } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "dynamic-model-canonical-classes",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    const gap = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 2 } },
    };
    const reversed_classes = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 1 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 0 } },
    };
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, query, &gap));
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, query, &reversed_classes));
}

test "artifact validation rejects noncanonical dynamic identity classes" {
    const fixture = @import("fixtures.zig").immutable_closure_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_export } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_adder } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const queries = [_]ir.SolverQuery{.{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) }};
    var bindings = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 1 } },
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
    };
    const models = [_]ir.SolverModel{.{
        .id = ir.SolverModelId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .bindings = &bindings,
        .evidence = &.{fixture.proof},
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.solver_models = &models;

    var canonical_report = try validation.validate(std.testing.allocator, &program, .core);
    defer canonical_report.deinit();
    try std.testing.expect(!canonical_report.contains(.invalid_solver_model_value));

    bindings[0].value = .{ .dynamic_identity = 2 };
    var gap_report = try validation.validate(std.testing.allocator, &program, .core);
    defer gap_report.deinit();
    try std.testing.expect(gap_report.contains(.invalid_solver_model_value));

    bindings[0].value = .{ .dynamic_identity = 0 };
    bindings[1].value = .{ .dynamic_identity = 1 };
    var order_report = try validation.validate(std.testing.allocator, &program, .core);
    defer order_report.deinit();
    try std.testing.expect(order_report.contains(.invalid_solver_model_value));
}

test "dynamic model replay rejects exact literal identity contradictions" {
    const fixture = @import("fixtures.zig").automatic_promotion_module;
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
    const equal_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    const same = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 0 } },
    };
    const distinct = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 1 } },
    };
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, equal_query, &same));
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, equal_query, &distinct));

    const queries = [_]ir.SolverQuery{equal_query};
    const models = [_]ir.SolverModel{.{
        .id = ir.SolverModelId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .bindings = &distinct,
        .evidence = &.{fixture.proof},
    }};
    program.queries = &queries;
    program.solver_models = &models;
    var tampered_report = try validation.validate(std.testing.allocator, &program, .core);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.invalid_solver_model_value));

    program.instructions = &fixture.instructions;
    program.queries = &.{};
    program.solver_models = &.{};
    const unequal_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) };
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, unequal_query, &distinct));
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, unequal_query, &same));
}

test "dynamic model replay preserves same-category alias freedom" {
    const table_left = ir.ValueId.fromIndex(0);
    const table_right = ir.ValueId.fromIndex(1);
    const function_value = ir.ValueId.fromIndex(2);
    const thread_left = ir.ValueId.fromIndex(3);
    const thread_right = ir.ValueId.fromIndex(4);
    const function_right = ir.ValueId.fromIndex(5);
    const values = [_]ir.Value{
        .{ .id = table_left, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .table }, .origin = .{ .parameter = 0 } },
        .{ .id = table_right, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .table }, .origin = .{ .parameter = 1 } },
        .{ .id = function_value, .function = ir.FunctionId.fromIndex(0), .type = .function, .origin = .{ .parameter = 2 } },
        .{ .id = thread_left, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .thread }, .origin = .{ .parameter = 3 } },
        .{ .id = thread_right, .function = ir.FunctionId.fromIndex(0), .type = .{ .kind = .thread }, .origin = .{ .parameter = 4 } },
        .{ .id = function_right, .function = ir.FunctionId.fromIndex(0), .type = .function, .origin = .{ .parameter = 5 } },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = table_left } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = table_right } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = function_value } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = thread_left } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = thread_right } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(5),
            .right = ir.SolverTermId.fromIndex(6),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = function_right } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(2),
            .right = ir.SolverTermId.fromIndex(8),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "dynamic-model-category-replay",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
    };
    const table_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(3) };
    const aliases = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 0 } },
    };
    const separate_tables = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 1 } },
    };
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, table_query, &aliases));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, table_query, &separate_tables));

    const cross_category_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_false, .goal = ir.SolverTermId.fromIndex(4) };
    const invalid_cross_category = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 0 } },
    };
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, cross_category_query, &invalid_cross_category));

    const thread_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(7) };
    const thread_aliases = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(5), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(6), .value = .{ .dynamic_identity = 0 } },
    };
    const separate_threads = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(5), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(6), .value = .{ .dynamic_identity = 1 } },
    };
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, thread_query, &thread_aliases));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, thread_query, &separate_threads));

    const function_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(9) };
    const function_aliases = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(8), .value = .{ .dynamic_identity = 0 } },
    };
    const separate_functions = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(8), .value = .{ .dynamic_identity = 1 } },
    };
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, function_query, &function_aliases));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, function_query, &separate_functions));
}

test "dynamic model replay and admission reject collapsed fresh allocations" {
    const fixture = @import("fixtures.zig").fresh_reference_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_table_a } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_table_b } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_table_copy } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_thread_a } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_thread_b } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(3),
            .right = ir.SolverTermId.fromIndex(4),
        } } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    const table_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(5) };
    const collapsed_tables = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 0 } },
    };
    const distinct_tables = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 1 } },
    };
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, table_query, &collapsed_tables));
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, table_query, &distinct_tables));

    const copy_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(6) };
    const separated_copy = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 1 } },
    };
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, copy_query, &separated_copy));

    const thread_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(7) };
    const collapsed_threads = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(3), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(4), .value = .{ .dynamic_identity = 0 } },
    };
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, thread_query, &collapsed_threads));

    const queries = [_]ir.SolverQuery{table_query};
    const models = [_]ir.SolverModel{.{
        .id = ir.SolverModelId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .bindings = &collapsed_tables,
        .evidence = &.{fixture.proof},
    }};
    program.queries = &queries;
    program.solver_models = &models;
    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.invalid_solver_model_value));
}

test "dynamic model replay enforces canonical function reference identity" {
    const fixture = @import("fixtures.zig").function_reference_module;
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
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(3),
        } } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    const same_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(4) };
    const same_target = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 0 } },
    };
    const separated_target = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 1 } },
    };
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, same_query, &same_target));
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, same_query, &separated_target));

    const copy_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(5) };
    const separated_copy = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 1 } },
    };
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, copy_query, &separated_copy));

    const different_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(6) };
    const collapsed_targets = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(3), .value = .{ .dynamic_identity = 0 } },
    };
    const distinct_targets = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(3), .value = .{ .dynamic_identity = 1 } },
    };
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, different_query, &collapsed_targets));
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, different_query, &distinct_targets));

    const queries = [_]ir.SolverQuery{different_query};
    const models = [_]ir.SolverModel{.{
        .id = ir.SolverModelId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .bindings = &collapsed_targets,
        .evidence = &.{fixture.proof},
    }};
    program.queries = &queries;
    program.solver_models = &models;
    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.invalid_solver_model_value));
}

test "dynamic model coherence enforces scalar domains and numeric representability" {
    const boolean_a = ir.ValueId.fromIndex(0);
    const boolean_b = ir.ValueId.fromIndex(1);
    const boolean_c = ir.ValueId.fromIndex(2);
    const copied_a = ir.ValueId.fromIndex(3);
    const copied_b = ir.ValueId.fromIndex(4);
    const copied_c = ir.ValueId.fromIndex(5);
    const exact_true = ir.ValueId.fromIndex(6);
    const exact_false = ir.ValueId.fromIndex(7);
    const large_integer = ir.ValueId.fromIndex(8);
    const large_number = ir.ValueId.fromIndex(9);
    const integer_seven = ir.ValueId.fromIndex(10);
    const number_seven = ir.ValueId.fromIndex(11);
    const values = [_]ir.Value{
        .{ .id = boolean_a, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = boolean_b, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = boolean_c, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .parameter = 2 } },
        .{ .id = copied_a, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = copied_b, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = copied_c, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = exact_true, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = exact_false, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = large_integer, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
        .{ .id = large_number, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(6), .index = 0 } } },
        .{ .id = integer_seven, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(7), .index = 0 } } },
        .{ .id = number_seven, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(8), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .copy = boolean_a }, .results = &.{copied_a}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .copy = boolean_b }, .results = &.{copied_b}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .copy = boolean_c }, .results = &.{copied_c}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .boolean = true } }, .results = &.{exact_true}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .boolean = false } }, .results = &.{exact_false}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(5), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "9007199254740993" } }, .results = &.{large_integer}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(6), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .special_number = .nan } }, .results = &.{large_number}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(7), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "7" } }, .results = &.{integer_seven}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(8), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 7.0 } }, .results = &.{number_seven}, .effects = .pure },
    };
    var terms: [values.len + 5]ir.SolverTerm = undefined;
    for (terms[0..values.len], values, 0..) |*term, value, index| {
        term.* = .{ .id = ir.SolverTermId.fromIndex(index), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = value.id } };
    }
    terms[12] = .{ .id = ir.SolverTermId.fromIndex(12), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } };
    terms[13] = .{ .id = ir.SolverTermId.fromIndex(13), .sort = .{ .kind = .dynamic_value }, .operation = .{ .if_then_else = .{
        .condition = ir.SolverTermId.fromIndex(12),
        .then_term = ir.SolverTermId.fromIndex(6),
        .else_term = ir.SolverTermId.fromIndex(7),
    } } };
    terms[14] = .{ .id = ir.SolverTermId.fromIndex(14), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
        .operator = .not_equal,
        .left = ir.SolverTermId.fromIndex(3),
        .right = ir.SolverTermId.fromIndex(4),
    } } };
    terms[15] = .{ .id = ir.SolverTermId.fromIndex(15), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
        .operator = .not_equal,
        .left = ir.SolverTermId.fromIndex(4),
        .right = ir.SolverTermId.fromIndex(5),
    } } };
    terms[16] = .{ .id = ir.SolverTermId.fromIndex(16), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
        .operator = .logical_and,
        .left = ir.SolverTermId.fromIndex(14),
        .right = ir.SolverTermId.fromIndex(15),
    } } };
    const program: ir.Program = .{
        .program_id = "dynamic-model-scalar-coherence",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };

    const three_boolean_classes = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(3), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(4), .value = .{ .dynamic_identity = 1 } },
        .{ .term = ir.SolverTermId.fromIndex(5), .value = .{ .dynamic_identity = 2 } },
    };
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &three_boolean_classes));

    const collapsed_exact_booleans = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(6), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(7), .value = .{ .dynamic_identity = 0 } },
    };
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &collapsed_exact_booleans));

    const conditional_third_class = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(6), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(7), .value = .{ .dynamic_identity = 1 } },
        .{ .term = ir.SolverTermId.fromIndex(13), .value = .{ .dynamic_identity = 2 } },
    };
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &conditional_third_class));

    const unresolved_numbers = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(8), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(9), .value = .{ .dynamic_identity = 1 } },
    };
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.unrepresentable, solver_model.dynamicBindingsCoherence(&program, &unresolved_numbers));

    const separated_equal_numbers = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(10), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(11), .value = .{ .dynamic_identity = 1 } },
    };
    const joined_equal_numbers = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(10), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(11), .value = .{ .dynamic_identity = 0 } },
    };
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.contradictory, solver_model.dynamicBindingsCoherence(&program, &separated_equal_numbers));
    try std.testing.expectEqual(solver_model.DynamicBindingsCoherence.coherent, solver_model.dynamicBindingsCoherence(&program, &joined_equal_numbers));

    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .find_model,
        .goal = ir.SolverTermId.fromIndex(16),
    }};
    const models = [_]ir.SolverModel{.{
        .id = ir.SolverModelId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .bindings = &three_boolean_classes,
    }};
    var imported_program = program;
    imported_program.queries = &queries;
    imported_program.solver_models = &models;
    var imported_report = try validation.validate(std.testing.allocator, &imported_program, .core);
    defer imported_report.deinit();
    try std.testing.expect(imported_report.contains(.invalid_solver_model_value));
}

test "artifact validation rejects unrepresentable exact dynamic numerics" {
    const fixture = @import("fixtures.zig").automatic_promotion_module;
    var values = fixture.values;
    values[fixture.v_matched.index()].type = .dynamic;
    values[fixture.v_unreachable.index()].type = .dynamic;
    var instructions = fixture.instructions;
    instructions[fixture.i_matched.index()].operation = .{ .constant = .{ .integer = "7" } };
    instructions[fixture.i_unreachable.index()].operation = .{ .constant = .{ .number = 7.0 } };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_matched } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_unreachable } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const queries = [_]ir.SolverQuery{.{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) }};
    var bindings = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .dynamic_identity = 0 } },
    };
    const models = [_]ir.SolverModel{.{
        .id = ir.SolverModelId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .bindings = &bindings,
        .evidence = &.{fixture.proof},
    }};
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.solver_models = &models;

    var exact_report = try validation.validate(std.testing.allocator, &program, .core);
    defer exact_report.deinit();
    try std.testing.expect(!exact_report.contains(.invalid_solver_model_value));

    bindings[1].value = .{ .dynamic_identity = 1 };
    var separated_report = try validation.validate(std.testing.allocator, &program, .core);
    defer separated_report.deinit();
    try std.testing.expect(separated_report.contains(.invalid_solver_model_value));

    instructions[fixture.i_matched.index()].operation = .{ .constant = .{ .integer = "9007199254740993" } };
    instructions[fixture.i_unreachable.index()].operation = .{ .constant = .{ .special_number = .nan } };
    var unresolved_report = try validation.validate(std.testing.allocator, &program, .core);
    defer unresolved_report.deinit();
    try std.testing.expect(unresolved_report.contains(.invalid_solver_model_value));
}

test "model replay checks query polarity, completeness, and redundant bindings" {
    const value_id = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = value_id,
        .function = ir.FunctionId.fromIndex(0),
        .type = .integer,
        .origin = .{ .parameter = 0 },
    }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = value_id } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "7" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "model-replay-polarity",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
    };
    const model_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    const seven = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .integer = "7" } }};
    const eight = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .integer = "8" } }};
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, model_query, &seven));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, model_query, &eight));
    try std.testing.expectEqual(solver_model.Replay.incomplete, try solver_model.replayAlloc(std.testing.allocator, &program, model_query, &.{}));
    const noncanonical = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .integer = "07" } }};
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, model_query, &noncanonical));

    const proof_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) };
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, proof_query, &eight));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, proof_query, &seven));

    const wrong_literal = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .integer = "7" } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .integer = "8" } },
    };
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, model_query, &wrong_literal));
}

test "model replay refuses out-of-range bit-vector bindings" {
    const value_id = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{.{ .id = value_id, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .parameter = 0 } }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .bit_vector, .bit_width = 8 }, .operation = .{ .value = value_id } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(0) } } },
    };
    const program: ir.Program = .{
        .program_id = "model-replay-invalid-bit-vector",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(1) };
    const bindings = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .bit_vector = .{ .value = "256", .bit_width = 8 } } }};
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, query, &bindings));
}

test "model replay checks every query assumption" {
    const value_id = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{.{ .id = value_id, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .parameter = 0 } }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = value_id } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "7" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
    };
    const constraints = [_]ir.Constraint{.{ .id = ir.ConstraintId.fromIndex(0), .predicate = ir.SolverTermId.fromIndex(2) }};
    const program: ir.Program = .{
        .program_id = "model-replay-assumption",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
        .constraints = &constraints,
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .find_model,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(3),
    };
    const seven = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .integer = "7" } }};
    const eight = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .integer = "8" } }};
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, query, &seven));
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, query, &eight));
}

test "model replay binds arbitrary precision domains without Z3" {
    const value_id = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{.{ .id = value_id, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .parameter = 0 } }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .real }, .operation = .{ .value = value_id } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .real }, .operation = .{ .real_literal = .{
            .numerator = "340282366920938463463374607431768211455",
            .denominator = "3",
        } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
    };
    const program: ir.Program = .{
        .program_id = "model-replay-arbitrary-precision",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    const bindings = [_]ir.SolverModelBinding{.{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .real = .{
        .numerator = "680564733841876926926749214863536422910",
        .denominator = "6",
    } } }};
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, query, &bindings));
}

test "dynamic truthiness model witnesses are identity-linked and coherent" {
    const function_id = ir.FunctionId.fromIndex(0);
    const unknown_left = ir.ValueId.fromIndex(0);
    const unknown_right = ir.ValueId.fromIndex(1);
    const known_string = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = unknown_left, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = unknown_right, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = known_string, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = ir.InstructionId.fromIndex(0),
        .block = ir.BlockId.fromIndex(0),
        .operation = .{ .constant = .{ .string = "known" } },
        .results = &.{known_string},
        .effects = .pure,
    }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = unknown_left } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = unknown_right } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(2) } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = known_string } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(5),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(6),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(5) } },
    };
    const program: ir.Program = .{
        .program_id = "dynamic-truthiness-model-replay",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };

    const unknown_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(1) };
    const truthy_witness = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .boolean = true } },
    };
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, unknown_query, &truthy_witness));
    const falsy_witness = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .boolean = false } },
    };
    try std.testing.expectEqual(solver_model.Replay.contradictory, try solver_model.replayAlloc(std.testing.allocator, &program, unknown_query, &falsy_witness));
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, unknown_query, &.{.{
        .term = ir.SolverTermId.fromIndex(1),
        .value = .{ .boolean = true },
    }}));

    const shared_identity_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(4) };
    const conflicting_truthiness = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .boolean = true } },
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(3), .value = .{ .boolean = false } },
    };
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, shared_identity_query, &conflicting_truthiness));

    const known_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(8) };
    const contradicted_known = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(5), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(8), .value = .{ .boolean = false } },
    };
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, known_query, &contradicted_known));

    const alias_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(7) };
    const contradicted_alias_class = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .boolean = false } },
        .{ .term = ir.SolverTermId.fromIndex(5), .value = .{ .dynamic_identity = 0 } },
    };
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, alias_query, &contradicted_alias_class));
}

test "dynamic numeric NaN model witnesses are identity-linked and coherent" {
    const function_id = ir.FunctionId.fromIndex(0);
    const unknown_left = ir.ValueId.fromIndex(0);
    const unknown_right = ir.ValueId.fromIndex(1);
    const known_integer = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = unknown_left, .function = function_id, .type = .number, .origin = .{ .parameter = 0 } },
        .{ .id = unknown_right, .function = function_id, .type = .number, .origin = .{ .parameter = 1 } },
        .{ .id = known_integer, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = ir.InstructionId.fromIndex(0),
        .block = ir.BlockId.fromIndex(0),
        .operation = .{ .constant = .{ .integer = "7" } },
        .results = &.{known_integer},
        .effects = .pure,
    }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = unknown_left } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_number_is_nan = ir.SolverTermId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = unknown_right } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_number_is_nan = ir.SolverTermId.fromIndex(2) } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .logical_or,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = known_integer } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_number_is_nan = ir.SolverTermId.fromIndex(5) } },
    };
    const program: ir.Program = .{
        .program_id = "dynamic-number-nan-model-replay",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };

    const unknown_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(1) };
    const nan_witness = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .boolean = true } },
    };
    try std.testing.expectEqual(solver_model.Replay.satisfied, try solver_model.replayAlloc(std.testing.allocator, &program, unknown_query, &nan_witness));
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, unknown_query, &.{.{
        .term = ir.SolverTermId.fromIndex(1),
        .value = .{ .boolean = true },
    }}));

    const shared_identity_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(4) };
    const conflicting_nan_class = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(0), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(1), .value = .{ .boolean = true } },
        .{ .term = ir.SolverTermId.fromIndex(2), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(3), .value = .{ .boolean = false } },
    };
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, shared_identity_query, &conflicting_nan_class));

    const known_query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_false, .goal = ir.SolverTermId.fromIndex(6) };
    const contradicted_known = [_]ir.SolverModelBinding{
        .{ .term = ir.SolverTermId.fromIndex(5), .value = .{ .dynamic_identity = 0 } },
        .{ .term = ir.SolverTermId.fromIndex(6), .value = .{ .boolean = true } },
    };
    try std.testing.expectError(error.InvalidModelInput, solver_model.replayAlloc(std.testing.allocator, &program, known_query, &contradicted_known));
}
