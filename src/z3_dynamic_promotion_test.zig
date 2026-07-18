const std = @import("std");
const lifter = @import("semantic_lifter");
const ir = lifter.ir;

test "source-bound dynamic equality promotion agrees across solver engines" {
    const fixture = lifter.fixtures.dynamic_truthiness_module;
    inline for (.{
        .{ .operator = ir.BinaryOperator.equal, .truth = true },
        .{ .operator = ir.BinaryOperator.not_equal, .truth = false },
    }) |case| {
        var instructions = fixture.instructions;
        instructions[fixture.i_truthy_not.index()].operation = .{ .binary = .{
            .operator = case.operator,
            .left = fixture.v_truthy_literal,
            .right = fixture.v_truthy_condition,
        } };
        var program = fixture.program;
        program.instructions = &instructions;
        var terms: std.ArrayList(ir.SolverTerm) = .empty;
        defer terms.deinit(std.testing.allocator);
        const definition = (try lifter.solver_promotion.ensureDefinition(
            std.testing.allocator,
            &program,
            &terms,
            fixture.v_truthy_not,
        )).?;
        program.solver_terms = terms.items;
        const query: ir.SolverQuery = .{
            .id = ir.QueryId.fromIndex(0),
            .kind = if (case.truth) .prove_true else .prove_false,
            .goal = definition,
        };
        try std.testing.expectEqual(ir.SolverResolution.proved, lifter.solver.solve(&program, query));
        var result = try lifter.z3_backend.defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
        try std.testing.expectEqual(@as(usize, 0), result.model.items.len);
    }
}

test "descriptor-derived numeric ordering canonicalizes dynamic Boolean values" {
    const fixture = lifter.fixtures.dynamic_truthiness_module;
    var values = fixture.values;
    values[fixture.v_truthy_literal.index()].type = .number;
    values[fixture.v_truthy_condition.index()].type = .number;
    values[fixture.v_truthy_not.index()].type = .dynamic;
    var instructions = fixture.instructions;
    instructions[fixture.i_truthy_literal.index()].operation = .{ .constant = .{ .number = 1.5 } };
    instructions[fixture.i_truthy_condition.index()].operation = .{ .constant = .{ .number = 2.25 } };
    instructions[fixture.i_truthy_condition.index()].effects = .pure;
    instructions[fixture.i_truthy_not.index()].operation = .{ .binary = .{
        .operator = .less,
        .left = fixture.v_truthy_literal,
        .right = fixture.v_truthy_condition,
    } };
    instructions[fixture.i_falsy_literal.index()].operation = .{ .constant = .{ .boolean = true } };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_truthy_not } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_falsy_literal } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(2),
    };

    try std.testing.expectEqual(ir.SolverResolution.proved, lifter.solver.solve(&program, query));
    var result = try lifter.z3_backend.defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqual(@as(usize, 0), result.model.items.len);
}

test "descriptor-derived exact Boolean results canonicalize dynamic Boolean values" {
    const fixture = lifter.fixtures.dynamic_truthiness_module;
    const Case = struct { operator: ir.BinaryOperator, left: bool, right: bool };
    for ([_]Case{
        .{ .operator = .logical_or, .left = false, .right = true },
        .{ .operator = .equal, .left = true, .right = true },
    }) |case| {
        var values = fixture.values;
        values[fixture.v_truthy_literal.index()].type = .boolean;
        values[fixture.v_truthy_condition.index()].type = .boolean;
        values[fixture.v_truthy_not.index()].type = .dynamic;
        var instructions = fixture.instructions;
        instructions[fixture.i_truthy_literal.index()].operation = .{ .constant = .{ .boolean = case.left } };
        instructions[fixture.i_truthy_condition.index()].operation = .{ .constant = .{ .boolean = case.right } };
        instructions[fixture.i_truthy_condition.index()].effects = .pure;
        instructions[fixture.i_truthy_not.index()].operation = .{ .binary = .{
            .operator = case.operator,
            .left = fixture.v_truthy_literal,
            .right = fixture.v_truthy_condition,
        } };
        instructions[fixture.i_falsy_literal.index()].operation = .{ .constant = .{ .boolean = true } };
        const terms = [_]ir.SolverTerm{
            .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_truthy_not } },
            .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_falsy_literal } },
            .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
                .operator = .equal,
                .left = ir.SolverTermId.fromIndex(0),
                .right = ir.SolverTermId.fromIndex(1),
            } } },
        };
        var program = fixture.program;
        program.values = &values;
        program.instructions = &instructions;
        program.solver_terms = &terms;
        const query: ir.SolverQuery = .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .goal = ir.SolverTermId.fromIndex(2),
        };

        try std.testing.expectEqual(ir.SolverResolution.proved, lifter.solver.solve(&program, query));
        var result = try lifter.z3_backend.defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
        try std.testing.expectEqual(@as(usize, 0), result.model.items.len);
    }
}

test "source-bound numeric equality is total and consumes non-NaN assumptions" {
    const fixture = lifter.fixtures.dynamic_truthiness_module;
    var values = fixture.values;
    values[fixture.v_truthy_condition.index()].type = .number;
    var instructions = fixture.instructions;
    instructions[fixture.i_truthy_condition.index()].operation = .{ .environment_get = .{
        .target = .{ .ambient = {} },
        .name = "unknown_number",
    } };
    instructions[fixture.i_truthy_condition.index()].effects = .semantic_environment_read;
    instructions[fixture.i_truthy_not.index()].operation = .{ .binary = .{
        .operator = .equal,
        .left = fixture.v_truthy_condition,
        .right = fixture.v_truthy_condition,
    } };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(std.testing.allocator);
    const definition = (try lifter.solver_promotion.ensureDefinition(
        std.testing.allocator,
        &program,
        &terms,
        fixture.v_truthy_not,
    )).?;
    program.solver_terms = terms.items;
    const definition_record = terms.items[definition.index()].operation.value_definition;
    try std.testing.expectEqual(@as(?ir.SolverTermId, null), definition_record.valid_when);
    const total_equality = terms.items[definition_record.expression.index()].operation.binary;
    try std.testing.expectEqual(ir.SolverBinaryOperator.logical_and, total_equality.operator);
    const guard = total_equality.left;
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = guard,
        .evidence = &.{fixture.proof},
        .scope = .{ .program = {} },
    }};
    program.constraints = &constraints;

    const unguarded: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = definition,
    };
    try std.testing.expectEqual(ir.SolverResolution.unknown, lifter.solver.solve(&program, unguarded));
    var counterexample = try lifter.z3_backend.defaultBackend().solve(std.testing.allocator, &program, unguarded);
    defer counterexample.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.disproved, counterexample.resolution);
    try std.testing.expectEqual(@as(usize, 2), counterexample.model.items.len);
    try std.testing.expectEqual(true, counterexample.model.items[1].value.boolean);
    try std.testing.expectEqual(
        lifter.solver_model.Replay.satisfied,
        try lifter.solver_model.replayAlloc(std.testing.allocator, &program, unguarded, counterexample.model.items),
    );

    var guarded = unguarded;
    guarded.assumptions = &.{ir.ConstraintId.fromIndex(0)};
    try std.testing.expectEqual(ir.SolverResolution.proved, lifter.solver.solve(&program, guarded));
    var guarded_result = try lifter.z3_backend.defaultBackend().solve(std.testing.allocator, &program, guarded);
    defer guarded_result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, guarded_result.resolution);
    try std.testing.expectEqual(@as(usize, 0), guarded_result.model.items.len);
}

test "source-bound exact infinities agree across solver engines" {
    const fixture = lifter.fixtures.dynamic_truthiness_module;
    const Case = struct {
        operator: ir.BinaryOperator,
        left: ir.SpecialNumber,
        right: ir.SpecialNumber,
    };
    for ([_]Case{
        .{ .operator = .equal, .left = .positive_infinity, .right = .positive_infinity },
        .{ .operator = .not_equal, .left = .positive_infinity, .right = .negative_infinity },
    }) |case| {
        var values = fixture.values;
        values[fixture.v_truthy_literal.index()].type = .number;
        values[fixture.v_truthy_condition.index()].type = .number;
        var instructions = fixture.instructions;
        instructions[fixture.i_truthy_literal.index()].operation = .{ .constant = .{ .special_number = case.left } };
        instructions[fixture.i_truthy_condition.index()].operation = .{ .constant = .{ .special_number = case.right } };
        instructions[fixture.i_truthy_condition.index()].effects = .pure;
        instructions[fixture.i_truthy_not.index()].operation = .{ .binary = .{
            .operator = case.operator,
            .left = fixture.v_truthy_literal,
            .right = fixture.v_truthy_condition,
        } };
        var program = fixture.program;
        program.values = &values;
        program.instructions = &instructions;
        var terms: std.ArrayList(ir.SolverTerm) = .empty;
        defer terms.deinit(std.testing.allocator);
        const definition = (try lifter.solver_promotion.ensureDefinition(
            std.testing.allocator,
            &program,
            &terms,
            fixture.v_truthy_not,
        )).?;
        program.solver_terms = terms.items;
        const definition_record = terms.items[definition.index()].operation.value_definition;
        try std.testing.expectEqual(@as(?ir.SolverTermId, null), definition_record.valid_when);
        const query: ir.SolverQuery = .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .goal = definition,
        };
        try std.testing.expectEqual(ir.SolverResolution.proved, lifter.solver.solve(&program, query));
        var result = try lifter.z3_backend.defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
        try std.testing.expectEqual(@as(usize, 0), result.model.items.len);
    }

    var values = fixture.values;
    values[fixture.v_truthy_literal.index()].type = .number;
    values[fixture.v_truthy_condition.index()].type = .number;
    var instructions = fixture.instructions;
    instructions[fixture.i_truthy_literal.index()].operation = .{ .constant = .{ .special_number = .positive_infinity } };
    instructions[fixture.i_truthy_condition.index()].operation = .{ .unary = .{
        .operator = .negate,
        .operand = fixture.v_truthy_literal,
    } };
    instructions[fixture.i_truthy_condition.index()].effects = .pure;
    instructions[fixture.i_truthy_not.index()].operation = .{ .binary = .{
        .operator = .not_equal,
        .left = fixture.v_truthy_literal,
        .right = fixture.v_truthy_condition,
    } };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(std.testing.allocator);
    const definition = (try lifter.solver_promotion.ensureDefinition(
        std.testing.allocator,
        &program,
        &terms,
        fixture.v_truthy_not,
    )).?;
    program.solver_terms = terms.items;
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = definition,
    };
    try std.testing.expectEqual(ir.SolverResolution.proved, lifter.solver.solve(&program, query));
    var result = try lifter.z3_backend.defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqual(@as(usize, 0), result.model.items.len);

    {
        var arithmetic_values = fixture.values;
        arithmetic_values[fixture.v_truthy_literal.index()].type = .number;
        arithmetic_values[fixture.v_truthy_condition.index()].type = .number;
        arithmetic_values[fixture.v_truthy_not.index()].type = .number;
        var arithmetic_instructions = fixture.instructions;
        arithmetic_instructions[fixture.i_truthy_literal.index()].operation = .{ .constant = .{ .special_number = .positive_infinity } };
        arithmetic_instructions[fixture.i_truthy_condition.index()].operation = .{ .constant = .{ .special_number = .negative_infinity } };
        arithmetic_instructions[fixture.i_truthy_condition.index()].effects = .pure;
        arithmetic_instructions[fixture.i_truthy_not.index()].operation = .{ .binary = .{
            .operator = .add,
            .left = fixture.v_truthy_literal,
            .right = fixture.v_truthy_condition,
        } };
        const arithmetic_terms = [_]ir.SolverTerm{
            .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_truthy_not } },
            .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_number_is_nan = ir.SolverTermId.fromIndex(0) } },
        };
        var arithmetic_program = fixture.program;
        arithmetic_program.values = &arithmetic_values;
        arithmetic_program.instructions = &arithmetic_instructions;
        arithmetic_program.solver_terms = &arithmetic_terms;
        const arithmetic_query: ir.SolverQuery = .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .goal = ir.SolverTermId.fromIndex(1),
        };
        try std.testing.expectEqual(ir.SolverResolution.proved, lifter.solver.solve(&arithmetic_program, arithmetic_query));
        var arithmetic_result = try lifter.z3_backend.defaultBackend().solve(std.testing.allocator, &arithmetic_program, arithmetic_query);
        defer arithmetic_result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, arithmetic_result.resolution);
        try std.testing.expectEqual(@as(usize, 0), arithmetic_result.model.items.len);
    }
}

test "Z3 NaN predicate models extract and replay both numeric domains" {
    const source = ir.ValueId.fromIndex(0);
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = source } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_number_is_nan = ir.SolverTermId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .logical_not = ir.SolverTermId.fromIndex(1) } },
    };
    const program: ir.Program = .{
        .program_id = "z3-dynamic-number-nan-model",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{.{
            .id = source,
            .function = ir.FunctionId.fromIndex(0),
            .type = .number,
            .origin = .{ .parameter = 0 },
        }},
        .solver_terms = &terms,
    };

    inline for (.{
        .{ .goal = ir.SolverTermId.fromIndex(1), .is_nan = true },
        .{ .goal = ir.SolverTermId.fromIndex(2), .is_nan = false },
    }) |case| {
        const query: ir.SolverQuery = .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .find_model,
            .goal = case.goal,
        };
        try std.testing.expectEqual(ir.SolverResolution.unknown, lifter.solver.solve(&program, query));

        var result = try lifter.z3_backend.defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
        try std.testing.expectEqual(@as(usize, 2), result.model.items.len);
        try std.testing.expectEqual(ir.SolverTermId.fromIndex(0), result.model.items[0].term);
        try std.testing.expectEqual(@as(u32, 0), result.model.items[0].value.dynamic_identity);
        try std.testing.expectEqual(ir.SolverTermId.fromIndex(1), result.model.items[1].term);
        try std.testing.expectEqual(case.is_nan, result.model.items[1].value.boolean);
        try std.testing.expectEqual(
            lifter.solver_model.Replay.satisfied,
            try lifter.solver_model.replayAlloc(std.testing.allocator, &program, query, result.model.items),
        );
    }
}
