const std = @import("std");
const ir = @import("ir.zig");
const fixtures = @import("fixtures.zig");
const solver_backend = @import("solver_backend.zig");
const solver_unsat_core = @import("solver_unsat_core.zig");
const validation = @import("validate.zig");

test "unsat core replay uses exactly the recorded assumptions" {
    const value_id = ir.ValueId.fromIndex(0);
    const term_id = ir.SolverTermId.fromIndex(0);
    const constraint_id = ir.ConstraintId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = value_id,
        .function = ir.FunctionId.fromIndex(0),
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const terms = [_]ir.SolverTerm{.{
        .id = term_id,
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = value_id },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = constraint_id,
        .predicate = term_id,
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{constraint_id},
        .goal = term_id,
    };
    const program: ir.Program = .{
        .program_id = "solver-unsat-core-replay",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
        .constraints = &constraints,
    };

    try std.testing.expectEqual(
        solver_unsat_core.Replay{ .unresolved = .bounded_internal_incompleteness },
        solver_unsat_core.replayInternal(&program, query, .proved, &.{}),
    );
    try std.testing.expectEqual(solver_unsat_core.Replay.satisfied, solver_unsat_core.replayInternal(&program, query, .proved, &.{constraint_id}));
    try std.testing.expectEqual(
        solver_unsat_core.Replay.satisfied,
        try solver_unsat_core.replayBackendAlloc(std.testing.allocator, &program, query, .proved, &.{constraint_id}, solver_backend.internalFacts()),
    );
}

test "generated cores fall back to the full sufficient assumption set" {
    const value_id = ir.ValueId.fromIndex(0);
    const term_id = ir.SolverTermId.fromIndex(0);
    const constraint_id = ir.ConstraintId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = value_id,
        .function = ir.FunctionId.fromIndex(0),
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const terms = [_]ir.SolverTerm{.{
        .id = term_id,
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = value_id },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = constraint_id,
        .predicate = term_id,
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{constraint_id},
        .goal = term_id,
    };
    const program: ir.Program = .{
        .program_id = "solver-unsat-core-normalization",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
        .constraints = &constraints,
    };
    const backend = solver_backend.internalFacts();
    var result = try backend.solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqual(@as(usize, 0), result.unsat_core.items.len);

    const replay_reason = try solver_unsat_core.ensureSufficientAlloc(std.testing.allocator, &program, query, backend, &result);
    try std.testing.expectEqual(
        solver_backend.UnknownReason.bounded_internal_incompleteness,
        replay_reason.?,
    );
    try std.testing.expectEqualSlices(ir.ConstraintId, &.{constraint_id}, result.unsat_core.items);
}

test "core replay rejects wrong polarity and missing semantic guards" {
    const false_term = ir.SolverTermId.fromIndex(0);
    const false_terms = [_]ir.SolverTerm{.{
        .id = false_term,
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = false },
    }};
    const false_program: ir.Program = .{
        .program_id = "solver-unsat-core-polarity",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &false_terms,
    };
    const false_query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = false_term,
    };
    try std.testing.expectEqual(solver_unsat_core.Replay.contradictory, solver_unsat_core.replayInternal(&false_program, false_query, .proved, &.{}));

    const guard = ir.SolverTermId.fromIndex(0);
    const one = ir.SolverTermId.fromIndex(1);
    const definition = ir.SolverTermId.fromIndex(2);
    const goal = ir.SolverTermId.fromIndex(3);
    const guard_constraint = ir.ConstraintId.fromIndex(0);
    const guarded_terms = [_]ir.SolverTerm{
        .{ .id = guard, .sort = .{ .kind = .boolean }, .operation = .{ .semantic_atom = .{ .primitive_operator_domain = ir.InstructionId.fromIndex(0) } } },
        .{ .id = one, .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "1" } },
        .{ .id = definition, .sort = .{ .kind = .integer }, .operation = .{ .value_definition = .{
            .value = ir.ValueId.fromIndex(0),
            .expression = one,
            .valid_when = guard,
        } } },
        .{ .id = goal, .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = definition, .right = one } } },
    };
    const guarded_constraints = [_]ir.Constraint{.{ .id = guard_constraint, .predicate = guard }};
    const guarded_program: ir.Program = .{
        .program_id = "solver-unsat-core-guard",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &guarded_terms,
        .constraints = &guarded_constraints,
    };
    const guarded_query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{guard_constraint},
        .goal = goal,
    };
    try std.testing.expectEqual(solver_unsat_core.Replay.contradictory, solver_unsat_core.replayInternal(&guarded_program, guarded_query, .proved, &.{}));
    try std.testing.expectEqual(solver_unsat_core.Replay.satisfied, solver_unsat_core.replayInternal(&guarded_program, guarded_query, .proved, &.{guard_constraint}));
}

fn expectCoreDiagnostic(report: *const validation.Report, code: validation.DiagnosticCode) !void {
    for (report.diagnostics.items) |diagnostic| {
        if (diagnostic.code == code and diagnostic.entity_index == 0) return;
    }
    return error.ExpectedDiagnosticMissing;
}

test "standalone cores replay without certificate authority" {
    const fixture = fixtures.arithmetic_module;
    const constraint_id = ir.ConstraintId.fromIndex(0);
    var terms = [_]ir.SolverTerm{
        .{
            .id = ir.SolverTermId.fromIndex(0),
            .sort = .{ .kind = .boolean },
            .operation = .{ .boolean_literal = true },
        },
        .{
            .id = ir.SolverTermId.fromIndex(1),
            .sort = .{ .kind = .boolean },
            .operation = .{ .boolean_literal = true },
        },
    };
    const constraints = [_]ir.Constraint{.{
        .id = constraint_id,
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{fixture.proof},
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{constraint_id},
        .goal = ir.SolverTermId.fromIndex(1),
    }};
    var cores = [_]ir.UnsatCore{.{
        .id = ir.UnsatCoreId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .constraints = &.{constraint_id},
        .evidence = &.{fixture.proof},
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    program.queries = &queries;
    program.unsat_cores = &cores;

    var valid_report = try validation.validate(std.testing.allocator, &program, .core);
    defer valid_report.deinit();
    try std.testing.expect(valid_report.isClean());

    cores[0].evidence = &.{};
    var evidence_report = try validation.validate(std.testing.allocator, &program, .core);
    defer evidence_report.deinit();
    try expectCoreDiagnostic(&evidence_report, .noncanonical_unsat_core_evidence);
    cores[0].evidence = &.{fixture.proof};

    terms[1].operation = .{ .boolean_literal = false };
    var contradictory_report = try validation.validate(std.testing.allocator, &program, .core);
    defer contradictory_report.deinit();
    try expectCoreDiagnostic(&contradictory_report, .contradictory_unsat_core);
}

test "standalone cores require deterministic replay completeness" {
    const fixture = fixtures.absolute_value_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = fixture.v_is_negative },
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    }};
    const cores = [_]ir.UnsatCore{.{
        .id = ir.UnsatCoreId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .constraints = &.{},
        .evidence = &.{fixture.proof},
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.unsat_cores = &cores;

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try expectCoreDiagnostic(&report, .incomplete_unsat_core);
}
