const ir = @import("ir.zig");
const solver_term = @import("solver_term.zig");

pub const ConditionProvedFn = *const fn (*const ir.Program, ir.SolverTermId) bool;

pub fn queryCovered(program: *const ir.Program, query: ir.SolverQuery, condition_proved: ConditionProvedFn) bool {
    if (!termCovered(program, query, query.goal, condition_proved, 0)) return false;
    for (query.assumptions) |constraint_id| {
        if (constraint_id.index() >= program.constraints.len) continue;
        if (!termCovered(program, query, program.constraints[constraint_id.index()].predicate, condition_proved, 0)) return false;
    }
    return true;
}

pub fn termPreconditionsProved(program: *const ir.Program, term_id: ir.SolverTermId, condition_proved: ConditionProvedFn) bool {
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = term_id,
    };
    return termCovered(program, query, term_id, condition_proved, 0);
}

fn termCovered(
    program: *const ir.Program,
    query: ir.SolverQuery,
    term_id: ir.SolverTermId,
    condition_proved: ConditionProvedFn,
    depth: usize,
) bool {
    if (term_id.index() >= program.solver_terms.len or depth > program.solver_terms.len) return true;
    const operation = program.solver_terms[term_id.index()].operation;
    switch (operation) {
        .value_definition => |definition| if (definition.valid_when) |condition| {
            if (!conditionCovered(program, query, condition, condition_proved)) return false;
        },
        .division => |division| if (!conditionCovered(program, query, division.defined_by, condition_proved)) return false,
        .remainder => |remainder| if (!conditionCovered(program, query, remainder.defined_by, condition_proved)) return false,
        else => {},
    }
    var dependencies = solver_term.dependencies(operation);
    while (dependencies.next()) |dependency| {
        if (!termCovered(program, query, dependency, condition_proved, depth + 1)) return false;
    }
    return true;
}

fn conditionCovered(
    program: *const ir.Program,
    query: ir.SolverQuery,
    condition: ir.SolverTermId,
    condition_proved: ConditionProvedFn,
) bool {
    if (condition_proved(program, condition)) return true;
    for (query.assumptions) |constraint_id| {
        if (constraint_id.index() >= program.constraints.len) continue;
        if (program.constraints[constraint_id.index()].predicate == condition) return true;
    }
    return false;
}

test "guarded value definitions require their semantic condition" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .semantic_atom = .{
            .primitive_operator_domain = fixture.i_result,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "2" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .integer }, .operation = .{ .value_definition = .{
            .value = fixture.v_factor,
            .expression = ir.SolverTermId.fromIndex(1),
            .valid_when = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(2),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{fixture.proof},
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    var query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(3),
    };

    try @import("std").testing.expect(!queryCovered(&program, query, neverProved));
    try @import("std").testing.expect(!termPreconditionsProved(&program, query.goal, neverProved));
    query.assumptions = &.{ir.ConstraintId.fromIndex(0)};
    try @import("std").testing.expect(queryCovered(&program, query, neverProved));
}

fn neverProved(_: *const ir.Program, _: ir.SolverTermId) bool {
    return false;
}
