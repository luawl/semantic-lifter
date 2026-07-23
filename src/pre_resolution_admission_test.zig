const std = @import("std");
const ir = @import("ir.zig");
const fixtures = @import("fixtures.zig");
const validation = @import("validate.zig");
const admission = @import("pre_resolution_admission.zig");
const pipeline = @import("pipeline.zig");
const proof_orchestrator = @import("proof_orchestrator.zig");
const solver_backend = @import("solver_backend.zig");

const CountingBackend = struct {
    calls: usize = 0,

    fn backend(self: *CountingBackend) solver_backend.Backend {
        return .{
            .engine = .internal_facts,
            .context = self,
            .solve_fn = solve,
        };
    }

    fn solve(
        context: ?*anyopaque,
        _: std.mem.Allocator,
        program: *const ir.Program,
        query: ir.SolverQuery,
    ) !solver_backend.Result {
        const self: *CountingBackend = @ptrCast(@alignCast(context.?));
        self.calls += 1;
        const resolution = @import("solver.zig").solve(program, query);
        return .{
            .engine = .internal_facts,
            .resolution = resolution,
            .unknown_reason = if (resolution == .unknown) .bounded_internal_incompleteness else null,
        };
    }
};

fn expectPendingInstructionClaimResolves(
    program: *const ir.Program,
    code: validation.DiagnosticCode,
    claim_id: ir.ClaimId,
) !void {
    var ordinary = try validation.validate(std.testing.allocator, program, .core);
    defer ordinary.deinit();
    try std.testing.expect(ordinary.contains(code));

    var preflight = try admission.validateAlloc(std.testing.allocator, program);
    defer preflight.deinit();
    try std.testing.expect(preflight.isClean());

    var outcome = try pipeline.runAlloc(
        std.testing.allocator,
        program,
        solver_backend.internalFacts(),
        .{ .profile = .core },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expectEqual(ir.ClaimStatus.proved, outcome.program().?.claims[claim_id.index()].status);
    try std.testing.expect(outcome.program().?.claims[claim_id.index()].certificate != null);
}

test "malformed non-solver IR never reaches resolution or a backend" {
    const fixture = fixtures.arithmetic_module;
    var functions = fixture.functions;
    functions[fixture.f_add.index()].parameters = &.{ fixture.v_right, fixture.v_left };

    const term_id = ir.SolverTermId.fromIndex(0);
    const query_id = ir.QueryId.fromIndex(0);
    const terms = [_]ir.SolverTerm{.{
        .id = term_id,
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .prove_true,
        .goal = term_id,
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .control_structure,
        .subject = .{ .program = {} },
        .status = .open,
        .blocks_profile = .core,
        .detail = "pending work must not hide malformed ownership",
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = query_id,
    }};
    var program = fixture.program;
    program.functions = &functions;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.obligations = &obligations;

    var counter: CountingBackend = .{};
    var outcome = try pipeline.runAlloc(
        std.testing.allocator,
        &program,
        counter.backend(),
        .{ .profile = .core },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.program() == null);
    try std.testing.expect(outcome.report.contains(.function_parameter_origin_mismatch));
    try std.testing.expectEqual(@as(usize, 0), counter.calls);

    try std.testing.expectError(
        error.InvalidProgramInput,
        proof_orchestrator.resolveAlloc(std.testing.allocator, &program, counter.backend()),
    );
    try std.testing.expectEqual(@as(usize, 0), counter.calls);
}

test "an exact pending effect claim may resolve before core admission" {
    const fixture = fixtures.open_pack_adjust_module;
    const term_id = ir.SolverTermId.fromIndex(0);
    const constraint_id = ir.ConstraintId.fromIndex(0);
    const query_id = ir.QueryId.fromIndex(0);
    const claim_id = ir.ClaimId.fromIndex(0);
    const terms = [_]ir.SolverTerm{.{
        .id = term_id,
        .sort = .{ .kind = .boolean },
        .operation = .{ .semantic_atom = .{ .instruction_effects = fixture.i_call } },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = constraint_id,
        .predicate = term_id,
        .evidence = &.{fixture.proof},
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .prove_true,
        .assumptions = &.{constraint_id},
        .goal = term_id,
    }};
    const claims = [_]ir.Claim{.{
        .id = claim_id,
        .subject = .{ .instruction = fixture.i_call },
        .predicate = term_id,
        .purpose = .{ .effect_summary = .pure },
        .status = .unproven,
        .evidence = &.{fixture.proof},
        .query = query_id,
    }};
    var instructions = fixture.instructions;
    instructions[fixture.i_call.index()].effects = .pure;
    instructions[fixture.i_call.index()].claims = &.{claim_id};
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    program.queries = &queries;
    program.claims = &claims;

    var ordinary = try validation.validate(std.testing.allocator, &program, .core);
    defer ordinary.deinit();
    try std.testing.expect(ordinary.contains(.understated_call_effects));

    var preflight = try admission.validateAlloc(std.testing.allocator, &program);
    defer preflight.deinit();
    try std.testing.expect(preflight.isClean());

    var counter: CountingBackend = .{};
    var outcome = try pipeline.runAlloc(
        std.testing.allocator,
        &program,
        counter.backend(),
        .{ .profile = .core },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expectEqual(@as(usize, 1), counter.calls);
    try std.testing.expectEqual(ir.ClaimStatus.proved, outcome.program().?.claims[claim_id.index()].status);
    try std.testing.expect(outcome.program().?.claims[claim_id.index()].certificate != null);
}

test "an exact pending primitive-domain claim may resolve before core admission" {
    const fixture = fixtures.arithmetic_module;
    const term_id = ir.SolverTermId.fromIndex(0);
    const constraint_id = ir.ConstraintId.fromIndex(0);
    const query_id = ir.QueryId.fromIndex(0);
    const claim_id = ir.ClaimId.fromIndex(0);
    const terms = [_]ir.SolverTerm{.{
        .id = term_id,
        .sort = .{ .kind = .boolean },
        .operation = .{ .semantic_atom = .{ .primitive_operator_domain = fixture.i_sum } },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = constraint_id,
        .predicate = term_id,
        .evidence = &.{fixture.proof},
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .prove_true,
        .assumptions = &.{constraint_id},
        .goal = term_id,
    }};
    const claims = [_]ir.Claim{.{
        .id = claim_id,
        .subject = .{ .instruction = fixture.i_sum },
        .predicate = term_id,
        .purpose = .{ .primitive_operator_domain = .pure },
        .status = .unproven,
        .evidence = &.{fixture.proof},
        .query = query_id,
    }};
    var values = fixture.values;
    values[fixture.v_left.index()].type = .dynamic;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation.binary.mode = .primitive;
    instructions[fixture.i_sum.index()].claims = &.{claim_id};
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    program.queries = &queries;
    program.claims = &claims;

    try expectPendingInstructionClaimResolves(&program, .unproved_primitive_operator_domain, claim_id);
}

test "an exact pending no-metamethod claim must leave sufficient base effects" {
    const fixture = fixtures.open_pack_adjust_module;
    const term_id = ir.SolverTermId.fromIndex(0);
    const constraint_id = ir.ConstraintId.fromIndex(0);
    const query_id = ir.QueryId.fromIndex(0);
    const claim_id = ir.ClaimId.fromIndex(0);
    const terms = [_]ir.SolverTerm{.{
        .id = term_id,
        .sort = .{ .kind = .boolean },
        .operation = .{ .semantic_atom = .{ .no_metamethod_dispatch = fixture.i_get } },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = constraint_id,
        .predicate = term_id,
        .evidence = &.{fixture.proof},
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .prove_true,
        .assumptions = &.{constraint_id},
        .goal = term_id,
    }};
    var claims = [_]ir.Claim{.{
        .id = claim_id,
        .subject = .{ .instruction = fixture.i_get },
        .predicate = term_id,
        .purpose = .{ .no_metamethod_dispatch = ir.EffectSummary.raw_table_read },
        .status = .unproven,
        .evidence = &.{fixture.proof},
        .query = query_id,
    }};
    var instructions = fixture.instructions;
    instructions[fixture.i_get.index()].effects = .raw_table_read;
    instructions[fixture.i_get.index()].claims = &.{claim_id};
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    program.queries = &queries;
    program.claims = &claims;

    try expectPendingInstructionClaimResolves(&program, .understated_environment_get_effects, claim_id);

    instructions[fixture.i_get.index()].effects = .pure;
    claims[0].purpose = .{ .no_metamethod_dispatch = .pure };
    var insufficient = try admission.validateAlloc(std.testing.allocator, &program);
    defer insufficient.deinit();
    try std.testing.expect(insufficient.contains(.understated_environment_get_effects));
}

test "an unmatched effect understatement is rejected before pending work executes" {
    const fixture = fixtures.open_pack_adjust_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_call.index()].effects = .pure;

    const term_id = ir.SolverTermId.fromIndex(0);
    const query_id = ir.QueryId.fromIndex(0);
    const terms = [_]ir.SolverTerm{.{
        .id = term_id,
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .prove_true,
        .goal = term_id,
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .effect_proof,
        .subject = .{ .instruction = fixture.i_call },
        .status = .open,
        .blocks_profile = .core,
        .detail = "an obligation is not instruction effect authority",
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = query_id,
    }};
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.obligations = &obligations;

    var counter: CountingBackend = .{};
    var outcome = try pipeline.runAlloc(
        std.testing.allocator,
        &program,
        counter.backend(),
        .{ .profile = .core },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.program() == null);
    try std.testing.expect(outcome.report.contains(.understated_call_effects));
    try std.testing.expect(!outcome.report.contains(.open_profile_obligation));
    try std.testing.expectEqual(@as(usize, 0), counter.calls);
}
