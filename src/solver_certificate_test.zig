const std = @import("std");
const ir = @import("ir.zig");
const fixtures = @import("fixtures.zig");
const proof_digest = @import("proof_digest.zig");
const proof_orchestrator = @import("proof_orchestrator.zig");
const solver_backend = @import("solver_backend.zig");
const validation = @import("validate.zig");

const Fixture = struct {
    resolved: proof_orchestrator.ResolvedProgram,
    core_certificate: ir.CertificateId,
    model_certificate: ir.CertificateId,
};

fn resolveFixture() !Fixture {
    const fixture = fixtures.arithmetic_module;
    const terms = [_]ir.SolverTerm{
        .{
            .id = ir.SolverTermId.fromIndex(0),
            .sort = .{ .kind = .boolean },
            .operation = .{ .boolean_literal = true },
        },
        .{
            .id = ir.SolverTermId.fromIndex(1),
            .sort = .{ .kind = .boolean },
            .operation = .{ .boolean_literal = false },
        },
    };
    const queries = [_]ir.SolverQuery{
        .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(0) },
        .{ .id = ir.QueryId.fromIndex(1), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(1) },
    };
    const claims = [_]ir.Claim{
        .{
            .id = ir.ClaimId.fromIndex(0),
            .subject = .{ .program = {} },
            .predicate = ir.SolverTermId.fromIndex(0),
            .status = .unproven,
            .evidence = &.{fixture.proof},
            .query = ir.QueryId.fromIndex(0),
        },
        .{
            .id = ir.ClaimId.fromIndex(1),
            .subject = .{ .program = {} },
            .predicate = ir.SolverTermId.fromIndex(1),
            .status = .unproven,
            .evidence = &.{fixture.proof},
            .query = ir.QueryId.fromIndex(1),
        },
    };
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .numeric_domain,
        .subject = .{ .program = {} },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "shares the proved query",
        .evidence = &.{fixture.proof},
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;
    program.obligations = &obligations;

    var resolved = try proof_orchestrator.resolveAlloc(std.testing.allocator, &program, solver_backend.internalFacts());
    errdefer resolved.deinit();
    return .{
        .core_certificate = resolved.program.claims[0].certificate.?,
        .model_certificate = resolved.program.claims[1].certificate.?,
        .resolved = resolved,
    };
}

fn expectDiagnosticAt(report: *const validation.Report, code: validation.DiagnosticCode, index: u32) !void {
    for (report.diagnostics.items) |diagnostic| {
        if (diagnostic.code == code and diagnostic.entity_index == index) return;
    }
    return error.ExpectedDiagnosticMissing;
}

test "resolved framework certificates require durable proof artifacts" {
    var fixture = try resolveFixture();
    defer fixture.resolved.deinit();
    const resolved = &fixture.resolved.program;

    try std.testing.expect(resolved.certificates[fixture.core_certificate.index()].unsat_core != null);
    try std.testing.expect(resolved.certificates[fixture.model_certificate.index()].model != null);
    for (resolved.certificates) |certificate| {
        try std.testing.expectEqual(ir.SolverEngine.internal_facts, certificate.engine);
        try std.testing.expect(certificate.evidence.len != 0);
        try std.testing.expect(proof_digest.isFrameworkDigest(certificate.certificate_digest.?));
    }
    var clean = try validation.validate(std.testing.allocator, resolved, .core);
    defer clean.deinit();
    try std.testing.expect(clean.isClean());

    const certificates = try std.testing.allocator.dupe(ir.SolverCertificate, resolved.certificates);
    defer std.testing.allocator.free(certificates);
    var tampered = resolved.*;
    tampered.certificates = certificates;

    certificates[fixture.core_certificate.index()].evidence = &.{};
    var evidence_report = try validation.validate(std.testing.allocator, &tampered, .core);
    defer evidence_report.deinit();
    try expectDiagnosticAt(&evidence_report, .certificate_without_proof, @intCast(fixture.core_certificate.index()));
    certificates[fixture.core_certificate.index()] = resolved.certificates[fixture.core_certificate.index()];

    certificates[fixture.core_certificate.index()].certificate_digest = null;
    var digest_report = try validation.validate(std.testing.allocator, &tampered, .core);
    defer digest_report.deinit();
    try expectDiagnosticAt(&digest_report, .certificate_without_proof, @intCast(fixture.core_certificate.index()));
    certificates[fixture.core_certificate.index()] = resolved.certificates[fixture.core_certificate.index()];

    certificates[fixture.core_certificate.index()].unsat_core = null;
    var core_report = try validation.validate(std.testing.allocator, &tampered, .core);
    defer core_report.deinit();
    try expectDiagnosticAt(&core_report, .certificate_without_artifact, @intCast(fixture.core_certificate.index()));
    certificates[fixture.core_certificate.index()] = resolved.certificates[fixture.core_certificate.index()];

    certificates[fixture.model_certificate.index()].model = null;
    var model_report = try validation.validate(std.testing.allocator, &tampered, .core);
    defer model_report.deinit();
    try expectDiagnosticAt(&model_report, .certificate_without_artifact, @intCast(fixture.model_certificate.index()));
}

test "resolved consumers require certificate-covered provenance" {
    var fixture = try resolveFixture();
    defer fixture.resolved.deinit();
    const resolved = &fixture.resolved.program;
    try std.testing.expectEqual(@as(usize, 1), resolved.evidence.len);

    const extra_evidence = ir.EvidenceId.fromIndex(1);
    const evidence = [_]ir.Evidence{
        resolved.evidence[0],
        .{ .id = extra_evidence, .kind = .frontend_proof, .locator = "fixture:consumer-only-provenance" },
    };
    var claims = [_]ir.Claim{ resolved.claims[0], resolved.claims[1] };
    var obligations = [_]ir.Obligation{resolved.obligations[0]};
    var tampered = resolved.*;
    tampered.evidence = &evidence;
    tampered.claims = &claims;
    tampered.obligations = &obligations;

    claims[0].evidence = &.{extra_evidence};
    var claim_report = try validation.validate(std.testing.allocator, &tampered, .core);
    defer claim_report.deinit();
    try expectDiagnosticAt(&claim_report, .claim_certificate_evidence_mismatch, 0);
    try std.testing.expect(!claim_report.contains(.certificate_digest_mismatch));
    claims[0] = resolved.claims[0];

    obligations[0].evidence = &.{extra_evidence};
    var obligation_report = try validation.validate(std.testing.allocator, &tampered, .core);
    defer obligation_report.deinit();
    try expectDiagnosticAt(&obligation_report, .obligation_certificate_evidence_mismatch, 0);
    try expectDiagnosticAt(&obligation_report, .certificate_digest_mismatch, @intCast(fixture.core_certificate.index()));

    obligations[0] = resolved.obligations[0];
    obligations[0].kind = .alias_proof;
    var kind_report = try validation.validate(std.testing.allocator, &tampered, .core);
    defer kind_report.deinit();
    try expectDiagnosticAt(&kind_report, .certificate_digest_mismatch, @intCast(fixture.core_certificate.index()));

    obligations[0] = resolved.obligations[0];
    obligations[0].subject = .{ .function = fixtures.arithmetic_module.f_add };
    var subject_report = try validation.validate(std.testing.allocator, &tampered, .core);
    defer subject_report.deinit();
    try expectDiagnosticAt(&subject_report, .obligation_query_subject_mismatch, 0);
    try expectDiagnosticAt(&subject_report, .certificate_digest_mismatch, @intCast(fixture.core_certificate.index()));

    obligations[0] = resolved.obligations[0];
    obligations[0].requirement.?.kind = .prove_false;
    var requirement_report = try validation.validate(std.testing.allocator, &tampered, .core);
    defer requirement_report.deinit();
    try expectDiagnosticAt(&requirement_report, .obligation_query_requirement_mismatch, 0);
    try expectDiagnosticAt(&requirement_report, .certificate_digest_mismatch, @intCast(fixture.core_certificate.index()));

    obligations[0] = resolved.obligations[0];
    obligations[0].blocks_profile = .core;
    var profile_report = try validation.validate(std.testing.allocator, &tampered, .core);
    defer profile_report.deinit();
    try expectDiagnosticAt(&profile_report, .certificate_digest_mismatch, @intCast(fixture.core_certificate.index()));
}

test "orchestration does not mint evidence-free framework certificates" {
    const fixture = fixtures.arithmetic_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    }};
    const claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(0),
        .status = .unproven,
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;

    var resolved = try proof_orchestrator.resolveAlloc(std.testing.allocator, &program, solver_backend.internalFacts());
    defer resolved.deinit();
    try std.testing.expectEqual(@as(usize, 0), resolved.program.certificates.len);
    try std.testing.expectEqual(ir.ClaimStatus.unproven, resolved.program.claims[0].status);
    try std.testing.expect(resolved.program.claims[0].certificate == null);

    var report = try validation.validate(std.testing.allocator, &resolved.program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "unknown framework results remain artifact-free" {
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
    const certificates = [_]ir.SolverCertificate{.{
        .id = ir.CertificateId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .engine = .internal_facts,
        .resolution = .unknown,
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.certificates = &certificates;

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "framework certificates retain the canonical dependency evidence closure" {
    const fixture = fixtures.arithmetic_module;
    const dependency_evidence = ir.EvidenceId.fromIndex(1);
    const evidence = [_]ir.Evidence{
        fixture.evidence[0],
        .{ .id = dependency_evidence, .kind = .frontend_proof, .locator = "fixture:query-dependency" },
    };
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{dependency_evidence},
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(0),
    }};
    const claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(0),
        .status = .unproven,
        .evidence = &.{fixture.proof},
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.evidence = &evidence;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    program.queries = &queries;
    program.claims = &claims;

    var resolved = try proof_orchestrator.resolveAlloc(std.testing.allocator, &program, solver_backend.internalFacts());
    defer resolved.deinit();
    const certificate_id = resolved.program.claims[0].certificate.?;
    const core_id = resolved.program.certificates[certificate_id.index()].unsat_core.?;
    try std.testing.expectEqualSlices(
        ir.EvidenceId,
        &.{ fixture.proof, dependency_evidence },
        resolved.program.certificates[certificate_id.index()].evidence,
    );

    const certificates = try std.testing.allocator.dupe(ir.SolverCertificate, resolved.program.certificates);
    defer std.testing.allocator.free(certificates);
    const cores = try std.testing.allocator.dupe(ir.UnsatCore, resolved.program.unsat_cores);
    defer std.testing.allocator.free(cores);
    certificates[certificate_id.index()].evidence = &.{fixture.proof};
    cores[core_id.index()].evidence = &.{fixture.proof};
    var tampered = resolved.program;
    tampered.certificates = certificates;
    tampered.unsat_cores = cores;
    const recomputed = try proof_digest.computeAlloc(
        std.testing.allocator,
        &tampered,
        tampered.queries[certificates[certificate_id.index()].query.index()],
        certificates[certificate_id.index()].engine,
        certificates[certificate_id.index()].resolution,
        certificates[certificate_id.index()].evidence,
        &.{},
        cores[core_id.index()].constraints,
    );
    defer std.testing.allocator.free(recomputed);
    certificates[certificate_id.index()].certificate_digest = recomputed;

    var report = try validation.validate(std.testing.allocator, &tampered, .core);
    defer report.deinit();
    try expectDiagnosticAt(&report, .noncanonical_certificate_evidence, @intCast(certificate_id.index()));
    try std.testing.expect(!report.contains(.noncanonical_unsat_core_evidence));
    try std.testing.expect(!report.contains(.certificate_digest_mismatch));
    try std.testing.expect(!report.contains(.certificate_artifact_mismatch));
    try std.testing.expect(!report.contains(.claim_certificate_evidence_mismatch));
}

test "standalone models retain dependency-closed evidence" {
    const fixture = fixtures.arithmetic_module;
    const term_id = ir.SolverTermId.fromIndex(0);
    const constraint_id = ir.ConstraintId.fromIndex(0);
    const query_id = ir.QueryId.fromIndex(0);
    const terms = [_]ir.SolverTerm{.{
        .id = term_id,
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = constraint_id,
        .predicate = term_id,
        .evidence = &.{fixture.proof},
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .find_model,
        .assumptions = &.{constraint_id},
        .goal = term_id,
    }};
    var models = [_]ir.SolverModel{.{
        .id = ir.SolverModelId.fromIndex(0),
        .query = query_id,
        .bindings = &.{},
        .evidence = &.{fixture.proof},
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    program.queries = &queries;
    program.solver_models = &models;

    var clean = try validation.validate(std.testing.allocator, &program, .core);
    defer clean.deinit();
    try std.testing.expect(clean.isClean());

    models[0].evidence = &.{};
    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try expectDiagnosticAt(&report, .noncanonical_solver_model_evidence, 0);
}
