const std = @import("std");
const ir = @import("ir.zig");
const solver = @import("solver.zig");
const diagnostics = @import("diagnostics.zig");
const proof_digest = @import("proof_digest.zig");
const proof_closure = @import("proof_closure.zig");
const solver_term = @import("solver_term.zig");
const solver_model = @import("solver_model.zig");
const solver_unsat_core = @import("solver_unsat_core.zig");

pub fn validate(report: *diagnostics.Report, program: *const ir.Program) !void {
    for (program.solver_models, 0..) |model, model_index| {
        const valid_query = validId(model.query, program.queries.len);
        if (!valid_query) try report.add(.invalid_solver_model_reference, model_index);
        var query_terms: ?solver_term.QueryTermSet = null;
        defer if (query_terms) |*set| set.deinit();
        if (valid_query) {
            query_terms = solver_term.QueryTermSet.init(report.allocator, program, program.queries[model.query.index()]) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.InvalidQueryReference, error.InvalidTermGraph => null,
            };
        }
        var model_shape_valid = valid_query and query_terms != null;
        for (model.evidence) |evidence_id| if (!validId(evidence_id, program.evidence.len)) try report.add(.invalid_evidence_reference, model_index);
        for (model.bindings, 0..) |binding, binding_index| {
            if (!validId(binding.term, program.solver_terms.len)) {
                try report.add(.invalid_solver_model_reference, model_index);
                model_shape_valid = false;
            } else {
                if (query_terms) |set| {
                    if (!set.contains(binding.term)) {
                        try report.add(.irrelevant_solver_model_term, model_index);
                        model_shape_valid = false;
                    }
                }
                if (!solver_model.modelValueMatchesSort(binding.value, program.solver_terms[binding.term.index()].sort)) {
                    try report.add(.invalid_solver_model_value, model_index);
                    model_shape_valid = false;
                }
            }
            for (model.bindings[0..binding_index]) |prior| {
                if (prior.term == binding.term) {
                    try report.add(.duplicate_solver_model_term, model_index);
                    model_shape_valid = false;
                    break;
                }
            }
        }
        if (model_shape_valid and
            (!solver_model.dynamicIdentitiesCanonical(program, model.bindings) or
                !solver_model.dynamicBindingsSemanticallyCoherent(program, model.bindings)))
        {
            try report.add(.invalid_solver_model_value, model_index);
            model_shape_valid = false;
        }
        if (model_shape_valid) {
            const replay = solver_model.replayAlloc(
                report.allocator,
                program,
                program.queries[model.query.index()],
                model.bindings,
            ) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.InvalidModelInput, error.InvalidValue => null,
            };
            if (replay) |result| switch (result) {
                .satisfied => {},
                .contradictory => try report.add(.contradictory_solver_model, model_index),
                .incomplete => try report.add(.incomplete_solver_model, model_index),
            };
            if (!modelHasCertificate(program, model.id)) {
                try validateEvidenceClosure(
                    report,
                    program,
                    program.queries[model.query.index()],
                    model.evidence,
                    model.bindings,
                    .noncanonical_solver_model_evidence,
                    model_index,
                );
            }
        }
    }

    for (program.unsat_cores, 0..) |core, core_index| {
        var core_shape_valid = validId(core.query, program.queries.len);
        if (!core_shape_valid) try report.add(.invalid_unsat_core_reference, core_index);
        for (core.evidence) |evidence_id| {
            if (!validId(evidence_id, program.evidence.len)) {
                core_shape_valid = false;
                try report.add(.invalid_evidence_reference, core_index);
            }
        }
        for (core.constraints, 0..) |constraint_id, constraint_index| {
            if (!validId(constraint_id, program.constraints.len) or
                !validId(core.query, program.queries.len) or
                !queryHasAssumption(program.queries[core.query.index()], constraint_id))
            {
                core_shape_valid = false;
                try report.add(.invalid_unsat_core_constraint, core_index);
            } else if (program.constraints[constraint_id.index()].evidence.len == 0) {
                core_shape_valid = false;
                try report.add(.unsat_core_constraint_without_evidence, core_index);
            }
            for (core.constraints[0..constraint_index]) |prior_id| {
                if (prior_id == constraint_id) {
                    core_shape_valid = false;
                    try report.add(.duplicate_unsat_core_constraint, core_index);
                    break;
                }
            }
        }
        if (core_shape_valid and !coreHasCertificate(program, core.id)) {
            var query = program.queries[core.query.index()];
            query.assumptions = core.constraints;
            try validateEvidenceClosure(
                report,
                program,
                query,
                core.evidence,
                &.{},
                .noncanonical_unsat_core_evidence,
                core_index,
            );
            const resolution: ir.SolverResolution = if (solver_unsat_core.resolutionUsesCore(query.kind, .proved)) .proved else .disproved;
            switch (solver_unsat_core.replayInternal(program, query, resolution, core.constraints)) {
                .satisfied => {},
                .contradictory => try report.add(.contradictory_unsat_core, core_index),
                .unresolved => try report.add(.incomplete_unsat_core, core_index),
            }
        }
    }

    for (program.certificates, 0..) |certificate, certificate_index| {
        if (!validId(certificate.query, program.queries.len)) {
            try report.add(.invalid_certificate_reference, certificate_index);
        } else {
            switch (certificate.engine) {
                .internal_facts => {
                    const replayed = solver.solve(program, program.queries[certificate.query.index()]);
                    if (replayed != certificate.resolution) try report.add(.certificate_replay_mismatch, certificate_index);
                },
                .z3 => {},
                .imported => {
                    const has_digest = certificate.certificate_digest != null and certificate.certificate_digest.?.len != 0;
                    if (certificate.resolution != .unknown and (certificate.evidence.len == 0 or !has_digest)) {
                        try report.add(.certificate_without_proof, certificate_index);
                    }
                },
            }
            if (certificate.engine != .imported and certificate.resolution != .unknown) {
                const has_digest = certificate.certificate_digest != null and
                    proof_digest.isFrameworkDigest(certificate.certificate_digest.?);
                if (certificate.evidence.len == 0 or !has_digest) {
                    try report.add(.certificate_without_proof, certificate_index);
                }
            }
            try validateCertificateArtifacts(report, program, certificate, certificate_index);
            try validateCertificateCoreReplay(report, program, certificate);
            try validateCertificateEvidence(report, program, certificate, certificate_index);
            try validateCertificateDigest(report, program, certificate, certificate_index);
        }
        for (certificate.evidence) |evidence_id| if (!validId(evidence_id, program.evidence.len)) try report.add(.invalid_evidence_reference, certificate_index);
    }
}

fn queryHasAssumption(query: ir.SolverQuery, constraint_id: ir.ConstraintId) bool {
    for (query.assumptions) |assumption_id| {
        if (assumption_id == constraint_id) return true;
    }
    return false;
}

fn coreHasCertificate(program: *const ir.Program, core_id: ir.UnsatCoreId) bool {
    for (program.certificates) |certificate| {
        if (certificate.unsat_core != null and certificate.unsat_core.? == core_id) return true;
    }
    return false;
}

fn modelHasCertificate(program: *const ir.Program, model_id: ir.SolverModelId) bool {
    for (program.certificates) |certificate| {
        if (certificate.model != null and certificate.model.? == model_id) return true;
    }
    return false;
}

fn validateCertificateArtifacts(report: *diagnostics.Report, program: *const ir.Program, certificate: ir.SolverCertificate, certificate_index: usize) !void {
    if (certificate.model) |model_id| {
        if (!validId(model_id, program.solver_models.len) or program.solver_models[model_id.index()].query != certificate.query) {
            try report.add(.invalid_certificate_reference, certificate_index);
        } else if (!std.mem.eql(ir.EvidenceId, program.solver_models[model_id.index()].evidence, certificate.evidence)) {
            try report.add(.certificate_artifact_mismatch, certificate_index);
        }
    }
    if (certificate.unsat_core) |core_id| {
        if (!validId(core_id, program.unsat_cores.len) or program.unsat_cores[core_id.index()].query != certificate.query) {
            try report.add(.invalid_certificate_reference, certificate_index);
        } else if (!std.mem.eql(ir.EvidenceId, program.unsat_cores[core_id.index()].evidence, certificate.evidence)) {
            try report.add(.certificate_artifact_mismatch, certificate_index);
        }
    }
    if (certificate.model != null and certificate.unsat_core != null) {
        try report.add(.certificate_artifact_mismatch, certificate_index);
        return;
    }
    if (!validId(certificate.query, program.queries.len)) return;
    const expects_model = switch (certificate.resolution) {
        .unknown => null,
        .proved => program.queries[certificate.query.index()].kind == .find_model,
        .disproved => program.queries[certificate.query.index()].kind != .find_model,
    };
    if (expects_model) |model_expected| {
        if ((certificate.model != null) != model_expected or (certificate.unsat_core != null) == model_expected) {
            if (certificate.model != null or certificate.unsat_core != null) try report.add(.certificate_artifact_mismatch, certificate_index);
        }
    } else if (certificate.model != null or certificate.unsat_core != null) {
        try report.add(.certificate_artifact_mismatch, certificate_index);
    }
    if (certificate.engine != .imported and certificate.resolution != .unknown and certificate.model == null and certificate.unsat_core == null) {
        try report.add(.certificate_without_artifact, certificate_index);
    }
}

fn validateCertificateCoreReplay(report: *diagnostics.Report, program: *const ir.Program, certificate: ir.SolverCertificate) !void {
    if (certificate.engine == .imported) return;
    const core_id = certificate.unsat_core orelse return;
    if (!validId(certificate.query, program.queries.len) or !validId(core_id, program.unsat_cores.len)) return;
    const core = program.unsat_cores[core_id.index()];
    if (core.query != certificate.query) return;
    switch (solver_unsat_core.replayInternal(
        program,
        program.queries[certificate.query.index()],
        certificate.resolution,
        core.constraints,
    )) {
        .satisfied => {},
        .contradictory => try report.add(.contradictory_unsat_core, core_id.index()),
        .unresolved => if (certificate.engine == .internal_facts) try report.add(.incomplete_unsat_core, core_id.index()),
    }
}

fn validateCertificateEvidence(
    report: *diagnostics.Report,
    program: *const ir.Program,
    certificate: ir.SolverCertificate,
    certificate_index: usize,
) std.mem.Allocator.Error!void {
    if (certificate.engine == .imported or certificate.resolution == .unknown or !validId(certificate.query, program.queries.len)) return;
    var model: []const ir.SolverModelBinding = &.{};
    if (certificate.model) |model_id| {
        if (!validId(model_id, program.solver_models.len)) return;
        model = program.solver_models[model_id.index()].bindings;
    }
    try validateEvidenceClosure(
        report,
        program,
        program.queries[certificate.query.index()],
        certificate.evidence,
        model,
        .noncanonical_certificate_evidence,
        certificate_index,
    );
}

fn validateEvidenceClosure(
    report: *diagnostics.Report,
    program: *const ir.Program,
    query: ir.SolverQuery,
    evidence: []const ir.EvidenceId,
    model: []const ir.SolverModelBinding,
    code: diagnostics.Code,
    entity_index: usize,
) std.mem.Allocator.Error!void {
    var closure = proof_closure.Closure.init(report.allocator, program, query, evidence, model) catch |err| switch (err) {
        error.InvalidClosureInput => return,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer closure.deinit();
    if (!closure.evidenceMatches(evidence)) try report.add(code, entity_index);
}

fn validateCertificateDigest(report: *diagnostics.Report, program: *const ir.Program, certificate: ir.SolverCertificate, certificate_index: usize) std.mem.Allocator.Error!void {
    const recorded = certificate.certificate_digest orelse return;
    if (!proof_digest.isFrameworkDigest(recorded)) {
        if (certificate.engine != .imported and proof_digest.isLegacyFrameworkDigest(recorded)) {
            try report.add(.certificate_digest_mismatch, certificate_index);
        }
        return;
    }
    if (!validId(certificate.query, program.queries.len)) return;

    var model: []const ir.SolverModelBinding = &.{};
    if (certificate.model) |model_id| {
        if (!validId(model_id, program.solver_models.len)) return;
        model = program.solver_models[model_id.index()].bindings;
    }
    var unsat_core: []const ir.ConstraintId = &.{};
    if (certificate.unsat_core) |core_id| {
        if (!validId(core_id, program.unsat_cores.len)) return;
        unsat_core = program.unsat_cores[core_id.index()].constraints;
    }

    const expected = proof_digest.computeAlloc(
        report.allocator,
        program,
        program.queries[certificate.query.index()],
        certificate.engine,
        certificate.resolution,
        certificate.evidence,
        model,
        unsat_core,
    ) catch |err| switch (err) {
        error.InvalidDigestInput => {
            try report.add(.certificate_digest_mismatch, certificate_index);
            return;
        },
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer report.allocator.free(expected);
    if (!std.mem.eql(u8, recorded, expected)) try report.add(.certificate_digest_mismatch, certificate_index);
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}
