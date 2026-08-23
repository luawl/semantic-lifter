const std = @import("std");
const Io = std.Io;
const ir = @import("ir.zig");
const diagnostics = @import("diagnostics.zig");
const solver_backend = @import("solver_backend.zig");
const solver_unsat_core = @import("solver_unsat_core.zig");
const pre_resolution_admission = @import("pre_resolution_admission.zig");
const proof_digest = @import("proof_digest.zig");
const proof_plan = @import("proof_plan.zig");
const control_flow = @import("control_flow.zig");
const control_query_plan = @import("control_query_plan.zig");
const irreducible_normalize = @import("irreducible_normalize.zig");

pub const ResolvedProgram = struct {
    backing_allocator: std.mem.Allocator,
    arena: *std.heap.ArenaAllocator,
    program: ir.Program,
    solve_report: diagnostics.Report,
    control_result: control_flow.ApplyResult = .{},
    owned_blocks: ?[]ir.Block = null,

    pub fn deinit(self: *ResolvedProgram) void {
        if (self.owned_blocks) |blocks| self.backing_allocator.free(blocks);
        self.solve_report.deinit();
        self.arena.deinit();
        self.backing_allocator.destroy(self.arena);
    }
};

/// Preserve a program after the caller has completed readable admission and
/// confirmed that it carries no solver state. No semantic proof is pending in
/// this case; the emitter still performs its ordinary naming and structuring.
pub fn preserveAdmittedAlloc(
    backing_allocator: std.mem.Allocator,
    program: *const ir.Program,
) !ResolvedProgram {
    var solve_report = diagnostics.Report.init(backing_allocator);
    errdefer solve_report.deinit();
    const arena = try backing_allocator.create(std.heap.ArenaAllocator);
    errdefer backing_allocator.destroy(arena);
    arena.* = std.heap.ArenaAllocator.init(backing_allocator);
    errdefer arena.deinit();
    return .{
        .backing_allocator = backing_allocator,
        .arena = arena,
        .program = program.*,
        .solve_report = solve_report,
    };
}

/// Authenticate and apply only reachable exact branch facts. This is a
/// bounded control checkpoint for large frontends: it deliberately stops
/// before edge-fact derivation, irreducible normalization, and structural
/// feedback. Callers can inspect or validate the resulting CFG before paying
/// for the full post-IR resolver.
pub fn resolveExactControlAlloc(
    backing_allocator: std.mem.Allocator,
    program: *const ir.Program,
    engine: solver_backend.Backend,
) !ResolvedProgram {
    var solve_report = diagnostics.Report.init(backing_allocator);
    errdefer solve_report.deinit();
    const arena = try backing_allocator.create(std.heap.ArenaAllocator);
    errdefer backing_allocator.destroy(arena);
    arena.* = std.heap.ArenaAllocator.init(backing_allocator);
    errdefer arena.deinit();
    const allocator = arena.allocator();

    var current = program.*;
    var models: std.ArrayList(ir.SolverModel) = .empty;
    try models.appendSlice(allocator, program.solver_models);
    var cores: std.ArrayList(ir.UnsatCore) = .empty;
    try cores.appendSlice(allocator, program.unsat_cores);
    var certificates: std.ArrayList(ir.SolverCertificate) = .empty;
    try certificates.appendSlice(allocator, program.certificates);
    var rewrites: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    try rewrites.appendSlice(allocator, program.edge_rewrites);
    var attempted_queries: std.ArrayList(bool) = .empty;
    var owned_blocks: ?[]ir.Block = null;
    errdefer if (owned_blocks) |blocks| backing_allocator.free(blocks);
    var aggregate_control: control_flow.ApplyResult = .{};

    if (control_query_plan.State.hasExactBranchTruth(&current)) {
        var planning = try control_query_plan.State.initExact(allocator, &current);
        current = try planning.expandExactBranches(&current);
        current.solver_models = models.items;
        current.unsat_cores = cores.items;
        current.certificates = certificates.items;
        current.edge_rewrites = rewrites.items;
        try resolvePlannedQueries(
            allocator,
            &current,
            &planning,
            engine,
            &models,
            &cores,
            &certificates,
            &attempted_queries,
            &solve_report,
        );
        current.claims = planning.claims.items;
        current.obligations = planning.obligations.items;
        current.solver_models = models.items;
        current.unsat_cores = cores.items;
        current.certificates = certificates.items;

        const next_blocks = try backing_allocator.alloc(ir.Block, current.blocks.len);
        const control_result = try control_flow.applyProvedBranchesWithState(
            allocator,
            &current,
            next_blocks,
            &rewrites,
        );
        aggregate_control = control_result;
        if (control_result.conflicting_certificate) |conflict| {
            backing_allocator.free(next_blocks);
            aggregate_control.conflicting_certificate = conflict;
        } else if (control_result.rewritten_blocks != 0 or control_result.specialized_edges != 0) {
            owned_blocks = next_blocks;
            current.blocks = next_blocks;
            current.edge_rewrites = rewrites.items;
        } else {
            backing_allocator.free(next_blocks);
        }
    }

    current.solver_models = models.items;
    current.unsat_cores = cores.items;
    current.certificates = certificates.items;
    current.edge_rewrites = rewrites.items;
    try refreshDependencyDigests(allocator, &current, certificates.items);
    return .{
        .backing_allocator = backing_allocator,
        .arena = arena,
        .program = current,
        .solve_report = solve_report,
        .control_result = aggregate_control,
        .owned_blocks = owned_blocks,
    };
}

pub fn hasSerializedSolverState(program: *const ir.Program) bool {
    return program.solver_terms.len != 0 or
        program.constraints.len != 0 or
        program.queries.len != 0 or
        program.solver_models.len != 0 or
        program.unsat_cores.len != 0 or
        program.certificates.len != 0 or
        program.claims.len != 0 or
        program.obligations.len != 0;
}

const QueryResolutionCache = struct {
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    engine: solver_backend.Backend,
    models: *std.ArrayList(ir.SolverModel),
    cores: *std.ArrayList(ir.UnsatCore),
    certificates: *std.ArrayList(ir.SolverCertificate),
    solve_report: *diagnostics.Report,

    fn resolve(self: *QueryResolutionCache, query_id: ir.QueryId, proof_evidence: []const ir.EvidenceId) !?ir.CertificateId {
        if (proof_evidence.len == 0) return null;
        const query_index = query_id.index();
        const query = self.program.queries[query_index];
        var result = try self.engine.solve(self.allocator, self.program, query);
        if (result.resolution == .unknown) {
            const engine = result.engine;
            const reason = result.unknown_reason.?;
            result.deinit(self.allocator);
            try self.solve_report.addSolverUnknown(query.id, engine, reason);
            return null;
        }
        if (try solver_unsat_core.ensureSufficientAlloc(self.allocator, self.program, query, self.engine, &result)) |reason| {
            try self.solve_report.addSolverUnknownForPhase(query.id, result.engine, .unsat_core_replay, reason);
        }

        const durable_evidence = try self.allocator.dupe(ir.EvidenceId, proof_evidence);
        const digest = try proof_digest.computeAlloc(
            self.allocator,
            self.program,
            query,
            result.engine,
            result.resolution,
            durable_evidence,
            result.model.items,
            result.unsat_core.items,
        );
        var model_id: ?ir.SolverModelId = null;
        var core_id: ?ir.UnsatCoreId = null;
        if (resolutionHasModel(query.kind, result.resolution)) {
            model_id = ir.SolverModelId.fromIndex(self.models.items.len);
            try self.models.append(self.allocator, .{
                .id = model_id.?,
                .query = query.id,
                .bindings = result.model.items,
                .evidence = durable_evidence,
            });
        } else {
            core_id = ir.UnsatCoreId.fromIndex(self.cores.items.len);
            try self.cores.append(self.allocator, .{
                .id = core_id.?,
                .query = query.id,
                .constraints = result.unsat_core.items,
                .evidence = durable_evidence,
            });
        }

        const certificate_id = ir.CertificateId.fromIndex(self.certificates.items.len);
        try self.certificates.append(self.allocator, .{
            .id = certificate_id,
            .query = query.id,
            .engine = result.engine,
            .resolution = result.resolution,
            .evidence = durable_evidence,
            .certificate_digest = digest,
            .model = model_id,
            .unsat_core = core_id,
        });
        return certificate_id;
    }
};

pub fn resolveAlloc(
    backing_allocator: std.mem.Allocator,
    program: *const ir.Program,
    engine: solver_backend.Backend,
) !ResolvedProgram {
    var preflight = try pre_resolution_admission.validateAlloc(backing_allocator, program);
    defer preflight.deinit();
    if (!preflight.isClean()) return error.InvalidProgramInput;
    try verifyCoreCertificatesAlloc(backing_allocator, program, engine);

    // A normalized frontend may publish authenticated rewrite history without
    // any remaining solver state. There is no semantic work for the resolver
    // to perform in that shape; re-running whole-program planning only builds
    // transient CFG/proof graphs and can exhaust memory on large holdouts.
    if (!hasSerializedSolverState(program) and program.edge_rewrites.len != 0) {
        return preserveAdmittedAlloc(backing_allocator, program);
    }

    return resolveAdmittedAlloc(backing_allocator, program, engine);
}

fn verifyCoreCertificatesAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    engine: solver_backend.Backend,
) !void {
    for (program.certificates) |certificate| {
        if (certificate.engine == .imported) continue;
        const core_id = certificate.unsat_core orelse continue;
        if (certificate.query.index() >= program.queries.len or core_id.index() >= program.unsat_cores.len) return error.InvalidProgramInput;
        const core = program.unsat_cores[core_id.index()];
        if (core.query != certificate.query) return error.InvalidProgramInput;
        const query = program.queries[certificate.query.index()];
        switch (solver_unsat_core.replayInternal(program, query, certificate.resolution, core.constraints)) {
            .satisfied => continue,
            .contradictory => return error.ContradictoryUnsatCore,
            .unresolved => {},
        }
        switch (try solver_unsat_core.replayBackendAlloc(
            allocator,
            program,
            query,
            certificate.resolution,
            core.constraints,
            engine,
        )) {
            .satisfied => {},
            .contradictory => return error.ContradictoryUnsatCore,
            .unresolved => |reason| return replayUnknownError(reason),
        }
    }
}

const ReplayUnknownError = error{
    SolverReplayBoundedInternalIncompleteness,
    SolverReplayTimeout,
    SolverReplayResourceExhaustion,
    SolverReplayBackendIndeterminacy,
    SolverReplayModelValueUnrepresentability,
};

fn replayUnknownError(reason: solver_backend.UnknownReason) ReplayUnknownError {
    return switch (reason) {
        .bounded_internal_incompleteness => error.SolverReplayBoundedInternalIncompleteness,
        .timeout => error.SolverReplayTimeout,
        .resource_exhaustion => error.SolverReplayResourceExhaustion,
        .backend_indeterminacy => error.SolverReplayBackendIndeterminacy,
        .model_value_unrepresentability => error.SolverReplayModelValueUnrepresentability,
    };
}

test "persisted core replay exposes typed transient rejection causes" {
    const cases = [_]struct {
        reason: solver_backend.UnknownReason,
        expected: ReplayUnknownError,
    }{
        .{ .reason = .bounded_internal_incompleteness, .expected = error.SolverReplayBoundedInternalIncompleteness },
        .{ .reason = .timeout, .expected = error.SolverReplayTimeout },
        .{ .reason = .resource_exhaustion, .expected = error.SolverReplayResourceExhaustion },
        .{ .reason = .backend_indeterminacy, .expected = error.SolverReplayBackendIndeterminacy },
        .{ .reason = .model_value_unrepresentability, .expected = error.SolverReplayModelValueUnrepresentability },
    };
    for (cases) |case| try std.testing.expectEqual(case.expected, replayUnknownError(case.reason));
}

fn resolveAdmittedAlloc(
    backing_allocator: std.mem.Allocator,
    program: *const ir.Program,
    engine: solver_backend.Backend,
) !ResolvedProgram {
    var solve_report = diagnostics.Report.init(backing_allocator);
    errdefer solve_report.deinit();
    const arena = try backing_allocator.create(std.heap.ArenaAllocator);
    errdefer backing_allocator.destroy(arena);
    arena.* = std.heap.ArenaAllocator.init(backing_allocator);
    errdefer arena.deinit();
    const allocator = arena.allocator();
    var current = program.*;
    var models: std.ArrayList(ir.SolverModel) = .empty;
    try models.appendSlice(allocator, program.solver_models);
    var cores: std.ArrayList(ir.UnsatCore) = .empty;
    try cores.appendSlice(allocator, program.unsat_cores);
    var certificates: std.ArrayList(ir.SolverCertificate) = .empty;
    try certificates.appendSlice(allocator, program.certificates);
    var rewrites: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    try rewrites.appendSlice(allocator, current.edge_rewrites);
    var attempted_queries: std.ArrayList(bool) = .empty;
    var owned_blocks: ?[]ir.Block = null;
    errdefer if (owned_blocks) |blocks| backing_allocator.free(blocks);
    var aggregate_control: control_flow.ApplyResult = .{};

    // Direct exact branch facts are already semantic evidence. Resolve their
    // authenticated obligations before structural normalization can retain a
    // dead arm as a loop boundary. The lightweight state copy avoids deriving
    // the full edge-fact graph before this simplification.
    const exact_prepass_start = Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds;
    const has_exact_branch = control_query_plan.State.hasExactBranchTruth(&current);
    if (has_exact_branch) {
        std.debug.print(
            "control_phase exact_prepass_begin functions={} blocks={} terms={} queries={}\\n",
            .{ current.functions.len, current.blocks.len, current.solver_terms.len, current.queries.len },
        );
        var initial_planning = try control_query_plan.State.initExact(allocator, &current);
        current = try initial_planning.expandExactBranches(&current);
        std.debug.print(
            "control_phase exact_prepass_expanded terms={} queries={} obligations={} claims={} ms={}\\n",
            .{
                current.solver_terms.len,
                current.queries.len,
                current.obligations.len,
                current.claims.len,
                @divTrunc(Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds - exact_prepass_start, std.time.ns_per_ms),
            },
        );
        current.solver_models = models.items;
        current.unsat_cores = cores.items;
        current.certificates = certificates.items;
        current.edge_rewrites = rewrites.items;
        try resolvePlannedQueries(
            allocator,
            &current,
            &initial_planning,
            engine,
            &models,
            &cores,
            &certificates,
            &attempted_queries,
            &solve_report,
        );
        std.debug.print(
            "control_phase exact_prepass_solved models={} cores={} certificates={} ms={}\\n",
            .{
                models.items.len,
                cores.items.len,
                certificates.items.len,
                @divTrunc(Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds - exact_prepass_start, std.time.ns_per_ms),
            },
        );
        current.claims = initial_planning.claims.items;
        current.obligations = initial_planning.obligations.items;

        const next_blocks = try backing_allocator.alloc(ir.Block, current.blocks.len);
        const initial_control = try control_flow.applyProvedBranchesWithState(
            allocator,
            &current,
            next_blocks,
            &rewrites,
        );
        if (initial_control.conflicting_certificate) |conflict| {
            backing_allocator.free(next_blocks);
            aggregate_control.conflicting_certificate = conflict;
        } else if (initial_control.rewritten_blocks != 0 or initial_control.specialized_edges != 0) {
            aggregate_control.rewritten_blocks += initial_control.rewritten_blocks;
            aggregate_control.specialized_edges += initial_control.specialized_edges;
            owned_blocks = next_blocks;
            current.edge_rewrites = rewrites.items;
        } else {
            backing_allocator.free(next_blocks);
        }
        std.debug.print(
            "control_phase exact_prepass_applied rewritten={} specialized={} ms={}\\n",
            .{
                initial_control.rewritten_blocks,
                initial_control.specialized_edges,
                @divTrunc(Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds - exact_prepass_start, std.time.ns_per_ms),
            },
        );
    }

    const control_normalize_start = Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds;
    const control_normalized = try irreducible_normalize.normalizeControlWithScratchInArena(
        allocator,
        backing_allocator,
        &current,
    );
    std.debug.print(
        "control_phase control_normalize_done has_exact={} blocks={} rewrites={} ms={}\\n",
        .{
            has_exact_branch,
            control_normalized.program.blocks.len,
            control_normalized.program.edge_rewrites.len,
            @divTrunc(Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds - control_normalize_start, std.time.ns_per_ms),
        },
    );
    if (owned_blocks) |blocks| {
        backing_allocator.free(blocks);
        owned_blocks = null;
    }
    current = control_normalized.program;
    rewrites = .empty;
    try rewrites.appendSlice(allocator, current.edge_rewrites);
    current.edge_rewrites = rewrites.items;

    const planning_init_start = Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds;
    std.debug.print(
        "control_phase planning_init_begin blocks={} rewrites={} terms={} queries={}\\n",
        .{ current.blocks.len, current.edge_rewrites.len, current.solver_terms.len, current.queries.len },
    );
    var planning = try control_query_plan.State.init(allocator, &current);
    std.debug.print(
        "control_phase planning_init_done terms={} queries={} obligations={} claims={} ms={}\\n",
        .{
            planning.terms.items.len,
            planning.queries.items.len,
            planning.obligations.items.len,
            planning.claims.items.len,
            @divTrunc(Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds - planning_init_start, std.time.ns_per_ms),
        },
    );
    current = try planning.expand(&current);
    std.debug.print(
        "control_phase planning_expand_done terms={} queries={} obligations={} claims={}\\n",
        .{ current.solver_terms.len, current.queries.len, current.obligations.len, current.claims.len },
    );

    // A frontend may publish an IR whose control history is already
    // authenticated and whose proof graph is empty. The control-only pass
    // above is still required to canonicalize that history, but the later
    // semantic-feedback pass has no query or obligation it can discharge.
    // Preserve the normalized program instead of replaying every function's
    // full irreducible search.
    if (current.queries.len == 0 and current.claims.len == 0 and current.obligations.len == 0) {
        current.solver_models = models.items;
        current.unsat_cores = cores.items;
        current.certificates = certificates.items;
        try refreshDependencyDigests(allocator, &current, certificates.items);
        return .{
            .backing_allocator = backing_allocator,
            .arena = arena,
            .program = current,
            .solve_report = solve_report,
            .control_result = aggregate_control,
            .owned_blocks = owned_blocks,
        };
    }

    var edge_slots: usize = 0;
    for (current.blocks) |block| edge_slots += switch (block.terminator) {
        .jump => 1,
        .branch => 2,
        else => 0,
    };
    const block_bound = @max(current.blocks.len, 1);
    const iteration_limit = std.math.mul(usize, block_bound, edge_slots + 1) catch return error.ControlRewriteLimitOverflow;
    var iteration: usize = 0;
    while (iteration < iteration_limit) : (iteration += 1) {
        if (iteration != 0) current = try planning.expand(&current);
        current.solver_models = models.items;
        current.unsat_cores = cores.items;
        current.certificates = certificates.items;
        current.edge_rewrites = rewrites.items;
        try resolvePlannedQueries(
            allocator,
            &current,
            &planning,
            engine,
            &models,
            &cores,
            &certificates,
            &attempted_queries,
            &solve_report,
        );
        if (try planning.materializeProvedControlBranches(&current)) {
            current.obligations = planning.obligations.items;
            try refreshDependencyDigests(allocator, &current, certificates.items);
        }

        const release_deferred_branch_arms = try planning.hasDeferredBranchArms(&current);
        if (release_deferred_branch_arms) planning.releaseDeferredBranchArms();

        const next_blocks = try backing_allocator.alloc(ir.Block, current.blocks.len);
        const control_result = try control_flow.applyProvedBranchesWithState(allocator, &current, next_blocks, &rewrites);
        if (control_result.conflicting_certificate) |conflict| {
            backing_allocator.free(next_blocks);
            aggregate_control.conflicting_certificate = conflict;
            break;
        }
        if (control_result.rewritten_blocks == 0 and control_result.specialized_edges == 0) {
            backing_allocator.free(next_blocks);
            if (release_deferred_branch_arms) continue;
            break;
        }
        aggregate_control.rewritten_blocks += control_result.rewritten_blocks;
        aggregate_control.specialized_edges += control_result.specialized_edges;
        if (owned_blocks) |blocks| backing_allocator.free(blocks);
        owned_blocks = next_blocks;
        current.edge_rewrites = rewrites.items;
        const renormalized = try irreducible_normalize.normalizeControlWithScratchInArena(
            allocator,
            backing_allocator,
            &current,
        );
        current = renormalized.program;
        rewrites = .empty;
        try rewrites.appendSlice(allocator, current.edge_rewrites);
        current.edge_rewrites = rewrites.items;
        if (owned_blocks) |blocks| backing_allocator.free(blocks);
        owned_blocks = null;
    } else {
        return error.NonConvergentControlRewrite;
    }

    current = planning.programView(&current);
    current.solver_models = models.items;
    current.unsat_cores = cores.items;
    current.certificates = certificates.items;
    current.edge_rewrites = rewrites.items;
    const final_normalized = try irreducible_normalize.normalizeWithScratchInArena(
        allocator,
        backing_allocator,
        &current,
    );
    current = final_normalized.program;
    rewrites = .empty;
    try rewrites.appendSlice(allocator, current.edge_rewrites);
    current.edge_rewrites = rewrites.items;
    try refreshDependencyDigests(allocator, &current, certificates.items);
    return .{
        .backing_allocator = backing_allocator,
        .arena = arena,
        .program = current,
        .solve_report = solve_report,
        .control_result = aggregate_control,
        .owned_blocks = owned_blocks,
    };
}

fn resolvePlannedQueries(
    allocator: std.mem.Allocator,
    current: *ir.Program,
    planning: *control_query_plan.State,
    engine: solver_backend.Backend,
    models: *std.ArrayList(ir.SolverModel),
    cores: *std.ArrayList(ir.UnsatCore),
    certificates: *std.ArrayList(ir.SolverCertificate),
    attempted_queries: *std.ArrayList(bool),
    solve_report: *diagnostics.Report,
) !void {
    while (attempted_queries.items.len < current.queries.len) {
        try attempted_queries.append(allocator, false);
    }

    var cache: QueryResolutionCache = .{
        .allocator = allocator,
        .program = current,
        .engine = engine,
        .models = models,
        .cores = cores,
        .certificates = certificates,
        .solve_report = solve_report,
    };
    var plan = try proof_plan.Plan.init(allocator, current);
    defer plan.deinit();
    for (plan.items) |work| {
        if (attempted_queries.items[work.query.index()]) continue;
        attempted_queries.items[work.query.index()] = true;
        const certificate_id = try cache.resolve(work.query, work.evidence) orelse continue;
        const certificate = certificates.items[certificate_id.index()];
        for (work.consumers) |consumer| switch (consumer) {
            .claim => |claim_id| {
                const claim = &planning.claims.items[claim_id.index()];
                claim.status = if (certificate.resolution == .proved) .proved else .disproved;
                claim.certificate = certificate_id;
            },
            .obligation => |obligation_id| {
                const obligation = &planning.obligations.items[obligation_id.index()];
                if (certificate.resolution == .proved) obligation.status = .discharged;
                obligation.certificate = certificate_id;
            },
        };
        current.solver_models = models.items;
        current.unsat_cores = cores.items;
        current.certificates = certificates.items;
    }
    current.claims = planning.claims.items;
    current.obligations = planning.obligations.items;
}

fn refreshDependencyDigests(
    allocator: std.mem.Allocator,
    program: *ir.Program,
    certificates: []ir.SolverCertificate,
) (error{InvalidProgramInput} || std.mem.Allocator.Error)!void {
    for (certificates) |*certificate| {
        const recorded = certificate.certificate_digest orelse continue;
        const framework_owned = certificate.engine != .imported and proof_digest.isFrameworkDigest(recorded);
        if (!framework_owned and
            !certificateUsedByControlBranch(program, certificate.id) and
            !std.mem.startsWith(u8, recorded, proof_digest.lexical_binding_prefix) and
            !std.mem.startsWith(u8, recorded, proof_digest.runtime_value_prefix) and
            !std.mem.startsWith(u8, recorded, proof_digest.combined_runtime_prefix) and
            !std.mem.startsWith(u8, recorded, proof_digest.control_branch_prefix)) continue;
        if (certificate.query.index() >= program.queries.len) return error.InvalidProgramInput;

        var model: []const ir.SolverModelBinding = &.{};
        if (certificate.model) |model_id| {
            if (model_id.index() >= program.solver_models.len) return error.InvalidProgramInput;
            model = program.solver_models[model_id.index()].bindings;
        }
        var unsat_core: []const ir.ConstraintId = &.{};
        if (certificate.unsat_core) |core_id| {
            if (core_id.index() >= program.unsat_cores.len) return error.InvalidProgramInput;
            unsat_core = program.unsat_cores[core_id.index()].constraints;
        }

        certificate.certificate_digest = proof_digest.computeAlloc(
            allocator,
            program,
            program.queries[certificate.query.index()],
            certificate.engine,
            certificate.resolution,
            certificate.evidence,
            model,
            unsat_core,
        ) catch |err| switch (err) {
            error.InvalidDigestInput => return error.InvalidProgramInput,
            error.OutOfMemory => return error.OutOfMemory,
        };
    }
}

/// Refresh proof digests after a caller has applied an authenticated generic
/// CFG transformation. Direct normalizer/fixture frontends use this boundary
/// before publication; the full resolver already performs the same refresh as
/// part of its transaction.
pub fn refreshSerializedProofDigestsAlloc(
    allocator: std.mem.Allocator,
    program: *ir.Program,
) (error{InvalidProgramInput} || std.mem.Allocator.Error)!void {
    // Parsed programs expose immutable slices, but publication owns the
    // backing storage and has an explicit mutable program boundary here.
    try refreshDependencyDigests(allocator, program, @constCast(program.certificates));
}

fn certificateUsedByControlBranch(program: *const ir.Program, certificate_id: ir.CertificateId) bool {
    for (program.obligations) |obligation| {
        if (obligation.certificate == null or obligation.certificate.? != certificate_id) continue;
        switch (obligation.subject) {
            .control_branch => return true,
            else => {},
        }
    }
    return false;
}

fn resolutionHasModel(kind: ir.QueryKind, resolution: ir.SolverResolution) bool {
    return switch (resolution) {
        .unknown => false,
        .proved => kind == .find_model,
        .disproved => kind != .find_model,
    };
}

test "detached framework proofs refresh after edge topology changes" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = fixture.v_is_negative },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{fixture.proof},
        .scope = .{ .edge = .{
            .source = fixture.b_entry,
            .kind = .branch_then,
            .target = fixture.b_negative,
        } },
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(0),
    };
    const queries = [_]ir.SolverQuery{query};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    program.queries = &queries;

    const initial = try proof_digest.computeAlloc(
        std.testing.allocator,
        &program,
        query,
        .z3,
        .proved,
        &.{fixture.proof},
        &.{},
        &.{},
    );
    defer std.testing.allocator.free(initial);
    try std.testing.expect(std.mem.startsWith(u8, initial, proof_digest.prefix));

    var certificates = [_]ir.SolverCertificate{.{
        .id = ir.CertificateId.fromIndex(0),
        .query = query.id,
        .engine = .z3,
        .resolution = .proved,
        .evidence = &.{fixture.proof},
        .certificate_digest = initial,
    }};
    program.certificates = &certificates;
    var blocks = fixture.blocks;
    blocks[fixture.b_negative.index()].terminator = .{ .return_values = &.{fixture.v_negated} };
    program.blocks = &blocks;

    try refreshDependencyDigests(std.testing.allocator, &program, &certificates);
    const refreshed = certificates[0].certificate_digest.?;
    defer if (refreshed.ptr != initial.ptr) std.testing.allocator.free(@constCast(refreshed));
    const expected = try proof_digest.computeAlloc(
        std.testing.allocator,
        &program,
        query,
        .z3,
        .proved,
        &.{fixture.proof},
        &.{},
        &.{},
    );
    defer std.testing.allocator.free(expected);
    try std.testing.expect(!std.mem.eql(u8, initial, refreshed));
    try std.testing.expectEqualStrings(expected, refreshed);
}
