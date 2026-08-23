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

test "proof forwarding renormalizes irreducible entries before serialization" {
    const function_id = ir.FunctionId.fromIndex(0);
    const child_function_id = ir.FunctionId.fromIndex(1);
    const entry_id = ir.BlockId.fromIndex(0);
    const primary_id = ir.BlockId.fromIndex(1);
    const secondary_id = ir.BlockId.fromIndex(2);
    const exit_id = ir.BlockId.fromIndex(3);
    const child_block_id = ir.BlockId.fromIndex(4);
    const entry_zero_id = ir.InstructionId.fromIndex(0);
    const primary_zero_id = ir.InstructionId.fromIndex(1);
    const condition_id = ir.InstructionId.fromIndex(2);
    const secondary_one_id = ir.InstructionId.fromIndex(3);
    const closure_id = ir.InstructionId.fromIndex(4);
    const selector = ir.ValueId.fromIndex(0);
    const entry_zero = ir.ValueId.fromIndex(1);
    const primary_value = ir.ValueId.fromIndex(2);
    const secondary_value = ir.ValueId.fromIndex(3);
    const exit_value = ir.ValueId.fromIndex(4);
    const primary_zero = ir.ValueId.fromIndex(5);
    const condition = ir.ValueId.fromIndex(6);
    const secondary_one = ir.ValueId.fromIndex(7);
    const closure_value = ir.ValueId.fromIndex(8);
    const child_captured_value = ir.ValueId.fromIndex(9);
    const child_capture = ir.CaptureId.fromIndex(0);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{
            .id = entry_zero,
            .function = function_id,
            .type = .integer,
            .origin = .{ .instruction_result = .{ .instruction = entry_zero_id, .index = 0 } },
        },
        .{
            .id = primary_value,
            .function = function_id,
            .type = .integer,
            .origin = .{ .block_parameter = .{ .block = primary_id, .index = 0 } },
        },
        .{
            .id = secondary_value,
            .function = function_id,
            .type = .integer,
            .origin = .{ .block_parameter = .{ .block = secondary_id, .index = 0 } },
        },
        .{
            .id = exit_value,
            .function = function_id,
            .type = .integer,
            .origin = .{ .block_parameter = .{ .block = exit_id, .index = 0 } },
        },
        .{
            .id = primary_zero,
            .function = function_id,
            .type = .integer,
            .origin = .{ .instruction_result = .{ .instruction = primary_zero_id, .index = 0 } },
        },
        .{
            .id = condition,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .instruction_result = .{ .instruction = condition_id, .index = 0 } },
        },
        .{
            .id = secondary_one,
            .function = function_id,
            .type = .integer,
            .origin = .{ .instruction_result = .{ .instruction = secondary_one_id, .index = 0 } },
        },
        .{
            .id = closure_value,
            .function = function_id,
            .type = .function,
            .origin = .{ .instruction_result = .{ .instruction = closure_id, .index = 0 } },
        },
        .{
            .id = child_captured_value,
            .function = child_function_id,
            .type = .integer,
            .origin = .{ .capture = child_capture },
        },
    };
    const captures = [_]ir.Capture{.{
        .id = child_capture,
        .function = child_function_id,
        .kind = .{ .immutable_value = child_captured_value },
        .evidence = &.{evidence_id},
    }};
    const instructions = [_]ir.Instruction{
        .{
            .id = entry_zero_id,
            .block = entry_id,
            .operation = .{ .constant = .{ .integer = "0" } },
            .results = &.{entry_zero},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
        .{
            .id = primary_zero_id,
            .block = primary_id,
            .operation = .{ .constant = .{ .integer = "0" } },
            .results = &.{primary_zero},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
        .{
            .id = condition_id,
            .block = primary_id,
            .operation = .{ .binary = .{
                .operator = .equal,
                .left = primary_value,
                .right = primary_zero,
            } },
            .results = &.{condition},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
        .{
            .id = secondary_one_id,
            .block = secondary_id,
            .operation = .{ .constant = .{ .integer = "1" } },
            .results = &.{secondary_one},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
        .{
            .id = closure_id,
            .block = secondary_id,
            .operation = .{ .make_closure = .{
                .function = child_function_id,
                .bindings = &.{.{ .value = secondary_value }},
            } },
            .results = &.{closure_value},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
    };
    const blocks = [_]ir.Block{
        .{
            .id = entry_id,
            .function = function_id,
            .instructions = &.{entry_zero_id},
            .terminator = .{ .branch = .{
                .condition = selector,
                .then_edge = .{ .target = secondary_id, .arguments = &.{entry_zero} },
                .else_edge = .{ .target = primary_id, .arguments = &.{entry_zero} },
            } },
            .evidence = &.{evidence_id},
        },
        .{
            .id = primary_id,
            .function = function_id,
            .parameters = &.{primary_value},
            .instructions = &.{ primary_zero_id, condition_id },
            .terminator = .{ .branch = .{
                .condition = condition,
                .then_edge = .{ .target = secondary_id, .arguments = &.{primary_value} },
                .else_edge = .{ .target = exit_id, .arguments = &.{primary_value} },
            } },
            .evidence = &.{evidence_id},
        },
        .{
            .id = secondary_id,
            .function = function_id,
            .parameters = &.{secondary_value},
            .instructions = &.{ secondary_one_id, closure_id },
            .terminator = .{ .jump = .{ .target = primary_id, .arguments = &.{secondary_one} } },
            .evidence = &.{evidence_id},
        },
        .{
            .id = exit_id,
            .function = function_id,
            .parameters = &.{exit_value},
            .terminator = .{ .return_values = &.{exit_value} },
            .evidence = &.{evidence_id},
        },
        .{
            .id = child_block_id,
            .function = child_function_id,
            .terminator = .{ .return_values = &.{child_captured_value} },
            .evidence = &.{evidence_id},
        },
    };
    const functions = [_]ir.Function{
        .{
            .id = function_id,
            .parameters = &.{selector},
            .blocks = &.{ entry_id, primary_id, secondary_id, exit_id },
            .entry_block = entry_id,
            .evidence = &.{evidence_id},
        },
        .{
            .id = child_function_id,
            .lexical_parent = function_id,
            .captures = &.{child_capture},
            .blocks = &.{child_block_id},
            .entry_block = child_block_id,
            .evidence = &.{evidence_id},
        },
    };
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .structural_derivation,
        .locator = "fixture:post-proof-irreducible-fixpoint",
    }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = closure_value } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(1),
    }};
    const claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(1),
        .status = .unproven,
        .required_for_emission = true,
        .evidence = &.{evidence_id},
        .query = ir.QueryId.fromIndex(0),
    }};
    const program: ir.Program = .{
        .program_id = "post-proof-irreducible-fixpoint",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .captures = &captures,
        .evidence = &evidence,
        .solver_terms = &terms,
        .queries = &queries,
        .claims = &claims,
    };

    var resolved = try resolveAlloc(std.testing.allocator, &program, solver_backend.internalFacts());
    defer resolved.deinit();
    try std.testing.expectEqual(@as(usize, 7), resolved.program.blocks.len);
    try std.testing.expectEqual(@as(usize, 3), resolved.program.edge_rewrites.len);
    try std.testing.expectEqual(ir.EdgeRewriteRule.node_split, resolved.program.edge_rewrites[0].rule);
    try std.testing.expectEqual(ir.EdgeRewriteRule.proved_branch, resolved.program.edge_rewrites[1].rule);
    try std.testing.expectEqual(ir.EdgeRewriteRule.node_split, resolved.program.edge_rewrites[2].rule);
    try std.testing.expect(resolved.program.certificates.len != 0);
    var combined_certificates: usize = 0;
    for (resolved.program.certificates) |certificate| {
        try std.testing.expect(proof_digest.isFrameworkDigest(certificate.certificate_digest.?));
        if (std.mem.startsWith(u8, certificate.certificate_digest.?, proof_digest.combined_runtime_prefix)) {
            combined_certificates += 1;
        }
    }
    try std.testing.expect(combined_certificates != 0);

    var report = try @import("validate.zig").validate(std.testing.allocator, &resolved.program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
    var graph = try @import("cfg.zig").Analysis.init(std.testing.allocator, &resolved.program, resolved.program.functions[0]);
    defer graph.deinit();
    var regions = try @import("irreducible_region.zig").analyze(std.testing.allocator, &graph);
    defer regions.deinit();
    try std.testing.expectEqual(@as(usize, 0), regions.regions.len);

    var reresolved = try resolveAlloc(std.testing.allocator, &resolved.program, solver_backend.internalFacts());
    defer reresolved.deinit();
    const codec = @import("codec.zig");
    const first_encoded = try codec.encodeAlloc(std.testing.allocator, &resolved.program);
    defer std.testing.allocator.free(first_encoded);
    const second_encoded = try codec.encodeAlloc(std.testing.allocator, &reresolved.program);
    defer std.testing.allocator.free(second_encoded);
    try std.testing.expectEqualStrings(first_encoded, second_encoded);

    var parsed = try codec.parse(std.testing.allocator, first_encoded);
    defer parsed.deinit();
    try std.testing.expect(std.mem.startsWith(
        u8,
        parsed.value.certificates[0].certificate_digest.?,
        proof_digest.combined_runtime_prefix,
    ));

    const stale_certificates = try std.testing.allocator.dupe(ir.SolverCertificate, parsed.value.certificates);
    defer std.testing.allocator.free(stale_certificates);
    stale_certificates[0].certificate_digest = proof_digest.lexical_binding_prefix ++ "0000000000000000000000000000000000000000000000000000000000000000";
    var stale_program = parsed.value;
    stale_program.certificates = stale_certificates;
    var stale_report = try @import("validate.zig").validate(std.testing.allocator, &stale_program, .core);
    defer stale_report.deinit();
    try std.testing.expect(stale_report.contains(.certificate_digest_mismatch));

    var transport_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer transport_arena.deinit();
    const transport_allocator = transport_arena.allocator();
    const imported_certificates = try transport_allocator.dupe(ir.SolverCertificate, parsed.value.certificates);
    imported_certificates[0].engine = .imported;
    var imported_program = parsed.value;
    imported_program.certificates = imported_certificates;
    var imported_model: []const ir.SolverModelBinding = &.{};
    if (imported_certificates[0].model) |model_id| {
        imported_model = imported_program.solver_models[model_id.index()].bindings;
    }
    var imported_core: []const ir.ConstraintId = &.{};
    if (imported_certificates[0].unsat_core) |core_id| {
        imported_core = imported_program.unsat_cores[core_id.index()].constraints;
    }
    const imported_digest = try proof_digest.computeAlloc(
        transport_allocator,
        &imported_program,
        imported_program.queries[imported_certificates[0].query.index()],
        .imported,
        imported_certificates[0].resolution,
        imported_certificates[0].evidence,
        imported_model,
        imported_core,
    );
    imported_certificates[0].certificate_digest = imported_digest;
    const imported_instructions = try transport_allocator.dupe(ir.Instruction, imported_program.instructions);
    imported_instructions[closure_id.index()].operation.make_closure.bindings = &.{.{ .value = entry_zero }};
    imported_program.instructions = imported_instructions;
    try refreshDependencyDigests(transport_allocator, &imported_program, imported_certificates);
    try std.testing.expect(!std.mem.eql(
        u8,
        imported_digest,
        imported_certificates[0].certificate_digest.?,
    ));
}

test "internal proof orchestration resolves required claims deterministically" {
    const fixtures = @import("fixtures.zig");
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
    const claims = [_]ir.Claim{
        .{
            .id = ir.ClaimId.fromIndex(0),
            .subject = .{ .program = {} },
            .predicate = ir.SolverTermId.fromIndex(0),
            .status = .unproven,
            .required_for_emission = true,
            .evidence = &.{fixture.proof},
            .query = ir.QueryId.fromIndex(0),
        },
        .{
            .id = ir.ClaimId.fromIndex(1),
            .subject = .{ .function = fixture.f_add },
            .predicate = ir.SolverTermId.fromIndex(0),
            .status = .unproven,
            .required_for_emission = true,
            .evidence = &.{fixture.proof},
            .query = ir.QueryId.fromIndex(0),
        },
    };
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .numeric_domain,
        .subject = .{ .program = {} },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "shared query must discharge this obligation",
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;
    program.obligations = &obligations;

    var resolved = try resolveAlloc(std.testing.allocator, &program, solver_backend.internalFacts());
    defer resolved.deinit();
    try std.testing.expectEqual(ir.ClaimStatus.proved, resolved.program.claims[0].status);
    try std.testing.expectEqual(ir.ClaimStatus.proved, resolved.program.claims[1].status);
    try std.testing.expectEqual(ir.ObligationStatus.discharged, resolved.program.obligations[0].status);
    try std.testing.expectEqual(resolved.program.claims[0].certificate, resolved.program.claims[1].certificate);
    try std.testing.expectEqual(resolved.program.claims[0].certificate, resolved.program.obligations[0].certificate);
    try std.testing.expectEqual(@as(usize, 1), resolved.program.certificates.len);
    try std.testing.expectEqual(@as(usize, 1), resolved.program.unsat_cores.len);
    try std.testing.expect(proof_digest.isFrameworkDigest(resolved.program.certificates[0].certificate_digest.?));

    var resolved_again = try resolveAlloc(std.testing.allocator, &program, solver_backend.internalFacts());
    defer resolved_again.deinit();
    try std.testing.expectEqualStrings(
        resolved.program.certificates[0].certificate_digest.?,
        resolved_again.program.certificates[0].certificate_digest.?,
    );

    var valid_report = try @import("validate.zig").validate(std.testing.allocator, &resolved.program, .readable_luau);
    defer valid_report.deinit();
    try std.testing.expect(valid_report.isClean());

    var tampered = resolved.program;
    tampered.program_id = "different-program-identity";
    var tampered_report = try @import("validate.zig").validate(std.testing.allocator, &tampered, .core);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.certificate_digest_mismatch));

    var changed_evidence = fixture.evidence;
    changed_evidence[fixture.proof.index()].locator = "fixture:changed-provenance";
    tampered = resolved.program;
    tampered.evidence = &changed_evidence;
    var provenance_report = try @import("validate.zig").validate(std.testing.allocator, &tampered, .core);
    defer provenance_report.deinit();
    try std.testing.expect(provenance_report.contains(.certificate_digest_mismatch));
}

test "external binding certificates survive persisted replay and reject remapping" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const capture_first = ir.CaptureId.fromIndex(0);
    const capture_second = ir.CaptureId.fromIndex(1);
    const captured_first = ir.ValueId.fromIndex(fixture.values.len);
    const captured_second = ir.ValueId.fromIndex(fixture.values.len + 1);
    const binding_first = ir.ExternalBindingId.fromIndex(0);
    const binding_second = ir.ExternalBindingId.fromIndex(1);
    const values = fixture.values ++ [_]ir.Value{
        .{ .id = captured_first, .function = fixture.f_entry, .type = .integer, .origin = .{ .capture = capture_first } },
        .{ .id = captured_second, .function = fixture.f_entry, .type = .integer, .origin = .{ .capture = capture_second } },
    };
    const captures = [_]ir.Capture{
        .{ .id = capture_first, .function = fixture.f_entry, .kind = .{ .immutable_value = captured_first }, .evidence = &.{fixture.proof} },
        .{ .id = capture_second, .function = fixture.f_entry, .kind = .{ .immutable_value = captured_second }, .evidence = &.{fixture.proof} },
    };
    const capture_ids = [_]ir.CaptureId{ capture_first, capture_second };
    var functions = fixture.functions;
    functions[fixture.f_entry.index()].captures = &capture_ids;
    const external_bindings = [_]ir.ExternalBinding{
        .{ .id = binding_first, .kind = .immutable_value, .type = .integer, .evidence = &.{fixture.proof} },
        .{ .id = binding_second, .kind = .immutable_value, .type = .integer, .evidence = &.{fixture.proof} },
    };
    const entry_bindings = [_]ir.ExternalBindingId{ binding_first, binding_second };
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
        .required_for_emission = true,
        .evidence = &.{fixture.proof},
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.entry_bindings = &entry_bindings;
    program.external_bindings = &external_bindings;
    program.functions = &functions;
    program.values = &values;
    program.captures = &captures;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;

    var resolved = try resolveAlloc(std.testing.allocator, &program, solver_backend.internalFacts());
    defer resolved.deinit();
    try std.testing.expectEqual(@as(usize, 1), resolved.program.certificates.len);
    try std.testing.expect(std.mem.startsWith(
        u8,
        resolved.program.certificates[0].certificate_digest.?,
        proof_digest.lexical_binding_prefix,
    ));

    const codec = @import("codec.zig");
    const encoded = try codec.encodeAlloc(std.testing.allocator, &resolved.program);
    defer std.testing.allocator.free(encoded);
    var parsed = try codec.parse(std.testing.allocator, encoded);
    defer parsed.deinit();

    var replay_report = try @import("validate.zig").validate(std.testing.allocator, &parsed.value, .core);
    defer replay_report.deinit();
    try std.testing.expect(replay_report.isClean());

    const stale_certificates = try std.testing.allocator.dupe(ir.SolverCertificate, parsed.value.certificates);
    defer std.testing.allocator.free(stale_certificates);
    stale_certificates[0].certificate_digest = proof_digest.external_binding_prefix ++ "0000000000000000000000000000000000000000000000000000000000000000";
    var stale_program = parsed.value;
    stale_program.certificates = stale_certificates;
    var stale_report = try @import("validate.zig").validate(std.testing.allocator, &stale_program, .core);
    defer stale_report.deinit();
    try std.testing.expect(stale_report.contains(.certificate_digest_mismatch));

    var replayed = try resolveAlloc(std.testing.allocator, &parsed.value, solver_backend.internalFacts());
    defer replayed.deinit();
    const replayed_encoded = try codec.encodeAlloc(std.testing.allocator, &replayed.program);
    defer std.testing.allocator.free(replayed_encoded);
    try std.testing.expectEqualStrings(encoded, replayed_encoded);

    const swapped_entry_bindings = [_]ir.ExternalBindingId{ binding_second, binding_first };
    var tampered = parsed.value;
    tampered.entry_bindings = &swapped_entry_bindings;
    var tampered_report = try @import("validate.zig").validate(std.testing.allocator, &tampered, .core);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.certificate_digest_mismatch));

    const imported_certificates = try std.testing.allocator.dupe(ir.SolverCertificate, parsed.value.certificates);
    defer std.testing.allocator.free(imported_certificates);
    defer for (imported_certificates[1..], 1..) |certificate, index| {
        const refreshed = certificate.certificate_digest orelse continue;
        const unchanged = if (parsed.value.certificates[index].certificate_digest) |original|
            refreshed.ptr == original.ptr
        else
            false;
        if (!unchanged) std.testing.allocator.free(@constCast(refreshed));
    };
    imported_certificates[0].engine = .imported;
    var model: []const ir.SolverModelBinding = &.{};
    if (imported_certificates[0].model) |model_id| model = parsed.value.solver_models[model_id.index()].bindings;
    var unsat_core: []const ir.ConstraintId = &.{};
    if (imported_certificates[0].unsat_core) |core_id| unsat_core = parsed.value.unsat_cores[core_id.index()].constraints;
    var imported_program = parsed.value;
    imported_program.certificates = imported_certificates;
    const imported_digest = try proof_digest.computeAlloc(
        std.testing.allocator,
        &imported_program,
        parsed.value.queries[imported_certificates[0].query.index()],
        .imported,
        imported_certificates[0].resolution,
        imported_certificates[0].evidence,
        model,
        unsat_core,
    );
    defer std.testing.allocator.free(imported_digest);
    imported_certificates[0].certificate_digest = imported_digest;
    imported_program.entry_bindings = &swapped_entry_bindings;
    try refreshDependencyDigests(std.testing.allocator, &imported_program, imported_certificates);
    const transported_digest = imported_certificates[0].certificate_digest.?;
    defer std.testing.allocator.free(transported_digest);
    try std.testing.expect(!std.mem.eql(u8, imported_digest, transported_digest));

    imported_certificates[0].certificate_digest = "fixture:opaque-imported-proof";
    try refreshDependencyDigests(std.testing.allocator, &imported_program, imported_certificates);
    try std.testing.expectEqualStrings("fixture:opaque-imported-proof", imported_certificates[0].certificate_digest.?);
}

test "lexical capture certificates survive replay and reject source remapping" {
    const fixture = @import("fixtures.zig").immutable_closure_module;
    const alternate = ir.ValueId.fromIndex(fixture.values.len);
    const values = fixture.values ++ [_]ir.Value{.{
        .id = alternate,
        .function = fixture.f_factory,
        .type = .integer,
        .origin = .{ .parameter = 1 },
    }};
    var functions = fixture.functions;
    functions[fixture.f_factory.index()].parameters = &.{ fixture.v_base, alternate };
    var instructions = fixture.instructions;
    instructions[fixture.i_add.index()].claims = &.{ir.ClaimId.fromIndex(2)};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = fixture.v_captured_base } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .semantic_atom = .{
            .primitive_operator_domain = fixture.i_add,
        } } },
    };
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(3),
        .evidence = &.{fixture.proof},
    }};
    const queries = [_]ir.SolverQuery{
        .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(1) },
        .{ .id = ir.QueryId.fromIndex(1), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) },
        .{
            .id = ir.QueryId.fromIndex(2),
            .kind = .prove_true,
            .assumptions = &.{ir.ConstraintId.fromIndex(0)},
            .goal = ir.SolverTermId.fromIndex(3),
        },
    };
    const claims = [_]ir.Claim{
        .{
            .id = ir.ClaimId.fromIndex(0),
            .subject = .{ .function = fixture.f_adder },
            .predicate = ir.SolverTermId.fromIndex(1),
            .status = .unproven,
            .required_for_emission = true,
            .evidence = &.{fixture.proof},
            .query = ir.QueryId.fromIndex(0),
        },
        .{
            .id = ir.ClaimId.fromIndex(1),
            .subject = .{ .program = {} },
            .predicate = ir.SolverTermId.fromIndex(2),
            .status = .unproven,
            .required_for_emission = true,
            .evidence = &.{fixture.proof},
            .query = ir.QueryId.fromIndex(1),
        },
        .{
            .id = ir.ClaimId.fromIndex(2),
            .subject = .{ .instruction = fixture.i_add },
            .predicate = ir.SolverTermId.fromIndex(3),
            .purpose = .{ .primitive_operator_domain = .pure },
            .status = .unproven,
            .required_for_emission = true,
            .evidence = &.{fixture.proof},
            .query = ir.QueryId.fromIndex(2),
        },
    };
    var program = fixture.program;
    program.functions = &functions;
    program.instructions = &instructions;
    program.values = &values;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    program.queries = &queries;
    program.claims = &claims;

    var resolved = try resolveAlloc(std.testing.allocator, &program, solver_backend.internalFacts());
    defer resolved.deinit();
    try std.testing.expectEqual(@as(usize, 3), resolved.program.certificates.len);
    try std.testing.expectEqual(@as(usize, 1), resolved.solve_report.diagnostics.items.len);
    const replay_diagnostic = resolved.solve_report.diagnostics.items[0];
    try std.testing.expectEqual(diagnostics.Code.solver_unknown, replay_diagnostic.code);
    try std.testing.expectEqual(@as(?u32, 2), replay_diagnostic.entity_index);
    try std.testing.expectEqual(
        diagnostics.SolverUnknownPhase.unsat_core_replay,
        replay_diagnostic.detail.solver_unknown.phase,
    );
    try std.testing.expectEqual(
        solver_backend.UnknownReason.bounded_internal_incompleteness,
        replay_diagnostic.detail.solver_unknown.reason,
    );
    try std.testing.expect(std.mem.startsWith(
        u8,
        resolved.program.certificates[0].certificate_digest.?,
        proof_digest.lexical_binding_prefix,
    ));
    try std.testing.expect(std.mem.startsWith(
        u8,
        resolved.program.certificates[1].certificate_digest.?,
        proof_digest.prefix,
    ));
    try std.testing.expect(std.mem.startsWith(
        u8,
        resolved.program.certificates[2].certificate_digest.?,
        proof_digest.lexical_binding_prefix,
    ));

    const codec = @import("codec.zig");
    const encoded = try codec.encodeAlloc(std.testing.allocator, &resolved.program);
    defer std.testing.allocator.free(encoded);
    var parsed = try codec.parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    var replay_report = try @import("validate.zig").validate(std.testing.allocator, &parsed.value, .core);
    defer replay_report.deinit();
    try std.testing.expect(replay_report.isClean());

    const stale_certificates = try std.testing.allocator.dupe(ir.SolverCertificate, parsed.value.certificates);
    defer std.testing.allocator.free(stale_certificates);
    stale_certificates[1].certificate_digest = proof_digest.lexical_binding_prefix ++ "0000000000000000000000000000000000000000000000000000000000000000";
    var stale = parsed.value;
    stale.certificates = stale_certificates;
    var stale_report = try @import("validate.zig").validate(std.testing.allocator, &stale, .core);
    defer stale_report.deinit();
    try std.testing.expect(stale_report.contains(.certificate_digest_mismatch));

    const tampered_values = try std.testing.allocator.dupe(ir.Value, parsed.value.values);
    defer std.testing.allocator.free(tampered_values);
    tampered_values[fixture.v_captured_base.index()].type = .dynamic;
    var stale_semantic = parsed.value;
    stale_semantic.values = tampered_values;
    var stale_semantic_report = try @import("validate.zig").validate(std.testing.allocator, &stale_semantic, .core);
    defer stale_semantic_report.deinit();
    var rejected_semantic_certificate = false;
    for (stale_semantic_report.diagnostics.items) |diagnostic| {
        if (diagnostic.code == .certificate_digest_mismatch and diagnostic.entity_index == 2) {
            rejected_semantic_certificate = true;
        }
    }
    try std.testing.expect(rejected_semantic_certificate);

    var replayed = try resolveAlloc(std.testing.allocator, &parsed.value, solver_backend.internalFacts());
    defer replayed.deinit();
    const replayed_encoded = try codec.encodeAlloc(std.testing.allocator, &replayed.program);
    defer std.testing.allocator.free(replayed_encoded);
    try std.testing.expectEqualStrings(encoded, replayed_encoded);

    const tampered_instructions = try std.testing.allocator.dupe(ir.Instruction, parsed.value.instructions);
    defer std.testing.allocator.free(tampered_instructions);
    tampered_instructions[fixture.i_make_adder.index()].operation.make_closure.bindings = &.{.{ .value = alternate }};
    var tampered = parsed.value;
    tampered.instructions = tampered_instructions;
    var tampered_report = try @import("validate.zig").validate(std.testing.allocator, &tampered, .core);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.certificate_digest_mismatch));
}
