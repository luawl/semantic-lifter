const std = @import("std");
const Io = std.Io;
const ir = @import("ir.zig");
const solver = @import("solver.zig");
const solver_equivalence = @import("solver_equivalence.zig");
const solver_preconditions = @import("solver_preconditions.zig");
const solver_term = @import("solver_term.zig");
const solver_promotion = @import("solver_promotion.zig");
const query_promotion = @import("query_promotion.zig");
const cfg = @import("cfg.zig");
const cfg_edge = @import("cfg_edge.zig");
const edge_path = @import("edge_path.zig");
const edge_facts = @import("edge_facts.zig");
const readable_scope = @import("readable_scope.zig");
const readable_error_location = @import("readable_error_location.zig");
const proof_digest = @import("proof_digest.zig");
const control_flow = @import("control_flow.zig");
const iteration_protocol = @import("iteration_protocol.zig");
const structure = @import("structure.zig");
const stage_trace = @import("stage_trace.zig");

const SliceToken = struct {
    address: usize,
    length: usize,

    fn from(comptime T: type, slice: []const T) SliceToken {
        return .{ .address = @intFromPtr(slice.ptr), .length = slice.len };
    }

    fn eql(self: SliceToken, other: SliceToken) bool {
        return self.address == other.address and self.length == other.length;
    }
};

const EdgeFactsSource = struct {
    functions: SliceToken,
    blocks: SliceToken,
    instructions: SliceToken,
    values: SliceToken,
    value_packs: SliceToken,
    places: SliceToken,
    captures: SliceToken,
    evidence: SliceToken,
    solver_terms: SliceToken,
    constraints: SliceToken,
    queries: SliceToken,
    edge_rewrites: SliceToken,

    fn from(program: *const ir.Program) EdgeFactsSource {
        return .{
            .functions = SliceToken.from(ir.Function, program.functions),
            .blocks = SliceToken.from(ir.Block, program.blocks),
            .instructions = SliceToken.from(ir.Instruction, program.instructions),
            .values = SliceToken.from(ir.Value, program.values),
            .value_packs = SliceToken.from(ir.ValuePack, program.value_packs),
            .places = SliceToken.from(ir.Place, program.places),
            .captures = SliceToken.from(ir.Capture, program.captures),
            .evidence = SliceToken.from(ir.Evidence, program.evidence),
            .solver_terms = SliceToken.from(ir.SolverTerm, program.solver_terms),
            .constraints = SliceToken.from(ir.Constraint, program.constraints),
            .queries = SliceToken.from(ir.SolverQuery, program.queries),
            .edge_rewrites = SliceToken.from(ir.CfgEdgeRewrite, program.edge_rewrites),
        };
    }

    fn matches(self: EdgeFactsSource, program: *const ir.Program) bool {
        return self.eql(EdgeFactsSource.from(program));
    }

    fn eql(self: EdgeFactsSource, other: EdgeFactsSource) bool {
        return self.functions.eql(other.functions) and
            self.blocks.eql(other.blocks) and
            self.instructions.eql(other.instructions) and
            self.values.eql(other.values) and
            self.value_packs.eql(other.value_packs) and
            self.places.eql(other.places) and
            self.captures.eql(other.captures) and
            self.evidence.eql(other.evidence) and
            self.solver_terms.eql(other.solver_terms) and
            self.constraints.eql(other.constraints) and
            self.queries.eql(other.queries) and
            self.edge_rewrites.eql(other.edge_rewrites);
    }
};

pub fn expandInArena(allocator: std.mem.Allocator, program: *const ir.Program) !ir.Program {
    var state = try State.init(allocator, program);
    state.releaseDeferredBranchArms();
    return state.expand(program);
}

pub const State = struct {
    allocator: std.mem.Allocator,
    terms: std.ArrayList(ir.SolverTerm) = .empty,
    constraints: std.ArrayList(ir.Constraint) = .empty,
    evidence: std.ArrayList(ir.Evidence) = .empty,
    queries: std.ArrayList(ir.SolverQuery) = .empty,
    obligations: std.ArrayList(ir.Obligation) = .empty,
    claims: std.ArrayList(ir.Claim) = .empty,
    defer_base_branch_arms: bool = true,
    edge_facts_source: ?EdgeFactsSource = null,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program) !State {
        var state = try initBase(allocator, program);
        var scope = try readable_scope.Scope.init(allocator, program);
        defer scope.deinit();
        const edge_fact_start = Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds;
        try state.deriveEdgeFacts(program, &scope);
        state.edge_facts_source = EdgeFactsSource.from(program);
        if (stage_trace.enabled) std.debug.print(
            "control_phase edge_facts_done terms={} constraints={} queries={} claims={} ms={}\\n",
            .{
                state.terms.items.len,
                state.constraints.items.len,
                state.queries.items.len,
                state.claims.items.len,
                @divTrunc(Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds - edge_fact_start, std.time.ns_per_ms),
            },
        );
        var promotion_program = state.programView(program);
        const promotion_start = Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds;
        _ = try query_promotion.promoteUnresolvedQueries(
            allocator,
            &promotion_program,
            &state.terms,
            &state.queries,
            &state.claims,
            &state.obligations,
        );
        if (stage_trace.enabled) std.debug.print(
            "control_phase query_promotion_done terms={} queries={} obligations={} claims={} ms={}\\n",
            .{
                state.terms.items.len,
                state.queries.items.len,
                state.obligations.items.len,
                state.claims.items.len,
                @divTrunc(Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds - promotion_start, std.time.ns_per_ms),
            },
        );
        return state;
    }

    /// Copy only durable proof inputs for the pre-structuring exact-fact pass.
    /// Edge-fact derivation is intentionally deferred until after exact
    /// branches have been authenticated and rewritten.
    pub fn initExact(allocator: std.mem.Allocator, program: *const ir.Program) !State {
        return initBase(allocator, program);
    }

    fn initBase(allocator: std.mem.Allocator, program: *const ir.Program) !State {
        var state: State = .{ .allocator = allocator };
        try state.terms.appendSlice(allocator, program.solver_terms);
        try state.constraints.appendSlice(allocator, program.constraints);
        try state.evidence.appendSlice(allocator, program.evidence);
        try state.queries.appendSlice(allocator, program.queries);
        try state.obligations.appendSlice(allocator, program.obligations);
        try state.claims.appendSlice(allocator, program.claims);
        return state;
    }

    pub fn programView(self: *const State, base: *const ir.Program) ir.Program {
        var view = base.*;
        view.solver_terms = self.terms.items;
        view.constraints = self.constraints.items;
        view.evidence = self.evidence.items;
        view.queries = self.queries.items;
        view.obligations = self.obligations.items;
        view.claims = self.claims.items;
        return view;
    }

    pub fn releaseDeferredBranchArms(self: *State) void {
        self.defer_base_branch_arms = false;
    }

    pub fn hasExactIterationForwardingBranch(program: *const ir.Program) bool {
        for (program.blocks) |block| {
            const branch = switch (block.terminator) {
                .branch => |value| value,
                else => continue,
            };
            const truth = exactBranchTruth(program, branch.condition, null);
            if (truth == .unknown) continue;
            const dead_edge = if (truth == .true_value) branch.else_edge else branch.then_edge;
            if (emptyParameterizedIterationForwarding(program, dead_edge)) return true;
        }
        return false;
    }

    pub fn hasExactBranchTruth(program: *const ir.Program) bool {
        for (program.blocks) |block| {
            const branch = switch (block.terminator) {
                .branch => |value| value,
                else => continue,
            };
            if (exactBranchTruth(program, branch.condition, null) != .unknown) return true;
        }
        return false;
    }

    fn emptyParameterizedIterationForwarding(program: *const ir.Program, initial: ir.Edge) bool {
        var edge = initial;
        var visited: usize = 0;
        while (visited < program.blocks.len) : (visited += 1) {
            if (edge.target.index() >= program.blocks.len) return false;
            const block = program.blocks[edge.target.index()];
            if (block.parameters.len == 0 or block.parameters.len != edge.arguments.len) return false;
            if (block.instructions.len != 0) {
                return iteration_protocol.transitionForHeader(program, block) != null;
            }
            edge = switch (block.terminator) {
                .jump => |next| next,
                else => return false,
            };
        }
        return false;
    }

    // Exact constants are solver-independent semantic facts, but they still
    // need the ordinary query, obligation, and certificate path before CFG
    // normalization can rely on the selected arm. Only loop-boundary facts
    // are promoted in this pre-pass. Other exact branches remain available to
    // the ordinary planner after the first structural normalization, avoiding
    // a root-wide proof queue for facts that cannot affect loop ownership.
    pub fn expandExactBranches(self: *State, program: *const ir.Program) !ir.Program {
        const boundary_candidates = try exactControlBoundaryMaskAlloc(self.allocator, program);
        defer self.allocator.free(boundary_candidates);
        return self.expandExactBranchesWithMask(program, boundary_candidates, "pre-normalization exact branch truthiness fact");
    }

    /// Expand only exact branches whose existing admitted structure identifies
    /// a boundary that can confuse direct readable emission. This path is for
    /// already-readable programs, so it deliberately avoids the broad natural
    /// loop mask used by the general resolver.
    pub fn expandAdmittedExactBranches(self: *State, program: *const ir.Program) !ir.Program {
        return self.expandAdmittedExactBranchesWithScratch(program, self.allocator);
    }

    /// The boundary scan constructs a temporary CFG and structure plan for
    /// every function. Resolver state normally lives in an arena, but those
    /// per-function plans need a reclaiming allocator or a large program
    /// retains every destroyed plan until the resolver returns.
    pub fn expandAdmittedExactBranchesWithScratch(
        self: *State,
        program: *const ir.Program,
        scratch_allocator: std.mem.Allocator,
    ) !ir.Program {
        const boundary_candidates = try admittedExactControlBoundaryMaskAlloc(scratch_allocator, program);
        defer scratch_allocator.free(boundary_candidates);
        return self.expandExactBranchesWithMask(program, boundary_candidates, "direct admitted exact branch truthiness fact");
    }

    fn expandExactBranchesWithMask(
        self: *State,
        program: *const ir.Program,
        boundary_candidates: []const bool,
        detail: []const u8,
    ) !ir.Program {
        var scope = try readable_scope.Scope.init(self.allocator, program);
        defer scope.deinit();
        var planned = self.programView(program);
        for (program.blocks) |block| {
            if (!scope.block(block.id) or
                block.id.index() >= boundary_candidates.len or
                !boundary_candidates[block.id.index()]) continue;
            const branch = switch (block.terminator) {
                .branch => |value| value,
                else => continue,
            };
            // This pre-pass exists only to protect exact frontend facts from
            // structural normalization. Do not promote unresolved branches
            // here; the ordinary planner handles those after normalization.
            const truth: ?bool = switch (exactBranchTruth(&planned, branch.condition, null)) {
                .true_value => true,
                .false_value => false,
                .unknown => null,
            };
            if (truth == null) continue;
            const witness = historicalBranch(&planned, block.id, branch) orelse continue;
            const term_id = (try self.ensureBranchTerm(&planned, branch.condition, null)) orelse continue;
            planned = self.programView(&planned);
            const query_kind: ir.QueryKind = if (truth.?) .prove_true else .prove_false;
            const query_id = try ensureQuery(self.allocator, &self.queries, term_id, query_kind, &.{}, &.{});
            if (hasControlBranchObligation(self.obligations.items, block.id, witness, query_id)) continue;
            const evidence = try branchTruthinessEvidenceAlloc(self.allocator, &planned, block, branch.condition);
            const certificate_id = findProvedCertificate(planned.certificates, query_id, evidence);
            try self.obligations.append(self.allocator, .{
                .id = ir.ObligationId.fromIndex(self.obligations.items.len),
                .kind = .control_structure,
                .subject = .{ .control_branch = .{ .block = block.id, .branch = witness } },
                .status = if (certificate_id == null) .open else .discharged,
                .blocks_profile = .readable_luau,
                .detail = detail,
                .evidence = evidence,
                .requirement = ir.ObligationRequirement.fromQuery(self.queries.items[query_id.index()]),
                .query = query_id,
                .certificate = certificate_id,
            });
            planned = self.programView(&planned);
        }
        return self.programView(&planned);
    }

    pub fn materializeProvedControlBranches(self: *State, program: *const ir.Program) !bool {
        var changed = false;
        for (program.claims) |claim| {
            if (claim.status != .proved or claim.query == null or claim.certificate == null) continue;
            const block_id = switch (claim.subject) {
                .block => |id| id,
                else => continue,
            };
            if (block_id.index() >= program.blocks.len or
                claim.query.?.index() >= program.queries.len or
                claim.certificate.?.index() >= program.certificates.len)
            {
                continue;
            }
            const block = program.blocks[block_id.index()];
            const branch = switch (block.terminator) {
                .branch => |value| value,
                else => continue,
            };
            const witness = historicalBranch(program, block.id, branch) orelse continue;
            const query = program.queries[claim.query.?.index()];
            const certificate = program.certificates[claim.certificate.?.index()];
            const fact = control_flow.queryValueFact(program, query) orelse continue;
            switch (edge_path.queryRoot(program, query)) {
                .none => {},
                .one, .ambiguous => continue,
            }
            if (query.id != claim.query.? or certificate.id != claim.certificate.? or
                certificate.query != query.id or certificate.resolution != .proved or
                fact.value != branch.condition or hasControlBranchObligation(self.obligations.items, block.id, witness, query.id))
            {
                continue;
            }
            const evidence = try branchTruthinessEvidenceAlloc(self.allocator, program, block, branch.condition);
            if (evidence.len == 0 or !evidenceCovers(certificate.evidence, evidence)) continue;
            try self.obligations.append(self.allocator, .{
                .id = ir.ObligationId.fromIndex(self.obligations.items.len),
                .kind = .control_structure,
                .subject = .{ .control_branch = .{ .block = block.id, .branch = witness } },
                .status = .discharged,
                .blocks_profile = .readable_luau,
                .detail = "authenticated proved branch selection",
                .evidence = evidence,
                .requirement = ir.ObligationRequirement.fromQuery(query),
                .query = query.id,
                .certificate = certificate.id,
            });
            changed = true;
        }
        return changed;
    }

    pub fn hasDeferredBranchArms(self: *const State, program: *const ir.Program) !bool {
        if (!self.defer_base_branch_arms) return false;
        var scope = try readable_scope.Scope.init(self.allocator, program);
        defer scope.deinit();
        for (program.blocks) |block| {
            if (!scope.block(block.id)) continue;
            const branch = switch (block.terminator) {
                .branch => |value| value,
                else => continue,
            };
            if (exactBranchTruth(program, branch.condition, findValueDefinition(program.solver_terms, branch.condition)) == .unknown and
                hasRelevantBaseConstraint(program, block, branch.condition, findValueDefinition(program.solver_terms, branch.condition))) return true;
        }
        return false;
    }

    /// T5-DEFERRED-ARM-FACTS: whether `edge` is an arm edge of a block whose arm truth facts are deferred (the
    /// predicate of `hasDeferredBranchArms`). No claim is planned over such an edge before the release, even
    /// from facts already on it: a proof that rewrote the arm now would not assume the arm facts released
    /// later, which would then fall outside its edge scope.
    fn armEdgeOfDeferredBlock(self: *const State, program: *const ir.Program, edge: ir.CfgEdgeRef) bool {
        if (!self.defer_base_branch_arms or edge.kind == .jump or edge.source.index() >= program.blocks.len) return false;
        const source = program.blocks[edge.source.index()];
        const branch = switch (source.terminator) {
            .branch => |value| value,
            else => return false,
        };
        const promoted = findValueDefinition(program.solver_terms, branch.condition);
        return exactBranchTruth(program, branch.condition, promoted) == .unknown and
            hasRelevantBaseConstraint(program, source, branch.condition, promoted);
    }

    fn deriveEdgeFacts(self: *State, program: *const ir.Program, scope: *const readable_scope.Scope) !void {
        var working = program.*;
        var history_cache = try edge_path.HistoryCache.init(self.allocator, program);
        defer history_cache.deinit();
        var structural_cache = try edge_facts.StructuralCache.init(self.allocator, program);
        defer structural_cache.deinit();
        const start = Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds;
        var processed: usize = 0;
        for (program.blocks) |block| {
            if (!scope.block(block.id)) continue;
            working.solver_terms = self.terms.items;
            working.constraints = self.constraints.items;
            working.evidence = self.evidence.items;
            const derive_branch_arms = switch (block.terminator) {
                .branch => |branch| blk: {
                    const promoted = try solver_promotion.ensureDefinition(self.allocator, &working, &self.terms, branch.condition);
                    working.solver_terms = self.terms.items;
                    const has_exact_truth = exactBranchTruth(&working, branch.condition, promoted) != .unknown;
                    // A block whose arm truth facts wait for its base claims derives no fact on its arm
                    // edges until they are released: the arm facts decide the arm edges' argument facts
                    // (replay, validate_proofs.zig:60) and must be carried by every proof that rewrites an
                    // arm (edge scope, :73), so the block's facts are all derived in one call.
                    if (!has_exact_truth and self.defer_base_branch_arms and
                        hasRelevantBaseConstraint(&working, block, branch.condition, promoted)) continue;
                    break :blk !has_exact_truth;
                },
                else => true,
            };
            try edge_facts.deriveBlockWithHistory(
                self.allocator,
                &working,
                scope,
                &self.terms,
                &self.constraints,
                &self.evidence,
                &history_cache,
                &structural_cache,
                block,
                derive_branch_arms,
            );
            processed += 1;
            if (processed % 250 == 0) {
                if (stage_trace.enabled) std.debug.print(
                    "control_phase edge_facts_progress blocks={} terms={} constraints={} ms={}\n",
                    .{
                        processed,
                        self.terms.items.len,
                        self.constraints.items.len,
                        @divTrunc(Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds - start, std.time.ns_per_ms),
                    },
                );
            }
        }
        if (stage_trace.enabled) std.debug.print(
            "control_phase edge_facts_complete blocks={} terms={} constraints={} ms={}\n",
            .{
                processed,
                self.terms.items.len,
                self.constraints.items.len,
                @divTrunc(Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds - start, std.time.ns_per_ms),
            },
        );
        self.edge_facts_source = EdgeFactsSource.from(program);
    }

    pub fn expand(self: *State, program: *const ir.Program) !ir.Program {
        var scope = try readable_scope.Scope.init(self.allocator, program);
        defer scope.deinit();
        try readable_error_location.deriveRequirements(
            self.allocator,
            program,
            &scope,
            &self.terms,
            &self.queries,
            &self.obligations,
        );
        if (self.edge_facts_source == null or !self.edge_facts_source.?.matches(program)) {
            var fact_program = self.programView(program);
            try self.deriveEdgeFacts(&fact_program, &scope);
        } else {
            if (stage_trace.enabled) std.debug.print("control_phase edge_facts_reused\n", .{});
        }
        var planned = self.programView(program);
        const working = &planned;
        var has_candidate = false;
        for (working.blocks) |block| {
            if (!scope.block(block.id)) continue;
            const branch = switch (block.terminator) {
                .branch => |value| value,
                else => continue,
            };
            const promoted = try solver_promotion.ensureDefinition(self.allocator, working, &self.terms, branch.condition);
            planned = self.programView(&planned);
            if (exactBranchTruth(working, branch.condition, promoted) != .unknown or
                hasAnyRelevantConstraint(working, block, branch.condition, promoted))
            {
                has_candidate = true;
                break;
            }
        }
        if (!has_candidate) return planned;

        for (working.blocks) |block| {
            if (!scope.block(block.id)) continue;
            const branch = switch (block.terminator) {
                .branch => |value| value,
                else => continue,
            };
            const witness = historicalBranch(working, block.id, branch) orelse continue;
            const promoted = try solver_promotion.ensureDefinition(self.allocator, working, &self.terms, branch.condition);
            planned = self.programView(&planned);
            const exact_truth: ?bool = switch (exactBranchTruth(working, branch.condition, promoted)) {
                .true_value => true,
                .false_value => false,
                .unknown => null,
            };
            if (exact_truth == null and !hasAnyRelevantConstraint(working, block, branch.condition, promoted)) continue;
            const term_id = (try self.ensureBranchTerm(working, branch.condition, promoted)) orelse continue;
            planned = self.programView(&planned);
            if (exact_truth) |truth| {
                const query_kind: ir.QueryKind = if (truth) .prove_true else .prove_false;
                const query_id = try ensureQuery(self.allocator, &self.queries, term_id, query_kind, &.{}, &.{});
                if (hasControlBranchObligation(self.obligations.items, block.id, witness, query_id)) continue;
                const evidence = try branchTruthinessEvidenceAlloc(self.allocator, working, block, branch.condition);
                const certificate_id = findProvedCertificate(working.certificates, query_id, evidence);
                try self.obligations.append(self.allocator, .{
                    .id = ir.ObligationId.fromIndex(self.obligations.items.len),
                    .kind = .control_structure,
                    .subject = .{ .control_branch = .{ .block = block.id, .branch = witness } },
                    .status = if (certificate_id == null) .open else .discharged,
                    .blocks_profile = .readable_luau,
                    .detail = "backend exact branch truthiness fact",
                    .evidence = evidence,
                    .requirement = ir.ObligationRequirement.fromQuery(self.queries.items[query_id.index()]),
                    .query = query_id,
                    .certificate = certificate_id,
                });
                planned = self.programView(&planned);
            } else {
                const negated_term = findNegatedTerm(self.terms.items, term_id) orelse blk: {
                    const id = ir.SolverTermId.fromIndex(self.terms.items.len);
                    try self.terms.append(self.allocator, .{
                        .id = id,
                        .sort = .{ .kind = .boolean },
                        .operation = .{ .logical_not = term_id },
                    });
                    planned = self.programView(&planned);
                    break :blk id;
                };
                const goals = [_]ir.SolverTermId{ term_id, negated_term };
                if (hasRelevantBaseConstraint(working, block, branch.condition, promoted)) {
                    const assumptions = try applicableConstraintsAlloc(self.allocator, working, block, .{ .base = {} });
                    try appendPairedClaims(self.allocator, working, block.id, goals, assumptions, &.{}, &self.queries, &self.claims);
                    planned = self.programView(&planned);
                }
                const incoming = try incomingEdgesAlloc(self.allocator, working, &scope, block.id);
                for (incoming) |edge| {
                    if (self.armEdgeOfDeferredBlock(working, edge)) continue;
                    const path = try relevantEdgePathAlloc(self.allocator, working, edge, branch.condition, promoted) orelse continue;
                    const assumptions = try applicableConstraintsAlloc(self.allocator, working, block, .{ .edge = .{ .edge = edge, .path = path } });
                    try appendPairedClaims(self.allocator, working, block.id, goals, assumptions, path.rewrites, &self.queries, &self.claims);
                    planned = self.programView(&planned);
                }
            }
        }

        return self.programView(&planned);
    }

    fn ensureBranchTerm(
        self: *State,
        program: *const ir.Program,
        condition: ir.ValueId,
        promoted: ?ir.SolverTermId,
    ) !?ir.SolverTermId {
        if (condition.index() >= program.values.len) return null;
        return switch (program.values[condition.index()].type.kind) {
            .boolean => promoted orelse findValueTerm(self.terms.items, condition) orelse blk: {
                const id = ir.SolverTermId.fromIndex(self.terms.items.len);
                try self.terms.append(self.allocator, .{
                    .id = id,
                    .sort = .{ .kind = .boolean },
                    .operation = .{ .value = condition },
                });
                break :blk id;
            },
            .dynamic => blk: {
                const value_term = findDynamicValueTerm(self.terms.items, condition) orelse value: {
                    const id = ir.SolverTermId.fromIndex(self.terms.items.len);
                    try self.terms.append(self.allocator, .{
                        .id = id,
                        .sort = .{ .kind = .dynamic_value },
                        .operation = .{ .value = condition },
                    });
                    break :value id;
                };
                break :blk findDynamicTruthinessTerm(self.terms.items, value_term) orelse truthiness: {
                    const id = ir.SolverTermId.fromIndex(self.terms.items.len);
                    try self.terms.append(self.allocator, .{
                        .id = id,
                        .sort = .{ .kind = .boolean },
                        .operation = .{ .dynamic_truthiness = value_term },
                    });
                    break :truthiness id;
                };
            },
            else => if (program.values[condition.index()].type.knownLuauTruthiness()) |truth|
                findBooleanLiteral(self.terms.items, truth) orelse literal: {
                    const id = ir.SolverTermId.fromIndex(self.terms.items.len);
                    try self.terms.append(self.allocator, .{
                        .id = id,
                        .sort = .{ .kind = .boolean },
                        .operation = .{ .boolean_literal = truth },
                    });
                    break :literal id;
                }
            else
                null,
        };
    }
};

fn exactBranchTruth(program: *const ir.Program, condition: ir.ValueId, promoted: ?ir.SolverTermId) solver.Truth {
    if (condition.index() >= program.values.len) return .unknown;
    return switch (program.values[condition.index()].type.kind) {
        .boolean => switch (solver.evaluateValue(program, condition)) {
            .boolean => |truth| if (truth) .true_value else .false_value,
            else => promotedTruth(program, promoted),
        },
        .dynamic => blk: {
            const descriptor = solver_equivalence.dynamicValueDescriptor(program, condition) orelse break :blk .unknown;
            const truth = solver_equivalence.dynamicDescriptorTruthiness(descriptor) orelse break :blk .unknown;
            break :blk if (truth) .true_value else .false_value;
        },
        else => if (program.values[condition.index()].type.knownLuauTruthiness()) |truth|
            if (truth) .true_value else .false_value
        else
            .unknown,
    };
}

fn exactControlBoundaryMaskAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
) ![]bool {
    const trace_start = Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds;
    const boundary_candidates = try allocator.alloc(bool, program.blocks.len);
    errdefer allocator.free(boundary_candidates);
    @memset(boundary_candidates, false);

    var total_boundary_candidates: usize = 0;

    // Exact branch truth is already a semantic fact when its value has an
    // exact-pure normalized source. It must not depend on a natural-loop
    // classifier recognizing the surrounding shape: a dead arm can itself be
    // the reason loop discovery becomes expensive or ambiguous. Authenticate
    // every reachable exact branch before structural normalization and retain
    // the ordinary query/certificate/rewrite path in expandExactBranches.
    // This is deliberately reachability-bounded; dead regions remain subject
    // to validation but cannot create control claims for source emission.
    for (program.functions) |function| {
        var analysis = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
            error.InvalidCfg => continue,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer analysis.deinit();

        var function_exact_branches: usize = 0;
        var function_candidates: usize = 0;
        for (function.blocks) |block_id| {
            if (!analysis.isReachable(block_id) or block_id.index() >= program.blocks.len) continue;
            const block = program.blocks[block_id.index()];
            const branch = switch (block.terminator) {
                .branch => |value| value,
                else => continue,
            };
            const truth = exactBranchTruth(program, branch.condition, null);
            if (truth == .unknown) continue;
            function_exact_branches += 1;
            if (boundary_candidates[block.id.index()]) continue;
            boundary_candidates[block.id.index()] = true;
            function_candidates += 1;
            total_boundary_candidates += 1;
            if (stage_trace.enabled) std.debug.print(
                "exact_branch_boundary_candidate function={} block={} then={} else={} truth={s}\n",
                .{ function.id.index(), block.id.index(), branch.then_edge.target.index(), branch.else_edge.target.index(), @tagName(truth) },
            );
        }
        if (stage_trace.enabled) std.debug.print(
            "exact_branch_boundary_scan function={} blocks={} exact_branches={} candidates={} ms={}\n",
            .{
                function.id.index(),
                function.blocks.len,
                function_exact_branches,
                function_candidates,
                @divTrunc(Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds - trace_start, std.time.ns_per_ms),
            },
        );
    }

    if (stage_trace.enabled) std.debug.print(
        "exact_branch_boundary_mask blocks={} candidates={} ms={}\n",
        .{
            program.blocks.len,
            total_boundary_candidates,
            @divTrunc(Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds - trace_start, std.time.ns_per_ms),
        },
    );

    return boundary_candidates;
}

fn admittedExactControlBoundaryMaskAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
) ![]bool {
    const trace_start = Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds;
    const boundary_candidates = try allocator.alloc(bool, program.blocks.len);
    errdefer allocator.free(boundary_candidates);
    @memset(boundary_candidates, false);

    var total_boundary_candidates: usize = 0;

    // A history-free frontend may still need the transparent forwarding
    // boundary before natural-loop discovery sees it. Once authenticated
    // rewrite history exists, those forwarding arms have already been
    // materialized; re-expanding them can invalidate the history and is not
    // required for readable admission.
    if (program.edge_rewrites.len == 0) {
        for (program.blocks) |block| {
            const branch = switch (block.terminator) {
                .branch => |value| value,
                else => continue,
            };
            const truth = exactBranchTruth(program, branch.condition, null);
            if (truth == .unknown) continue;
            const dead_edge = if (truth == .true_value) branch.else_edge else branch.then_edge;
            if (!State.emptyParameterizedIterationForwarding(program, dead_edge)) continue;
            if (!boundary_candidates[block.id.index()]) {
                boundary_candidates[block.id.index()] = true;
                total_boundary_candidates += 1;
            }
        }
    }

    // The direct readable path may specialize an exact branch only when the
    // already-admitted structure exposes the precise loop-boundary shape that
    // the emitter cannot otherwise own: an exitless infinite loop whose sole
    // body node is a normal exit boundary for the same header. The structural
    // witness is family-neutral and is intentionally narrower than natural
    // loop membership used by the general resolver.
    for (program.functions) |function| {
        var analysis = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
            error.InvalidCfg => continue,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer analysis.deinit();

        var plan = structure.Plan.init(allocator, &analysis) catch |err| switch (err) {
            error.UnsupportedShape => continue,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer plan.deinit();

        const before = total_boundary_candidates;
        markAdmittedExactBoundaryRegion(program, plan.root, boundary_candidates, &total_boundary_candidates);
        if (total_boundary_candidates != before) {
            if (stage_trace.enabled) std.debug.print(
                "admitted_exact_boundary_scan function={} candidates={}\n",
                .{ function.id.index(), total_boundary_candidates - before },
            );
        }
    }

    if (stage_trace.enabled) std.debug.print(
        "admitted_exact_boundary_mask blocks={} candidates={} ms={}\n",
        .{
            program.blocks.len,
            total_boundary_candidates,
            @divTrunc(Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds - trace_start, std.time.ns_per_ms),
        },
    );
    return boundary_candidates;
}

fn markAdmittedExactBoundaryRegion(
    program: *const ir.Program,
    region: *const structure.Region,
    boundary_candidates: []bool,
    total_boundary_candidates: *usize,
) void {
    for (region.nodes) |node| markAdmittedExactBoundaryNode(
        program,
        node,
        boundary_candidates,
        total_boundary_candidates,
    );
}

fn markAdmittedExactBoundaryNode(
    program: *const ir.Program,
    node: structure.Node,
    boundary_candidates: []bool,
    total_boundary_candidates: *usize,
) void {
    switch (node) {
        .block, .loop_control, .loop_terminal => {},
        .branch => |branch| {
            markAdmittedExactBoundaryRegion(program, branch.then_region, boundary_candidates, total_boundary_candidates);
            markAdmittedExactBoundaryRegion(program, branch.else_region, boundary_candidates, total_boundary_candidates);
        },
        .loop => |loop| {
            markAdmittedExactBoundaryRegion(program, loop.body_region, boundary_candidates, total_boundary_candidates);
        },
        .latch_loop => |loop| {
            markAdmittedExactBoundaryRegion(program, loop.body_region, boundary_candidates, total_boundary_candidates);
        },
        .infinite_loop => |loop| {
            if (loop.exit == null and loop.body_region.nodes.len == 1) {
                switch (loop.body_region.nodes[0]) {
                    .loop_boundary => |boundary| {
                        const is_normal_exit = switch (boundary.boundary) {
                            .exit => true,
                            else => false,
                        };
                        if (is_normal_exit and boundary.block == loop.header and
                            loop.header.index() < program.blocks.len)
                        {
                            const block = program.blocks[loop.header.index()];
                            const is_exact_branch = switch (block.terminator) {
                                .branch => |branch| exactBranchTruth(program, branch.condition, null) != .unknown,
                                else => false,
                            };
                            if (is_exact_branch and !boundary_candidates[loop.header.index()]) {
                                boundary_candidates[loop.header.index()] = true;
                                total_boundary_candidates.* += 1;
                            }
                        }
                    },
                    else => {},
                }
            }
            markAdmittedExactBoundaryRegion(program, loop.body_region, boundary_candidates, total_boundary_candidates);
            if (loop.shared_side_exit) |side_exit| {
                for (side_exit.entries) |entry| {
                    markAdmittedExactBoundaryRegion(program, entry.region, boundary_candidates, total_boundary_candidates);
                }
            }
        },
        .loop_boundary => |boundary| {
            markAdmittedExactBoundaryRegion(program, boundary.body_region, boundary_candidates, total_boundary_candidates);
            switch (boundary.boundary) {
                .side_exit => |side_exit| markAdmittedExactBoundaryRegion(
                    program,
                    side_exit.region,
                    boundary_candidates,
                    total_boundary_candidates,
                ),
                .side_escape => |side_escape| markAdmittedExactBoundaryRegion(
                    program,
                    side_escape.region,
                    boundary_candidates,
                    total_boundary_candidates,
                ),
                .exit, .escape, .terminal, .shared_exit => {},
            }
        },
    }
}

fn promotedTruth(program: *const ir.Program, promoted: ?ir.SolverTermId) solver.Truth {
    const term_id = promoted orelse return .unknown;
    if (!solver_preconditions.termPreconditionsProved(program, term_id, solver.evaluatesTrue)) return .unknown;
    return solver.evaluateTruth(program, term_id);
}

fn appendPairedClaims(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    block_id: ir.BlockId,
    goals: [2]ir.SolverTermId,
    assumptions: []const ir.ConstraintId,
    path_rewrites: []const ir.EdgeRewriteId,
    queries: *std.ArrayList(ir.SolverQuery),
    claims: *std.ArrayList(ir.Claim),
) !void {
    if (assumptions.len == 0) return;
    for (goals) |goal| {
        const query_id = try ensureQuery(allocator, queries, goal, .prove_true, assumptions, path_rewrites);
        if (hasBlockClaim(claims.items, block_id, query_id)) continue;
        const certificate_id = findResolvedCertificate(program.certificates, query_id);
        const status: ir.ClaimStatus = if (certificate_id) |id|
            switch (program.certificates[id.index()].resolution) {
                .proved => .proved,
                .disproved => .disproved,
                .unknown => .unproven,
            }
        else
            .unproven;
        try claims.append(allocator, .{
            .id = ir.ClaimId.fromIndex(claims.items.len),
            .subject = .{ .block = block_id },
            .predicate = goal,
            .status = status,
            .query = query_id,
            .certificate = certificate_id,
        });
    }
}

fn findValueTerm(terms: []const ir.SolverTerm, value_id: ir.ValueId) ?ir.SolverTermId {
    for (terms) |term| {
        if (term.sort.kind != .boolean) continue;
        switch (term.operation) {
            .value => |candidate| if (candidate == value_id) return term.id,
            .value_definition => |definition| if (definition.value == value_id) return term.id,
            else => {},
        }
    }
    return null;
}

fn findDynamicValueTerm(terms: []const ir.SolverTerm, value_id: ir.ValueId) ?ir.SolverTermId {
    for (terms) |term| {
        if (term.sort.kind != .dynamic_value) continue;
        switch (term.operation) {
            .value => |candidate| if (candidate == value_id) return term.id,
            else => {},
        }
    }
    return null;
}

fn findDynamicTruthinessTerm(terms: []const ir.SolverTerm, operand: ir.SolverTermId) ?ir.SolverTermId {
    for (terms) |term| switch (term.operation) {
        .dynamic_truthiness => |candidate| if (candidate == operand) return term.id,
        else => {},
    };
    return null;
}

fn findBooleanLiteral(terms: []const ir.SolverTerm, truth: bool) ?ir.SolverTermId {
    for (terms) |term| switch (term.operation) {
        .boolean_literal => |candidate| if (candidate == truth) return term.id,
        else => {},
    };
    return null;
}

fn findValueDefinition(terms: []const ir.SolverTerm, value_id: ir.ValueId) ?ir.SolverTermId {
    for (terms) |term| switch (term.operation) {
        .value_definition => |definition| if (definition.value == value_id) return term.id,
        else => {},
    };
    return null;
}

fn findNegatedTerm(terms: []const ir.SolverTerm, operand: ir.SolverTermId) ?ir.SolverTermId {
    for (terms) |term| switch (term.operation) {
        .logical_not => |candidate| if (candidate == operand) return term.id,
        else => {},
    };
    return null;
}

fn ensureQuery(
    allocator: std.mem.Allocator,
    queries: *std.ArrayList(ir.SolverQuery),
    goal: ir.SolverTermId,
    kind: ir.QueryKind,
    assumptions: []const ir.ConstraintId,
    path_rewrites: []const ir.EdgeRewriteId,
) !ir.QueryId {
    for (queries.items) |query| {
        if (query.kind == kind and
            query.goal == goal and
            std.mem.eql(ir.ConstraintId, query.assumptions, assumptions) and
            std.mem.eql(ir.EdgeRewriteId, query.path_rewrites, path_rewrites)) return query.id;
    }
    const id = ir.QueryId.fromIndex(queries.items.len);
    try queries.append(allocator, .{
        .id = id,
        .kind = kind,
        .assumptions = try allocator.dupe(ir.ConstraintId, assumptions),
        .path_rewrites = try allocator.dupe(ir.EdgeRewriteId, path_rewrites),
        .goal = goal,
    });
    return id;
}

fn hasControlBranchObligation(
    obligations: []const ir.Obligation,
    block_id: ir.BlockId,
    branch: ir.Branch,
    query_id: ir.QueryId,
) bool {
    for (obligations) |obligation| {
        if (obligation.query == null or obligation.query.? != query_id) continue;
        switch (obligation.subject) {
            .control_branch => |candidate| if (candidate.block == block_id and sameBranch(candidate.branch, branch)) return true,
            else => {},
        }
    }
    return false;
}

pub fn branchTruthinessEvidenceAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    block: ir.Block,
    condition: ir.ValueId,
) std.mem.Allocator.Error![]const ir.EvidenceId {
    var evidence: std.ArrayList(ir.EvidenceId) = .empty;
    errdefer evidence.deinit(allocator);

    if (condition.index() < program.values.len) {
        const value = program.values[condition.index()];
        const origin_evidence: []const ir.EvidenceId = switch (value.origin) {
            .parameter => if (value.function.index() < program.functions.len)
                program.functions[value.function.index()].evidence
            else
                &.{},
            .block_parameter => |origin| if (origin.block.index() < program.blocks.len)
                program.blocks[origin.block.index()].evidence
            else
                &.{},
            .instruction_result => |origin| if (origin.instruction.index() < program.instructions.len)
                program.instructions[origin.instruction.index()].evidence
            else
                &.{},
            .capture => |capture_id| if (capture_id.index() < program.captures.len)
                program.captures[capture_id.index()].evidence
            else
                &.{},
        };
        try appendCanonicalEvidence(allocator, program, &evidence, origin_evidence);
    }
    try appendCanonicalEvidence(allocator, program, &evidence, block.evidence);
    return evidence.toOwnedSlice(allocator);
}

fn appendCanonicalEvidence(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    evidence: *std.ArrayList(ir.EvidenceId),
    candidates: []const ir.EvidenceId,
) std.mem.Allocator.Error!void {
    for (candidates) |candidate| {
        if (candidate.index() >= program.evidence.len) continue;
        var insert_at: usize = 0;
        while (insert_at < evidence.items.len and evidence.items[insert_at].index() < candidate.index()) : (insert_at += 1) {}
        if (insert_at < evidence.items.len and evidence.items[insert_at] == candidate) continue;

        try evidence.append(allocator, candidate);
        var move = evidence.items.len - 1;
        while (move > insert_at) : (move -= 1) evidence.items[move] = evidence.items[move - 1];
        evidence.items[insert_at] = candidate;
    }
}

fn findProvedCertificate(
    certificates: []const ir.SolverCertificate,
    query_id: ir.QueryId,
    required_evidence: []const ir.EvidenceId,
) ?ir.CertificateId {
    for (certificates) |certificate| {
        if (certificate.query == query_id and
            certificate.resolution == .proved and
            certificate.certificate_digest != null and
            proof_digest.isControlBranchDigest(certificate.certificate_digest.?) and
            evidenceCovers(certificate.evidence, required_evidence)) return certificate.id;
    }
    return null;
}

fn sameBranch(left: ir.Branch, right: ir.Branch) bool {
    return left.condition == right.condition and
        edge_path.sameEdge(left.then_edge, right.then_edge) and
        edge_path.sameEdge(left.else_edge, right.else_edge);
}

fn historicalBranch(program: *const ir.Program, source: ir.BlockId, live: ir.Branch) ?ir.Branch {
    return .{
        .condition = live.condition,
        .then_edge = reverseEdgeHistory(program, source, .branch_then, live.then_edge) orelse return null,
        .else_edge = reverseEdgeHistory(program, source, .branch_else, live.else_edge) orelse return null,
    };
}

fn reverseEdgeHistory(
    program: *const ir.Program,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    live: ir.Edge,
) ?ir.Edge {
    var current = live;
    var index = program.edge_rewrites.len;
    while (index != 0) {
        index -= 1;
        const rewrite = program.edge_rewrites[index];
        if (rewrite.source != source or rewrite.kind != kind) continue;
        if (!edge_path.sameEdge(rewrite.to, current)) return null;
        current = rewrite.from;
    }
    return current;
}

fn evidenceCovers(available: []const ir.EvidenceId, required: []const ir.EvidenceId) bool {
    for (required) |required_id| {
        var found = false;
        for (available) |available_id| {
            if (available_id != required_id) continue;
            found = true;
            break;
        }
        if (!found) return false;
    }
    return true;
}

fn findResolvedCertificate(certificates: []const ir.SolverCertificate, query_id: ir.QueryId) ?ir.CertificateId {
    for (certificates) |certificate| {
        if (certificate.query == query_id and certificate.resolution != .unknown) return certificate.id;
    }
    return null;
}

fn hasBlockClaim(claims: []const ir.Claim, block_id: ir.BlockId, query_id: ir.QueryId) bool {
    for (claims) |claim| {
        if (claim.query == null or claim.query.? != query_id) continue;
        switch (claim.subject) {
            .block => |candidate| if (candidate == block_id) return true,
            else => {},
        }
    }
    return false;
}

fn hasAnyRelevantConstraint(
    program: *const ir.Program,
    block: ir.Block,
    condition: ir.ValueId,
    promoted: ?ir.SolverTermId,
) bool {
    for (program.constraints) |constraint| {
        if (constraint.evidence.len != 0 and
            constraintCanReachBlock(program, constraint, block) and
            constraintRelevant(program, constraint.predicate, condition, promoted))
        {
            return true;
        }
    }
    return false;
}

fn hasRelevantBaseConstraint(
    program: *const ir.Program,
    block: ir.Block,
    condition: ir.ValueId,
    promoted: ?ir.SolverTermId,
) bool {
    for (program.constraints) |constraint| {
        if (constraint.evidence.len != 0 and
            baseConstraintApplies(constraint, block) and
            constraintRelevant(program, constraint.predicate, condition, promoted))
        {
            return true;
        }
    }
    return false;
}

const EdgePath = struct {
    root: ir.CfgEdgeRef,
    rewrites: []const ir.EdgeRewriteId,
};

fn relevantEdgePathAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    edge: ir.CfgEdgeRef,
    condition: ir.ValueId,
    promoted: ?ir.SolverTermId,
) !?EdgePath {
    for (program.constraints) |constraint| {
        const scoped_edge = switch (constraint.scope) {
            .edge => |value| value,
            else => continue,
        };
        if (constraint.evidence.len == 0 or !constraintRelevant(program, constraint.predicate, condition, promoted)) continue;
        const rewrites = try edge_path.pathForConstraintAlloc(allocator, program, constraint, edge) orelse continue;
        return .{ .root = scoped_edge, .rewrites = rewrites };
    }
    return null;
}

fn constraintRelevant(
    program: *const ir.Program,
    predicate: ir.SolverTermId,
    condition: ir.ValueId,
    promoted: ?ir.SolverTermId,
) bool {
    if (termOverlapsValueDependencies(program, predicate, condition, 0)) return true;
    return if (promoted) |root| termDependsOnTerm(program, root, predicate, 0) else false;
}

fn termDependsOnTerm(
    program: *const ir.Program,
    root: ir.SolverTermId,
    dependency: ir.SolverTermId,
    depth: usize,
) bool {
    if (root == dependency) return true;
    if (root.index() >= program.solver_terms.len or depth > program.solver_terms.len) return false;
    var dependencies = solver_term.dependencies(program.solver_terms[root.index()].operation);
    while (dependencies.next()) |candidate| {
        if (termDependsOnTerm(program, candidate, dependency, depth + 1)) return true;
    }
    return false;
}

fn samePath(left: []const ir.EdgeRewriteId, right: []const ir.EdgeRewriteId) bool {
    return std.mem.eql(ir.EdgeRewriteId, left, right);
}

fn edgeConstraintApplies(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    constraint: ir.Constraint,
    context: EdgePathContext,
) !bool {
    const scoped_edge = switch (constraint.scope) {
        .edge => |value| value,
        else => return false,
    };
    if (!std.meta.eql(scoped_edge, context.path.root)) return false;
    const rewrites = try edge_path.pathForConstraintAlloc(allocator, program, constraint, context.edge) orelse return false;
    return samePath(rewrites, context.path.rewrites);
}

const EdgePathContext = struct {
    edge: ir.CfgEdgeRef,
    path: EdgePath,
};

const ConstraintContext = union(enum) {
    base: void,
    edge: EdgePathContext,
};

fn baseConstraintApplies(constraint: ir.Constraint, block: ir.Block) bool {
    return switch (constraint.scope) {
        .explicit_only, .edge => false,
        .program => true,
        .function => |function_id| function_id == block.function,
        .block => |block_id| block_id == block.id,
    };
}

fn constraintCanReachBlock(program: *const ir.Program, constraint: ir.Constraint, block: ir.Block) bool {
    return switch (constraint.scope) {
        .edge => |scoped_edge| blk: {
            const current = cfg_edge.value(program, scoped_edge) orelse break :blk false;
            const effective = edge_path.constraintEffectiveTarget(program, constraint) orelse break :blk false;
            break :blk current.target == effective and effective == block.id;
        },
        else => baseConstraintApplies(constraint, block),
    };
}

fn constraintApplies(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    constraint: ir.Constraint,
    block: ir.Block,
    context: ConstraintContext,
) !bool {
    return switch (context) {
        .base => baseConstraintApplies(constraint, block),
        .edge => |edge_context| switch (constraint.scope) {
            .edge => try edgeConstraintApplies(allocator, program, constraint, edge_context),
            else => baseConstraintApplies(constraint, block),
        },
    };
}

fn termOverlapsValueDependencies(
    program: *const ir.Program,
    term_id: ir.SolverTermId,
    value_id: ir.ValueId,
    depth: usize,
) bool {
    if (term_id.index() >= program.solver_terms.len or depth > program.solver_terms.len) return false;
    const operation = program.solver_terms[term_id.index()].operation;
    switch (operation) {
        .value => |candidate| if (valueClosuresOverlap(program, value_id, candidate, 0)) return true,
        .value_definition => |definition| if (valueClosuresOverlap(program, value_id, definition.value, 0)) return true,
        else => {},
    }
    var dependencies = solver_term.dependencies(operation);
    while (dependencies.next()) |operand| {
        if (termOverlapsValueDependencies(program, operand, value_id, depth + 1)) return true;
    }
    return false;
}

fn valueClosuresOverlap(program: *const ir.Program, condition: ir.ValueId, candidate: ir.ValueId, depth: usize) bool {
    const limit = program.values.len + program.instructions.len;
    if (depth > limit) return false;
    if (valueDependsOn(program, condition, candidate, 0)) return true;
    const source = solver.normalizedValueSource(program, candidate) orelse return false;
    return switch (source) {
        .constant => false,
        .copy => |copy| valueClosuresOverlap(program, condition, copy.source, depth + 1),
        .unary => |unary| valueClosuresOverlap(program, condition, unary.operand, depth + 1),
        .binary => |binary| valueClosuresOverlap(program, condition, binary.left, depth + 1) or
            valueClosuresOverlap(program, condition, binary.right, depth + 1),
    };
}

fn valueDependsOn(program: *const ir.Program, value_id: ir.ValueId, dependency: ir.ValueId, depth: usize) bool {
    const limit = program.values.len + program.instructions.len;
    if (depth > limit) return false;
    if (value_id == dependency) return true;
    const source = solver.normalizedValueSource(program, value_id) orelse return false;
    return switch (source) {
        .constant => false,
        .copy => |copy| valueDependsOn(program, copy.source, dependency, depth + 1),
        .unary => |unary| valueDependsOn(program, unary.operand, dependency, depth + 1),
        .binary => |binary| valueDependsOn(program, binary.left, dependency, depth + 1) or
            valueDependsOn(program, binary.right, dependency, depth + 1),
    };
}

fn applicableConstraintsAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    block: ir.Block,
    context: ConstraintContext,
) ![]ir.ConstraintId {
    var assumptions: std.ArrayList(ir.ConstraintId) = .empty;
    for (program.constraints) |constraint| {
        if (constraint.evidence.len != 0 and try constraintApplies(allocator, program, constraint, block, context)) {
            try assumptions.append(allocator, constraint.id);
        }
    }
    return assumptions.toOwnedSlice(allocator);
}

fn incomingEdgesAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    target: ir.BlockId,
) ![]ir.CfgEdgeRef {
    var incoming: std.ArrayList(ir.CfgEdgeRef) = .empty;
    if (target.index() >= program.blocks.len) return incoming.toOwnedSlice(allocator);
    const function_id = program.blocks[target.index()].function;
    if (function_id.index() >= program.functions.len) return incoming.toOwnedSlice(allocator);
    var analysis = try cfg.Analysis.init(allocator, program, program.functions[function_id.index()]);
    defer analysis.deinit();
    for (program.blocks) |block| {
        if (!scope.block(block.id)) continue;
        switch (block.terminator) {
            .jump => |edge| if (edge.target == target and !analysis.dominates(target, block.id)) {
                try incoming.append(allocator, .{ .source = block.id, .kind = .jump, .target = target });
            },
            .branch => |branch| {
                if (!analysis.dominates(target, block.id)) {
                    if (branch.then_edge.target == target) try incoming.append(allocator, .{ .source = block.id, .kind = .branch_then, .target = target });
                    if (branch.else_edge.target == target) try incoming.append(allocator, .{ .source = block.id, .kind = .branch_else, .target = target });
                }
            },
            else => {},
        }
    }
    return incoming.toOwnedSlice(allocator);
}

test "natural and self loop backedges do not seed target-state proof queries" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const latch = ir.BlockId.fromIndex(2);
    const condition = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = latch } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = latch },
        } } },
    };
    const program: ir.Program = .{
        .program_id = "cyclic-edge-query-refusal",
        .entry_function = function_id,
        .functions = &.{.{
            .id = function_id,
            .entry_block = entry,
            .parameters = &.{condition},
            .blocks = &.{ entry, header, latch },
        }},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer scope.deinit();
    const header_incoming = try incomingEdgesAlloc(std.testing.allocator, &program, &scope, header);
    defer std.testing.allocator.free(header_incoming);
    try std.testing.expectEqual(@as(usize, 1), header_incoming.len);
    try std.testing.expectEqual(entry, header_incoming[0].source);
    try std.testing.expectEqual(ir.CfgEdgeKind.jump, header_incoming[0].kind);

    const latch_incoming = try incomingEdgesAlloc(std.testing.allocator, &program, &scope, latch);
    defer std.testing.allocator.free(latch_incoming);
    try std.testing.expectEqual(@as(usize, 1), latch_incoming.len);
    try std.testing.expectEqual(header, latch_incoming[0].source);
    try std.testing.expectEqual(ir.CfgEdgeKind.jump, latch_incoming[0].kind);
}

test "unreachable branches do not create backend facts or proof work" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const dead_branch_id = ir.BlockId.fromIndex(1);
    const dead_then_id = ir.BlockId.fromIndex(2);
    const dead_else_id = ir.BlockId.fromIndex(3);
    const condition_id = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = condition_id,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = dead_branch_id, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition_id,
            .then_edge = .{ .target = dead_then_id },
            .else_edge = .{ .target = dead_else_id },
        } } },
        .{ .id = dead_then_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = dead_else_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .parameters = &.{condition_id},
        .entry_block = entry_id,
        .blocks = &.{ entry_id, dead_branch_id, dead_then_id, dead_else_id },
    };
    const program: ir.Program = .{
        .program_id = "unreachable-branch-proof-planning",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const expanded = try expandInArena(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 0), expanded.solver_terms.len);
    try std.testing.expectEqual(@as(usize, 0), expanded.constraints.len);
    try std.testing.expectEqual(@as(usize, 0), expanded.evidence.len);
    try std.testing.expectEqual(@as(usize, 0), expanded.queries.len);
    try std.testing.expectEqual(@as(usize, 0), expanded.claims.len);
    try std.testing.expectEqual(@as(usize, 0), expanded.obligations.len);
}

test "exact branch facts synthesize family-neutral proof work" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_is_negative.index()].operation = .{ .constant = .{ .boolean = true } };
    var program = fixture.program;
    program.instructions = &instructions;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const expanded = try expandInArena(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 2), expanded.solver_terms.len);
    try std.testing.expectEqual(@as(usize, 1), expanded.queries.len);
    try std.testing.expectEqual(@as(usize, 1), expanded.obligations.len);
    try std.testing.expectEqual(ir.ObligationStatus.open, expanded.obligations[0].status);
    try std.testing.expectEqual(fixture.b_entry, expanded.obligations[0].subject.control_branch.block);
    try std.testing.expect(control_flow.sameBranch(
        fixture.blocks[fixture.b_entry.index()].terminator.branch,
        expanded.obligations[0].subject.control_branch.branch,
    ));
    try std.testing.expectEqual(ir.QueryKind.prove_true, expanded.queries[0].kind);
    const goal = expanded.solver_terms[expanded.queries[0].goal.index()];
    try std.testing.expect(goal.operation == .value_definition);
    try std.testing.expectEqual(fixture.v_is_negative, goal.operation.value_definition.value);
}

test "pre-normalization exact branches do not require loop classification" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_is_negative.index()].operation = .{ .constant = .{ .boolean = true } };
    var program = fixture.program;
    program.instructions = &instructions;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var planning = try State.initExact(arena.allocator(), &program);
    const expanded = try planning.expandExactBranches(&program);
    try std.testing.expectEqual(@as(usize, 1), expanded.queries.len);
    try std.testing.expectEqual(@as(usize, 1), expanded.obligations.len);
    try std.testing.expectEqual(fixture.b_entry, expanded.obligations[0].subject.control_branch.block);
    try std.testing.expectEqual(ir.QueryKind.prove_true, expanded.queries[0].kind);

    var effectful_instructions = instructions;
    effectful_instructions[fixture.i_is_negative.index()].effects = .{
        .precision = .exact,
        .may_throw = true,
    };
    var effectful_program = fixture.program;
    effectful_program.instructions = &effectful_instructions;
    var effectful_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer effectful_arena.deinit();
    var effectful_planning = try State.initExact(effectful_arena.allocator(), &effectful_program);
    const rejected = try effectful_planning.expandExactBranches(&effectful_program);
    try std.testing.expectEqual(@as(usize, 0), rejected.queries.len);
    try std.testing.expectEqual(@as(usize, 0), rejected.obligations.len);
}

test "exact dynamic branches plan explicit truthiness without prior constraints" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const then_id = ir.BlockId.fromIndex(1);
    const else_id = ir.BlockId.fromIndex(2);
    const literal = ir.ValueId.fromIndex(0);
    const condition = ir.ValueId.fromIndex(1);
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = entry_id, .operation = .{ .constant = .{ .string = "truthy" } }, .results = &.{literal}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = entry_id, .operation = .{ .copy = literal }, .results = &.{condition}, .effects = .pure },
    };
    const values = [_]ir.Value{
        .{ .id = literal, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = condition, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .instructions = &.{ ir.InstructionId.fromIndex(0), ir.InstructionId.fromIndex(1) }, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = then_id },
            .else_edge = .{ .target = else_id },
        } } },
        .{ .id = then_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = else_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const program: ir.Program = .{
        .program_id = "explicit-dynamic-branch-truthiness",
        .entry_function = function_id,
        .functions = &.{.{ .id = function_id, .entry_block = entry_id, .blocks = &.{ entry_id, then_id, else_id } }},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const expanded = try expandInArena(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 2), expanded.solver_terms.len);
    try std.testing.expectEqual(condition, expanded.solver_terms[0].operation.value);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(0), expanded.solver_terms[1].operation.dynamic_truthiness);
    try std.testing.expectEqual(@as(usize, 1), expanded.queries.len);
    try std.testing.expectEqual(ir.QueryKind.prove_true, expanded.queries[0].kind);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(1), expanded.queries[0].goal);
    try std.testing.expectEqual(ir.SolverResolution.proved, solver.solve(&expanded, expanded.queries[0]));
}

test "concrete scalar branch domains plan exact Luau truthiness" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const then_id = ir.BlockId.fromIndex(1);
    const else_id = ir.BlockId.fromIndex(2);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = then_id },
            .else_edge = .{ .target = else_id },
        } } },
        .{ .id = then_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = else_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const rows = [_]struct { value_type: ir.ValueType, truth: bool }{
        .{ .value_type = .{ .kind = .nil_value }, .truth = false },
        .{ .value_type = .integer, .truth = true },
        .{ .value_type = .number, .truth = true },
        .{ .value_type = .string, .truth = true },
        .{ .value_type = .{ .kind = .table }, .truth = true },
        .{ .value_type = .function, .truth = true },
        .{ .value_type = .{ .kind = .thread }, .truth = true },
        .{ .value_type = .{ .kind = .userdata }, .truth = true },
    };
    for (rows) |row| {
        const values = [_]ir.Value{.{
            .id = condition,
            .function = function_id,
            .type = row.value_type,
            .origin = .{ .parameter = 0 },
        }};
        const program: ir.Program = .{
            .program_id = "concrete-branch-truthiness",
            .entry_function = function_id,
            .functions = &.{.{
                .id = function_id,
                .parameters = &.{condition},
                .entry_block = entry_id,
                .blocks = &.{ entry_id, then_id, else_id },
            }},
            .blocks = &blocks,
            .instructions = &.{},
            .values = &values,
        };

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const expanded = try expandInArena(arena.allocator(), &program);
        try std.testing.expectEqual(@as(usize, 1), expanded.queries.len);
        try std.testing.expectEqual(if (row.truth) ir.QueryKind.prove_true else ir.QueryKind.prove_false, expanded.queries[0].kind);
        const goal = expanded.solver_terms[expanded.queries[0].goal.index()];
        try std.testing.expectEqual(row.truth, goal.operation.boolean_literal);
        try std.testing.expectEqual(ir.SolverResolution.proved, solver.solve(&expanded, expanded.queries[0]));
    }
}

test "concrete branch provenance follows every value origin" {
    const function_id = ir.FunctionId.fromIndex(0);
    const origin_block_id = ir.BlockId.fromIndex(0);
    const branch_block_id = ir.BlockId.fromIndex(1);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const capture_id = ir.CaptureId.fromIndex(0);
    const parameter = ir.ValueId.fromIndex(0);
    const block_parameter = ir.ValueId.fromIndex(1);
    const instruction_result = ir.ValueId.fromIndex(2);
    const capture_value = ir.ValueId.fromIndex(3);
    const function_evidence = ir.EvidenceId.fromIndex(0);
    const origin_block_evidence = ir.EvidenceId.fromIndex(1);
    const instruction_evidence = ir.EvidenceId.fromIndex(2);
    const capture_evidence = ir.EvidenceId.fromIndex(3);
    const branch_evidence = ir.EvidenceId.fromIndex(4);
    const evidence = [_]ir.Evidence{
        .{ .id = function_evidence, .kind = .dynamic_fixture, .locator = "fixture:branch-function-origin" },
        .{ .id = origin_block_evidence, .kind = .dynamic_fixture, .locator = "fixture:branch-block-origin" },
        .{ .id = instruction_evidence, .kind = .dynamic_fixture, .locator = "fixture:branch-instruction-origin" },
        .{ .id = capture_evidence, .kind = .dynamic_fixture, .locator = "fixture:branch-capture-origin" },
        .{ .id = branch_evidence, .kind = .dynamic_fixture, .locator = "fixture:branch-context" },
    };
    const values = [_]ir.Value{
        .{ .id = parameter, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = block_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = origin_block_id, .index = 0 } } },
        .{ .id = instruction_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } } },
        .{ .id = capture_value, .function = function_id, .type = .integer, .origin = .{ .capture = capture_id } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = origin_block_id,
        .operation = .{ .constant = .{ .integer = "1" } },
        .results = &.{instruction_result},
        .effects = .pure,
        .evidence = &.{instruction_evidence},
    }};
    const blocks = [_]ir.Block{
        .{
            .id = origin_block_id,
            .function = function_id,
            .parameters = &.{block_parameter},
            .instructions = &.{instruction_id},
            .terminator = .{ .return_values = &.{} },
            .evidence = &.{origin_block_evidence},
        },
        .{
            .id = branch_block_id,
            .function = function_id,
            .terminator = .{ .return_values = &.{} },
            .evidence = &.{branch_evidence},
        },
    };
    const captures = [_]ir.Capture{.{
        .id = capture_id,
        .function = function_id,
        .kind = .{ .immutable_value = parameter },
        .evidence = &.{capture_evidence},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{parameter},
        .captures = &.{capture_id},
        .blocks = &.{ origin_block_id, branch_block_id },
        .entry_block = origin_block_id,
        .evidence = &.{function_evidence},
    }};
    const program: ir.Program = .{
        .program_id = "concrete-branch-origin-provenance",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .captures = &captures,
        .evidence = &evidence,
    };
    const rows = [_]struct {
        condition: ir.ValueId,
        expected: []const ir.EvidenceId,
    }{
        .{ .condition = parameter, .expected = &.{ function_evidence, branch_evidence } },
        .{ .condition = block_parameter, .expected = &.{ origin_block_evidence, branch_evidence } },
        .{ .condition = instruction_result, .expected = &.{ instruction_evidence, branch_evidence } },
        .{ .condition = capture_value, .expected = &.{ capture_evidence, branch_evidence } },
    };

    for (rows) |row| {
        const actual = try branchTruthinessEvidenceAlloc(std.testing.allocator, &program, blocks[branch_block_id.index()], row.condition);
        defer std.testing.allocator.free(actual);
        try std.testing.expectEqualSlices(ir.EvidenceId, row.expected, actual);
    }
}

test "straight-line expansion publishes normalized unresolved query state" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const terms = [_]ir.SolverTerm{
        .{
            .id = ir.SolverTermId.fromIndex(0),
            .sort = .{ .kind = .integer },
            .operation = .{ .value = fixture.v_result },
        },
        .{
            .id = ir.SolverTermId.fromIndex(1),
            .sort = .{ .kind = .boolean },
            .operation = .{ .binary = .{
                .operator = .equal,
                .left = ir.SolverTermId.fromIndex(0),
                .right = ir.SolverTermId.fromIndex(0),
            } },
        },
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
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var state = try State.init(arena.allocator(), &program);
    const expanded = try state.expand(&program);

    try std.testing.expectEqual(@as(usize, 1), expanded.queries.len);
    try std.testing.expect(expanded.queries[0].goal != queries[0].goal);
    try std.testing.expectEqual(expanded.queries[0].goal, expanded.claims[0].predicate);
    try std.testing.expectEqual(ir.SolverResolution.proved, solver.solve(&expanded, expanded.queries[0]));
}

test "value definitions retain their bound identity for query relevance" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    const terms = [_]ir.SolverTerm{
        .{
            .id = ir.SolverTermId.fromIndex(0),
            .sort = .{ .kind = .boolean },
            .operation = .{ .boolean_literal = true },
        },
        .{
            .id = ir.SolverTermId.fromIndex(1),
            .sort = .{ .kind = .boolean },
            .operation = .{ .value_definition = .{
                .value = fixture.v_is_negative,
                .expression = ir.SolverTermId.fromIndex(0),
            } },
        },
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    try std.testing.expectEqual(ir.SolverTermId.fromIndex(1), findValueTerm(&terms, fixture.v_is_negative).?);
    try std.testing.expect(termOverlapsValueDependencies(&program, ir.SolverTermId.fromIndex(1), fixture.v_is_negative, 0));
}

test "scoped facts synthesize paired nonblocking branch queries" {
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
        .scope = .{ .block = fixture.b_entry },
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const expanded = try expandInArena(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 2), expanded.solver_terms.len);
    try std.testing.expectEqual(@as(usize, 2), expanded.queries.len);
    try std.testing.expectEqual(@as(usize, 2), expanded.claims.len);
    try std.testing.expectEqual(@as(usize, 0), expanded.obligations.len);
    try std.testing.expectEqualSlices(ir.ConstraintId, &.{ir.ConstraintId.fromIndex(0)}, expanded.queries[0].assumptions);
    try std.testing.expectEqual(ir.QueryKind.prove_true, expanded.queries[0].kind);
    try std.testing.expectEqual(ir.QueryKind.prove_true, expanded.queries[1].kind);
    try std.testing.expect(expanded.solver_terms[expanded.queries[1].goal.index()].operation == .logical_not);
}

test "unrelated scoped facts do not multiply branch queries" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{fixture.proof},
        .scope = .{ .program = {} },
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const expanded = try expandInArena(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 0), expanded.queries.len);
    try std.testing.expectEqual(@as(usize, 0), expanded.claims.len);
}

test "edge facts create path-specific dispatcher queries without predecessor leakage" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const left_id = ir.BlockId.fromIndex(1);
    const right_id = ir.BlockId.fromIndex(2);
    const dispatch_id = ir.BlockId.fromIndex(3);
    const true_id = ir.BlockId.fromIndex(4);
    const false_id = ir.BlockId.fromIndex(5);
    const entry_condition = ir.ValueId.fromIndex(0);
    const dispatch_condition = ir.ValueId.fromIndex(1);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .branch = .{
            .condition = entry_condition,
            .then_edge = .{ .target = left_id },
            .else_edge = .{ .target = right_id },
        } } },
        .{ .id = left_id, .function = function_id, .terminator = .{ .jump = .{ .target = dispatch_id, .arguments = &.{entry_condition} } } },
        .{ .id = right_id, .function = function_id, .terminator = .{ .jump = .{ .target = dispatch_id, .arguments = &.{entry_condition} } } },
        .{ .id = dispatch_id, .function = function_id, .parameters = &.{dispatch_condition}, .terminator = .{ .branch = .{
            .condition = dispatch_condition,
            .then_edge = .{ .target = true_id },
            .else_edge = .{ .target = false_id },
        } } },
        .{ .id = true_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = false_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const values = [_]ir.Value{
        .{ .id = entry_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = dispatch_condition, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = dispatch_id, .index = 0 } } },
    };
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = dispatch_condition },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{evidence_id},
        .scope = .{ .edge = .{ .source = left_id, .kind = .jump, .target = dispatch_id } },
    }};
    const program: ir.Program = .{
        .program_id = "edge-scoped-dispatch-query",
        .entry_function = function_id,
        .functions = &.{.{
            .id = function_id,
            .parameters = &.{entry_condition},
            .entry_block = entry_id,
            .blocks = &.{ entry_id, left_id, right_id, dispatch_id, true_id, false_id },
        }},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &.{.{ .id = evidence_id, .kind = .dynamic_fixture, .locator = "fixture:edge-scoped-dispatch-query" }},
        .solver_terms = &terms,
        .constraints = &constraints,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const expanded = try expandInArena(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 4), expanded.queries.len);
    try std.testing.expectEqual(@as(usize, 4), expanded.claims.len);
    var left_queries: usize = 0;
    var right_queries: usize = 0;
    for (expanded.queries) |query| {
        const root = switch (edge_path.queryRoot(&expanded, query)) {
            .one => |edge| edge,
            .none, .ambiguous => return error.TestExpectedSingleEdgeRoot,
        };
        const expected_assumptions: usize = if (root.source == left_id) 2 else if (root.source == right_id) 1 else return error.TestUnexpectedEdgeRoot;
        if (root.source == left_id) left_queries += 1 else right_queries += 1;
        try std.testing.expectEqual(expected_assumptions, query.assumptions.len);
        for (query.assumptions) |constraint_id| {
            const scoped = expanded.constraints[constraint_id.index()].scope.edge;
            try std.testing.expectEqual(root.source, scoped.source);
            try std.testing.expectEqual(root.kind, scoped.kind);
            try std.testing.expectEqual(root.target, scoped.target);
        }
    }
    try std.testing.expectEqual(@as(usize, 2), left_queries);
    try std.testing.expectEqual(@as(usize, 2), right_queries);
    for (expanded.claims) |claim| try std.testing.expectEqual(dispatch_id, claim.subject.block);
}

test "edge facts on a branch arm that carries its own condition replay against the arm truth" {
    // T4-ARM-FACTS-ORDER: the dispatcher test above with its forwarders removed. Each arm of the
    // entry branch passes the branch condition straight to the dispatch parameter, so the arm's own
    // truth fact decides the argument. Every structural fact must replay as the validator replays it
    // (validate_proofs.zig -> edge_facts.replaysConstraint): on the then-arm `dispatch_condition`, on
    // the else-arm `not dispatch_condition`, not an equality with `entry_condition`.
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const dispatch_id = ir.BlockId.fromIndex(1);
    const true_id = ir.BlockId.fromIndex(2);
    const false_id = ir.BlockId.fromIndex(3);
    const entry_condition = ir.ValueId.fromIndex(0);
    const dispatch_condition = ir.ValueId.fromIndex(1);
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .branch = .{
            .condition = entry_condition,
            .then_edge = .{ .target = dispatch_id, .arguments = &.{entry_condition} },
            .else_edge = .{ .target = dispatch_id, .arguments = &.{entry_condition} },
        } } },
        .{ .id = dispatch_id, .function = function_id, .parameters = &.{dispatch_condition}, .terminator = .{ .branch = .{
            .condition = dispatch_condition,
            .then_edge = .{ .target = true_id },
            .else_edge = .{ .target = false_id },
        } } },
        .{ .id = true_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = false_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const values = [_]ir.Value{
        .{ .id = entry_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = dispatch_condition, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = dispatch_id, .index = 0 } } },
    };
    const program: ir.Program = .{
        .program_id = "branch-arm-carries-own-condition",
        .entry_function = function_id,
        .functions = &.{.{
            .id = function_id,
            .parameters = &.{entry_condition},
            .entry_block = entry_id,
            .blocks = &.{ entry_id, dispatch_id, true_id, false_id },
        }},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const expanded = try expandInArena(arena.allocator(), &program);
    var arm_arguments: usize = 0;
    for (expanded.constraints) |constraint| {
        if (constraint.evidence.len != 1 or !edge_facts.isStructuralEvidence(expanded.evidence[constraint.evidence[0].index()])) continue;
        try std.testing.expect(edge_facts.replaysConstraint(&expanded, constraint));
        const scoped = switch (constraint.scope) {
            .edge => |edge| edge,
            else => continue,
        };
        if (scoped.source != entry_id) continue;
        switch (expanded.solver_terms[constraint.predicate.index()].operation) {
            .value => |value| if (value == dispatch_condition) {
                try std.testing.expectEqual(ir.CfgEdgeKind.branch_then, scoped.kind);
                arm_arguments += 1;
            },
            .logical_not => |operand| switch (expanded.solver_terms[operand.index()].operation) {
                .value => |value| if (value == dispatch_condition) {
                    try std.testing.expectEqual(ir.CfgEdgeKind.branch_else, scoped.kind);
                    arm_arguments += 1;
                },
                else => {},
            },
            else => {},
        }
    }
    try std.testing.expectEqual(@as(usize, 2), arm_arguments);
}

test "edge facts over numeric state plan queries for a derived dispatcher condition" {
    const fixture = @import("fixtures.zig").relational_dispatch_module;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const expanded = try expandInArena(arena.allocator(), &fixture.program);
    try std.testing.expect(expanded.solver_terms.len > fixture.solver_terms.len);
    var has_next_state_definition = false;
    var has_condition_definition = false;
    for (expanded.solver_terms) |term| switch (term.operation) {
        .value_definition => |definition| {
            if (definition.value == fixture.v_next_state) has_next_state_definition = true;
            if (definition.value == fixture.v_condition) has_condition_definition = true;
        },
        else => {},
    };
    try std.testing.expect(has_next_state_definition);
    try std.testing.expect(has_condition_definition);
    try std.testing.expectEqual(@as(usize, 8), expanded.constraints.len);
    try std.testing.expectEqual(@as(usize, 4), expanded.queries.len);
    try std.testing.expectEqual(@as(usize, 4), expanded.claims.len);
    var left_queries: usize = 0;
    var right_queries: usize = 0;
    for (expanded.queries) |query| {
        const root = switch (edge_path.queryRoot(&expanded, query)) {
            .one => |edge| edge,
            .none, .ambiguous => return error.TestExpectedSingleEdgeRoot,
        };
        const expected_frontend = if (root.source == fixture.b_left)
            fixture.c_left
        else if (root.source == fixture.b_right)
            fixture.c_right
        else
            return error.TestUnexpectedEdgeRoot;
        if (root.source == fixture.b_left) left_queries += 1 else right_queries += 1;
        try std.testing.expectEqual(@as(usize, 2), query.assumptions.len);
        try std.testing.expectEqual(expected_frontend, query.assumptions[0]);
        const structural = expanded.constraints[query.assumptions[1].index()];
        try std.testing.expect(edge_facts.isStructuralEvidence(expanded.evidence[structural.evidence[0].index()]));
        const scoped = structural.scope.edge;
        try std.testing.expectEqual(root.source, scoped.source);
        try std.testing.expectEqual(root.kind, scoped.kind);
        try std.testing.expectEqual(root.target, scoped.target);
    }
    try std.testing.expectEqual(@as(usize, 2), left_queries);
    try std.testing.expectEqual(@as(usize, 2), right_queries);
    const goal_value = switch (expanded.solver_terms[expanded.queries[0].goal.index()].operation) {
        .value => |value| value,
        .value_definition => |definition| definition.value,
        else => return error.TestExpectedValueGoal,
    };
    try std.testing.expectEqual(fixture.v_condition, goal_value);
}
