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
            std.debug.print(
                "exact_branch_boundary_candidate function={} block={} then={} else={} truth={s}\n",
                .{ function.id.index(), block.id.index(), branch.then_edge.target.index(), branch.else_edge.target.index(), @tagName(truth) },
            );
        }
        std.debug.print(
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

    std.debug.print(
        "exact_branch_boundary_mask blocks={} candidates={} ms={}\n",
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
