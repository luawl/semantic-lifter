const std = @import("std");
const ir = @import("ir.zig");
const proof_closure = @import("proof_closure.zig");

pub const Consumer = union(enum) {
    claim: ir.ClaimId,
    obligation: ir.ObligationId,
};

pub const WorkItem = struct {
    query: ir.QueryId,
    consumers: []Consumer,
    evidence: []ir.EvidenceId,
};

pub const Plan = struct {
    allocator: std.mem.Allocator,
    items: []WorkItem,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program) !Plan {
        var items: std.ArrayList(WorkItem) = .empty;
        errdefer {
            destroyItems(allocator, items.items);
            items.deinit(allocator);
        }

        for (program.queries) |query| {
            var consumers: std.ArrayList(Consumer) = .empty;
            errdefer consumers.deinit(allocator);
            var evidence: std.ArrayList(ir.EvidenceId) = .empty;
            errdefer evidence.deinit(allocator);
            var subject_closure: ?proof_closure.Closure = null;
            defer if (subject_closure) |*closure| closure.deinit();

            for (program.claims, 0..) |claim, claim_index| {
                if (!claimIsEligible(claim, query)) continue;
                try consumers.append(allocator, .{ .claim = ir.ClaimId.fromIndex(claim_index) });
                for (claim.evidence) |evidence_id| {
                    if (evidence_id.index() < program.evidence.len) try appendUniqueEvidence(allocator, &evidence, evidence_id);
                }
            }
            for (program.obligations, 0..) |obligation, obligation_index| {
                if (!obligationIsEligible(obligation, query)) continue;
                if (subject_closure == null) subject_closure = try proof_closure.Closure.initForObligationSubject(allocator, program, query);
                if (!subject_closure.?.coversObligationSubject(program, obligation.subject)) return error.InvalidObligationSubject;
                try consumers.append(allocator, .{ .obligation = ir.ObligationId.fromIndex(obligation_index) });
                for (obligation.evidence) |evidence_id| {
                    if (evidence_id.index() < program.evidence.len) try appendUniqueEvidence(allocator, &evidence, evidence_id);
                }
            }
            if (consumers.items.len == 0) {
                consumers.deinit(allocator);
                evidence.deinit(allocator);
                continue;
            }

            var closure = try proof_closure.Closure.init(allocator, program, query, evidence.items, &.{});
            defer closure.deinit();
            evidence.clearRetainingCapacity();
            for (closure.evidence, 0..) |needed, evidence_index| {
                if (needed) try evidence.append(allocator, ir.EvidenceId.fromIndex(evidence_index));
            }
            const owned_consumers = try consumers.toOwnedSlice(allocator);
            errdefer allocator.free(owned_consumers);
            const owned_evidence = try evidence.toOwnedSlice(allocator);
            errdefer allocator.free(owned_evidence);
            try items.append(allocator, .{
                .query = query.id,
                .consumers = owned_consumers,
                .evidence = owned_evidence,
            });
        }
        return .{
            .allocator = allocator,
            .items = try items.toOwnedSlice(allocator),
        };
    }

    pub fn deinit(self: *Plan) void {
        destroyItems(self.allocator, self.items);
        self.allocator.free(self.items);
        self.* = undefined;
    }
};

pub fn claimIsEligible(claim: ir.Claim, query: ir.SolverQuery) bool {
    if (claim.status != .unproven or claim.certificate != null or claim.query == null or claim.query.? != query.id) return false;
    if (query.goal != claim.predicate) return false;
    return query.kind == .prove_true or query.kind == .prove_equivalent;
}

pub fn obligationIsEligible(obligation: ir.Obligation, query: ir.SolverQuery) bool {
    const requirement = obligation.requirement orelse return false;
    return obligation.status == .open and
        obligation.certificate == null and
        obligation.query != null and
        obligation.query.? == query.id and
        requirement.kind == query.kind and
        requirement.predicate == query.goal;
}

fn appendUniqueEvidence(allocator: std.mem.Allocator, evidence: *std.ArrayList(ir.EvidenceId), candidate: ir.EvidenceId) !void {
    for (evidence.items) |existing| if (existing == candidate) return;
    try evidence.append(allocator, candidate);
}

fn destroyItems(allocator: std.mem.Allocator, items: []WorkItem) void {
    for (items) |item| {
        allocator.free(item.consumers);
        allocator.free(item.evidence);
    }
}

test "proof work is grouped in canonical query order across consumer kinds" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const obligation_evidence = ir.EvidenceId.fromIndex(1);
    const evidence = [_]ir.Evidence{
        fixture.evidence[0],
        .{ .id = obligation_evidence, .kind = .frontend_proof, .locator = "fixture:obligation-provenance" },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = false } },
    };
    const queries = [_]ir.SolverQuery{
        .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(0) },
        .{ .id = ir.QueryId.fromIndex(1), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(1) },
    };
    const claims = [_]ir.Claim{
        .{
            .id = ir.ClaimId.fromIndex(0),
            .subject = .{ .program = {} },
            .predicate = ir.SolverTermId.fromIndex(1),
            .status = .unproven,
            .evidence = &.{fixture.proof},
            .query = ir.QueryId.fromIndex(1),
        },
        .{
            .id = ir.ClaimId.fromIndex(1),
            .subject = .{ .program = {} },
            .predicate = ir.SolverTermId.fromIndex(0),
            .status = .unproven,
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
        .detail = "shares the second query",
        .evidence = &.{obligation_evidence},
        .requirement = ir.ObligationRequirement.fromQuery(queries[1]),
        .query = ir.QueryId.fromIndex(1),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.evidence = &evidence;
    program.claims = &claims;
    program.obligations = &obligations;

    var plan = try Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqual(@as(usize, 2), plan.items.len);
    try std.testing.expectEqual(ir.QueryId.fromIndex(0), plan.items[0].query);
    try std.testing.expectEqual(ir.QueryId.fromIndex(1), plan.items[1].query);
    try std.testing.expectEqual(@as(usize, 1), plan.items[0].consumers.len);
    try std.testing.expectEqual(@as(usize, 2), plan.items[1].consumers.len);
    try std.testing.expect(plan.items[0].consumers[0] == .claim);
    try std.testing.expect(plan.items[1].consumers[0] == .claim);
    try std.testing.expect(plan.items[1].consumers[1] == .obligation);
    try std.testing.expectEqualSlices(ir.EvidenceId, &.{ fixture.proof, obligation_evidence }, plan.items[1].evidence);
}

test "proof planning rejects an obligation unrelated to its query" {
    const fixture = @import("fixtures.zig").arithmetic_module;
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
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .effect_proof,
        .subject = .{ .instruction = fixture.i_sum },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "constant truth does not prove instruction semantics",
        .evidence = &.{fixture.proof},
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.obligations = &obligations;

    try std.testing.expectError(error.InvalidObligationSubject, Plan.init(std.testing.allocator, &program));
}
