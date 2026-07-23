const std = @import("std");
const ir = @import("ir.zig");
const solver = @import("solver.zig");
const solver_promotion = @import("solver_promotion.zig");
const solver_preconditions = @import("solver_preconditions.zig");
const solver_term = @import("solver_term.zig");

pub const Result = struct {
    promoted_queries: usize = 0,
    appended_terms: usize = 0,
};

pub fn promoteUnresolvedQueries(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    queries: *std.ArrayList(ir.SolverQuery),
    claims: *std.ArrayList(ir.Claim),
    obligations: *std.ArrayList(ir.Obligation),
) std.mem.Allocator.Error!Result {
    var result: Result = .{};
    var working = program.*;
    working.solver_terms = terms.items;
    working.queries = queries.items;
    working.claims = claims.items;
    working.obligations = obligations.items;

    const query_count = queries.items.len;
    for (0..query_count) |query_index| {
        const query_id = ir.QueryId.fromIndex(query_index);
        if (!queryCanBePromoted(program, query_id, queries.items, claims.items, obligations.items)) continue;

        const initial_term_count = terms.items.len;
        const memo = try allocator.alloc(?ir.SolverTermId, initial_term_count);
        defer allocator.free(memo);
        @memset(memo, null);
        var promoter: Promoter = .{
            .allocator = allocator,
            .program = &working,
            .terms = terms,
            .memo = memo,
            .base_term_count = initial_term_count,
        };
        const original_goal = queries.items[query_index].goal;
        const promoted_goal = (try promoter.promote(original_goal, 0)) orelse {
            terms.items = terms.items[0..initial_term_count];
            working.solver_terms = terms.items;
            continue;
        };
        working.solver_terms = terms.items;
        if (promoted_goal == original_goal) {
            terms.items = terms.items[0..initial_term_count];
            working.solver_terms = terms.items;
            continue;
        }

        var candidate = queries.items[query_index];
        candidate.goal = promoted_goal;
        if (!solver_preconditions.queryCovered(&working, candidate, solver.evaluatesTrue)) {
            terms.items = terms.items[0..initial_term_count];
            working.solver_terms = terms.items;
            continue;
        }

        queries.items[query_index].goal = promoted_goal;
        for (claims.items) |*claim| {
            if (claim.query != null and claim.query.? == query_id) claim.predicate = promoted_goal;
        }
        for (obligations.items) |*obligation| {
            if (obligation.query != null and obligation.query.? == query_id) {
                obligation.requirement.?.predicate = promoted_goal;
            }
        }
        working.queries = queries.items;
        working.claims = claims.items;
        working.obligations = obligations.items;
        result.promoted_queries += 1;
        result.appended_terms += terms.items.len - initial_term_count;
    }
    return result;
}

const Promoter = struct {
    allocator: std.mem.Allocator,
    program: *ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    memo: []?ir.SolverTermId,
    base_term_count: usize,

    fn promote(self: *Promoter, term_id: ir.SolverTermId, depth: usize) std.mem.Allocator.Error!?ir.SolverTermId {
        if (term_id.index() >= self.base_term_count or depth > self.base_term_count) return null;
        if (self.memo[term_id.index()]) |known| return known;
        const term = self.program.solver_terms[term_id.index()];
        if (term.operation == .value_definition) {
            self.memo[term_id.index()] = term_id;
            return term_id;
        }
        if (term.operation == .value) {
            const promoted = try solver_promotion.ensureDefinition(
                self.allocator,
                self.program,
                self.terms,
                term.operation.value,
            );
            self.program.solver_terms = self.terms.items;
            const resolved = promoted orelse term_id;
            self.memo[term_id.index()] = resolved;
            return resolved;
        }

        var mapped: [solver_term.max_dependencies]ir.SolverTermId = undefined;
        var count: usize = 0;
        var changed = false;
        var dependencies = solver_term.dependencies(term.operation);
        while (dependencies.next()) |dependency| {
            if (count >= mapped.len) return null;
            const promoted = (try self.promote(dependency, depth + 1)) orelse return null;
            mapped[count] = promoted;
            changed = changed or promoted != dependency;
            count += 1;
        }
        if (!changed) {
            self.memo[term_id.index()] = term_id;
            return term_id;
        }
        const operation = solver_term.remapDependencies(term.operation, mapped[0..count]) orelse return null;
        const promoted = try solver_promotion.ensureCanonicalTerm(self.allocator, self.terms, term.sort, operation);
        self.program.solver_terms = self.terms.items;
        self.memo[term_id.index()] = promoted;
        return promoted;
    }
};

fn queryCanBePromoted(
    program: *const ir.Program,
    query_id: ir.QueryId,
    queries: []const ir.SolverQuery,
    claims: []const ir.Claim,
    obligations: []const ir.Obligation,
) bool {
    if (query_id.index() >= queries.len or queries[query_id.index()].id != query_id) return false;
    const query = queries[query_id.index()];
    for (program.certificates) |certificate| if (certificate.query == query_id) return false;
    for (program.solver_models) |model| if (model.query == query_id) return false;
    for (program.unsat_cores) |core| if (core.query == query_id) return false;

    var has_consumer = false;
    for (claims) |claim| {
        if (claim.query == null or claim.query.? != query_id) continue;
        has_consumer = true;
        if (claim.status != .unproven or
            claim.certificate != null or
            claim.predicate != query.goal or
            (query.kind != .prove_true and query.kind != .prove_equivalent)) return false;
    }
    for (obligations) |obligation| {
        if (obligation.query == null or obligation.query.? != query_id) continue;
        has_consumer = true;
        const requirement = obligation.requirement orelse return false;
        if (obligation.status != .open or
            obligation.certificate != null or
            requirement.kind != query.kind or
            requirement.predicate != query.goal) return false;
    }
    return has_consumer;
}

test "nested unresolved query goals promote value leaves" {
    const fixture = @import("fixtures.zig").automatic_promotion_module;
    const terms_seed = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .value = fixture.v_condition } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const queries_seed = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(2),
    }};
    const claims_seed = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(2),
        .status = .unproven,
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms_seed;
    program.queries = &queries_seed;
    program.claims = &claims_seed;
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(std.testing.allocator);
    try terms.appendSlice(std.testing.allocator, &terms_seed);
    var queries: std.ArrayList(ir.SolverQuery) = .empty;
    defer queries.deinit(std.testing.allocator);
    try queries.appendSlice(std.testing.allocator, &queries_seed);
    var claims: std.ArrayList(ir.Claim) = .empty;
    defer claims.deinit(std.testing.allocator);
    try claims.appendSlice(std.testing.allocator, &claims_seed);
    var obligations: std.ArrayList(ir.Obligation) = .empty;
    defer obligations.deinit(std.testing.allocator);

    const result = try promoteUnresolvedQueries(
        std.testing.allocator,
        &program,
        &terms,
        &queries,
        &claims,
        &obligations,
    );
    try std.testing.expectEqual(@as(usize, 1), result.promoted_queries);
    try std.testing.expect(queries.items[0].goal != queries_seed[0].goal);
    try std.testing.expectEqual(queries.items[0].goal, claims.items[0].predicate);
    const promoted_goal = terms.items[queries.items[0].goal.index()].operation.binary;
    try std.testing.expect(terms.items[promoted_goal.left.index()].operation == .value_definition);
    var resolved = program;
    resolved.solver_terms = terms.items;
    resolved.queries = queries.items;
    resolved.claims = claims.items;
    try std.testing.expectEqual(ir.SolverResolution.proved, solver.solve(&resolved, resolved.queries[0]));
}

test "missing promoted preconditions roll back the entire query" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };
    const bv32: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 32 };
    var values = fixture.values;
    values[fixture.v_right.index()].type = u32_type;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_factor.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .shift_left,
        .left = fixture.v_sum,
        .right = fixture.v_right,
        .mode = .primitive,
        .shift_behavior = .luau_bit32,
    } };
    const terms_seed = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv32, .operation = .{ .value = fixture.v_result } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv32, .operation = .{ .bit_vector_literal = .{ .value = "0", .bit_width = 32 } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const queries_seed = [_]ir.SolverQuery{.{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) }};
    const claims_seed = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(2),
        .status = .unproven,
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms_seed;
    program.queries = &queries_seed;
    program.claims = &claims_seed;
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(std.testing.allocator);
    try terms.appendSlice(std.testing.allocator, &terms_seed);
    var queries: std.ArrayList(ir.SolverQuery) = .empty;
    defer queries.deinit(std.testing.allocator);
    try queries.appendSlice(std.testing.allocator, &queries_seed);
    var claims: std.ArrayList(ir.Claim) = .empty;
    defer claims.deinit(std.testing.allocator);
    try claims.appendSlice(std.testing.allocator, &claims_seed);
    var obligations: std.ArrayList(ir.Obligation) = .empty;
    defer obligations.deinit(std.testing.allocator);

    const result = try promoteUnresolvedQueries(std.testing.allocator, &program, &terms, &queries, &claims, &obligations);
    try std.testing.expectEqual(@as(usize, 0), result.promoted_queries);
    try std.testing.expectEqual(@as(usize, terms_seed.len), terms.items.len);
    try std.testing.expectEqual(queries_seed[0].goal, queries.items[0].goal);
    try std.testing.expectEqual(claims_seed[0].predicate, claims.items[0].predicate);
}

test "promotion does not repair a mismatched claim predicate" {
    const fixture = @import("fixtures.zig").automatic_promotion_module;
    const terms_seed = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .value = fixture.v_condition } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = false } },
    };
    const queries_seed = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(2),
    }};
    const claims_seed = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(3),
        .status = .unproven,
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms_seed;
    program.queries = &queries_seed;
    program.claims = &claims_seed;
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(std.testing.allocator);
    try terms.appendSlice(std.testing.allocator, &terms_seed);
    var queries: std.ArrayList(ir.SolverQuery) = .empty;
    defer queries.deinit(std.testing.allocator);
    try queries.appendSlice(std.testing.allocator, &queries_seed);
    var claims: std.ArrayList(ir.Claim) = .empty;
    defer claims.deinit(std.testing.allocator);
    try claims.appendSlice(std.testing.allocator, &claims_seed);
    var obligations: std.ArrayList(ir.Obligation) = .empty;
    defer obligations.deinit(std.testing.allocator);

    const result = try promoteUnresolvedQueries(std.testing.allocator, &program, &terms, &queries, &claims, &obligations);
    try std.testing.expectEqual(@as(usize, 0), result.promoted_queries);
    try std.testing.expectEqual(@as(usize, terms_seed.len), terms.items.len);
    try std.testing.expectEqual(queries_seed[0].goal, queries.items[0].goal);
    try std.testing.expectEqual(claims_seed[0].predicate, claims.items[0].predicate);
}

test "materialized queries and their digest closure remain unchanged" {
    const fixture = @import("fixtures.zig").automatic_promotion_module;
    const terms_seed = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .value = fixture.v_condition } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const queries_seed = [_]ir.SolverQuery{
        .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) },
        .{ .id = ir.QueryId.fromIndex(1), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) },
    };
    const certificate: ir.SolverCertificate = .{
        .id = ir.CertificateId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .engine = .imported,
        .resolution = .proved,
        .evidence = &.{fixture.proof},
        .certificate_digest = "fixture:materialized-query",
    };
    const claims_seed = [_]ir.Claim{
        .{ .id = ir.ClaimId.fromIndex(0), .subject = .{ .program = {} }, .predicate = ir.SolverTermId.fromIndex(2), .status = .proved, .evidence = &.{fixture.proof}, .query = ir.QueryId.fromIndex(0), .certificate = certificate.id },
        .{ .id = ir.ClaimId.fromIndex(1), .subject = .{ .program = {} }, .predicate = ir.SolverTermId.fromIndex(2), .status = .unproven, .query = ir.QueryId.fromIndex(1) },
    };
    var program = fixture.program;
    program.solver_terms = &terms_seed;
    program.queries = &queries_seed;
    program.certificates = &.{certificate};
    program.claims = &claims_seed;
    const proof_digest = @import("proof_digest.zig");
    const before = try proof_digest.computeAlloc(
        std.testing.allocator,
        &program,
        queries_seed[0],
        .imported,
        .proved,
        &.{fixture.proof},
        &.{},
        &.{},
    );
    defer std.testing.allocator.free(before);
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(std.testing.allocator);
    try terms.appendSlice(std.testing.allocator, &terms_seed);
    var queries: std.ArrayList(ir.SolverQuery) = .empty;
    defer queries.deinit(std.testing.allocator);
    try queries.appendSlice(std.testing.allocator, &queries_seed);
    var claims: std.ArrayList(ir.Claim) = .empty;
    defer claims.deinit(std.testing.allocator);
    try claims.appendSlice(std.testing.allocator, &claims_seed);
    var obligations: std.ArrayList(ir.Obligation) = .empty;
    defer obligations.deinit(std.testing.allocator);

    const result = try promoteUnresolvedQueries(std.testing.allocator, &program, &terms, &queries, &claims, &obligations);
    try std.testing.expectEqual(@as(usize, 1), result.promoted_queries);
    try std.testing.expectEqual(queries_seed[0].goal, queries.items[0].goal);
    try std.testing.expect(queries_seed[1].goal != queries.items[1].goal);
    var resolved = program;
    resolved.solver_terms = terms.items;
    resolved.queries = queries.items;
    resolved.claims = claims.items;
    const after = try proof_digest.computeAlloc(
        std.testing.allocator,
        &resolved,
        resolved.queries[0],
        .imported,
        .proved,
        &.{fixture.proof},
        &.{},
        &.{},
    );
    defer std.testing.allocator.free(after);
    try std.testing.expectEqualStrings(before, after);
}
