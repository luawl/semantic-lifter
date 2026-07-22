const std = @import("std");
const ir = @import("ir.zig");
const internal = @import("solver.zig");
const solver_preconditions = @import("solver_preconditions.zig");

pub const UnknownReason = enum {
    bounded_internal_incompleteness,
    timeout,
    resource_exhaustion,
    backend_indeterminacy,
    model_value_unrepresentability,
};

pub const Result = struct {
    engine: ir.SolverEngine,
    resolution: ir.SolverResolution,
    unknown_reason: ?UnknownReason = null,
    model: std.ArrayList(ir.SolverModelBinding) = .empty,
    unsat_core: std.ArrayList(ir.ConstraintId) = .empty,

    fn validateState(self: *const Result) !void {
        if (self.resolution == .unknown) {
            if (self.unknown_reason == null) return error.MissingUnknownReason;
            if (self.model.items.len != 0 or self.unsat_core.items.len != 0) return error.UnknownResultHasArtifact;
        } else if (self.unknown_reason != null) {
            return error.UnexpectedUnknownReason;
        }
    }

    pub fn deinit(self: *Result, allocator: std.mem.Allocator) void {
        for (self.model.items) |binding| switch (binding.value) {
            .boolean => {},
            .integer => |value| allocator.free(@constCast(value)),
            .real => |value| {
                allocator.free(@constCast(value.numerator));
                allocator.free(@constCast(value.denominator));
            },
            .bit_vector => |value| allocator.free(@constCast(value.value)),
            .dynamic_identity => {},
        };
        self.model.deinit(allocator);
        self.unsat_core.deinit(allocator);
    }
};

pub const SolveFn = *const fn (
    context: ?*anyopaque,
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    query: ir.SolverQuery,
) anyerror!Result;

pub const Backend = struct {
    engine: ir.SolverEngine,
    context: ?*anyopaque = null,
    solve_fn: SolveFn,

    pub fn solve(self: Backend, allocator: std.mem.Allocator, program: *const ir.Program, query: ir.SolverQuery) !Result {
        if (!solver_preconditions.queryCovered(program, query, internal.evaluatesTrue)) return error.MissingSolverPrecondition;
        var result = try self.solve_fn(self.context, allocator, program, query);
        errdefer result.deinit(allocator);
        if (result.engine != self.engine) return error.BackendIdentityMismatch;
        try result.validateState();
        return result;
    }
};

pub fn internalFacts() Backend {
    return .{
        .engine = .internal_facts,
        .solve_fn = solveInternal,
    };
}

fn solveInternal(_: ?*anyopaque, _: std.mem.Allocator, program: *const ir.Program, query: ir.SolverQuery) !Result {
    const resolution = internal.solve(program, query);
    return .{
        .engine = .internal_facts,
        .resolution = resolution,
        .unknown_reason = if (resolution == .unknown) .bounded_internal_incompleteness else null,
    };
}

test "backend interface preserves engine identity" {
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const program: ir.Program = .{
        .program_id = "backend-interface",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    };
    var result = try internalFacts().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try @import("std").testing.expectEqual(ir.SolverEngine.internal_facts, result.engine);
    try @import("std").testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try @import("std").testing.expectEqual(@as(?UnknownReason, null), result.unknown_reason);
}

test "internal backend types bounded incompleteness" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .semantic_atom = .{ .instruction_effects = fixture.i_sum } },
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    };

    var result = try internalFacts().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.unknown, result.resolution);
    try std.testing.expectEqual(UnknownReason.bounded_internal_incompleteness, result.unknown_reason.?);
}

test "backend result validation rejects inconsistent unknown states" {
    const missing_reason: Result = .{ .engine = .internal_facts, .resolution = .unknown };
    try std.testing.expectError(error.MissingUnknownReason, missing_reason.validateState());

    const known_with_reason: Result = .{
        .engine = .internal_facts,
        .resolution = .proved,
        .unknown_reason = .timeout,
    };
    try std.testing.expectError(error.UnexpectedUnknownReason, known_with_reason.validateState());

    var unknown_with_model: Result = .{
        .engine = .internal_facts,
        .resolution = .unknown,
        .unknown_reason = .bounded_internal_incompleteness,
    };
    defer unknown_with_model.deinit(std.testing.allocator);
    try unknown_with_model.model.append(std.testing.allocator, .{
        .term = ir.SolverTermId.fromIndex(0),
        .value = .{ .dynamic_identity = 0 },
    });
    try std.testing.expectError(error.UnknownResultHasArtifact, unknown_with_model.validateState());

    var unknown_with_core: Result = .{
        .engine = .internal_facts,
        .resolution = .unknown,
        .unknown_reason = .bounded_internal_incompleteness,
    };
    defer unknown_with_core.deinit(std.testing.allocator);
    try unknown_with_core.unsat_core.append(std.testing.allocator, ir.ConstraintId.fromIndex(0));
    try std.testing.expectError(error.UnknownResultHasArtifact, unknown_with_core.validateState());
}
