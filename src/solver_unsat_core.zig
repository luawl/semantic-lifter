const std = @import("std");
const ir = @import("ir.zig");
const solver = @import("solver.zig");
const solver_backend = @import("solver_backend.zig");
const solver_preconditions = @import("solver_preconditions.zig");

pub const Replay = union(enum) {
    satisfied,
    contradictory,
    unresolved: solver_backend.UnknownReason,
};

pub fn resolutionUsesCore(kind: ir.QueryKind, resolution: ir.SolverResolution) bool {
    return switch (resolution) {
        .unknown => false,
        .proved => kind != .find_model,
        .disproved => kind == .find_model,
    };
}

pub fn replayInternal(
    program: *const ir.Program,
    query: ir.SolverQuery,
    resolution: ir.SolverResolution,
    constraints: []const ir.ConstraintId,
) Replay {
    if (!resolutionUsesCore(query.kind, resolution)) return .contradictory;
    var restricted = query;
    restricted.assumptions = constraints;
    if (!solver_preconditions.queryCovered(program, restricted, solver.evaluatesTrue)) return .contradictory;
    const actual = solver.solve(program, restricted);
    if (actual == .unknown) return .{ .unresolved = .bounded_internal_incompleteness };
    return classifyKnown(actual, resolution);
}

pub fn replayBackendAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    query: ir.SolverQuery,
    resolution: ir.SolverResolution,
    constraints: []const ir.ConstraintId,
    backend: solver_backend.Backend,
) !Replay {
    if (!resolutionUsesCore(query.kind, resolution)) return .contradictory;
    var restricted = query;
    restricted.assumptions = constraints;
    var result = backend.solve(allocator, program, restricted) catch |err| switch (err) {
        error.MissingSolverPrecondition => return .contradictory,
        else => return err,
    };
    defer result.deinit(allocator);
    if (result.resolution == .unknown) return .{ .unresolved = result.unknown_reason.? };
    return classifyKnown(result.resolution, resolution);
}

pub fn ensureSufficientAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    query: ir.SolverQuery,
    backend: solver_backend.Backend,
    result: *solver_backend.Result,
) !?solver_backend.UnknownReason {
    if (!resolutionUsesCore(query.kind, result.resolution)) return null;
    const replay = switch (result.engine) {
        .internal_facts => replayInternal(program, query, result.resolution, result.unsat_core.items),
        .z3 => try replayBackendAlloc(allocator, program, query, result.resolution, result.unsat_core.items, backend),
        .imported => Replay{ .unresolved = .backend_indeterminacy },
    };
    const unresolved_reason: ?solver_backend.UnknownReason = switch (replay) {
        .satisfied => return null,
        .contradictory => null,
        .unresolved => |reason| reason,
    };

    // The full query was just solved by this backend, so its complete
    // assumption list is a deterministic sufficient core.
    result.unsat_core.clearRetainingCapacity();
    try result.unsat_core.appendSlice(allocator, query.assumptions);
    return unresolved_reason;
}

fn classifyKnown(actual: ir.SolverResolution, expected: ir.SolverResolution) Replay {
    std.debug.assert(actual != .unknown);
    return if (actual == expected) .satisfied else .contradictory;
}
