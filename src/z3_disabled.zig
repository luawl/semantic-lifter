const backend = @import("solver_backend.zig");

pub const enabled = false;

pub const Options = struct {
    timeout_ms: u32 = 5000,
    resource_limit: u32 = 0,
};

const default_options: Options = .{};

pub fn solverBackend(_: *const Options) backend.Backend {
    return .{
        .engine = .z3,
        .solve_fn = solveDisabled,
    };
}

pub fn defaultBackend() backend.Backend {
    return solverBackend(&default_options);
}

fn solveDisabled(_: ?*anyopaque, _: @import("std").mem.Allocator, _: *const @import("ir.zig").Program, _: @import("ir.zig").SolverQuery) !backend.Result {
    return error.Z3Disabled;
}

test "disabled backend remains an explicit optional boundary" {
    try @import("std").testing.expect(!enabled);
    const options: Options = .{ .timeout_ms = 0, .resource_limit = 1 };
    const selected = solverBackend(&options);
    try @import("std").testing.expectEqual(@import("ir.zig").SolverEngine.z3, selected.engine);
}
