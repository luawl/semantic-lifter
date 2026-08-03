const std = @import("std");

pub const max_output_bytes: usize = 1024 * 1024;
pub const timeout_nanoseconds: u64 = 30 * std.time.ns_per_s;

pub const Result = struct {
    allocator: std.mem.Allocator,
    term: std.process.Child.Term,
    stdout: []u8,
    stderr: []u8,

    pub fn deinit(self: *Result) void {
        self.allocator.free(self.stderr);
        self.allocator.free(self.stdout);
        self.* = undefined;
    }

    pub fn succeeded(self: Result) bool {
        return classifyTerm(self.term) == .success;
    }
};

pub const Termination = enum {
    success,
    compiler_rejected,
    compiler_terminated,
};

pub fn run(
    allocator: std.mem.Allocator,
    io: std.Io,
    compiler_path: []const u8,
    source_path: []const u8,
    diagnostic_source_path: []const u8,
) !Result {
    const process_result = try std.process.run(allocator, io, .{
        .argv = &.{ compiler_path, "--null", source_path },
        .stdout_limit = .limited(max_output_bytes),
        .stderr_limit = .limited(max_output_bytes),
        .timeout = .{ .duration = .{
            .clock = .awake,
            .raw = .fromNanoseconds(timeout_nanoseconds),
        } },
    });
    defer allocator.free(process_result.stderr);
    defer allocator.free(process_result.stdout);
    const stdout = try normalizeSourcePathAlloc(allocator, process_result.stdout, source_path, diagnostic_source_path);
    errdefer allocator.free(stdout);
    const stderr = try normalizeSourcePathAlloc(allocator, process_result.stderr, source_path, diagnostic_source_path);
    return .{
        .allocator = allocator,
        .term = process_result.term,
        .stdout = stdout,
        .stderr = stderr,
    };
}

fn normalizeSourcePathAlloc(
    allocator: std.mem.Allocator,
    output: []const u8,
    source_path: []const u8,
    diagnostic_source_path: []const u8,
) std.mem.Allocator.Error![]u8 {
    const full_path = try std.mem.replaceOwned(u8, allocator, output, source_path, diagnostic_source_path);
    defer allocator.free(full_path);
    return std.mem.replaceOwned(
        u8,
        allocator,
        full_path,
        std.fs.path.basename(source_path),
        std.fs.path.basename(diagnostic_source_path),
    );
}

pub fn classifyTerm(term: std.process.Child.Term) Termination {
    return switch (term) {
        .exited => |code| if (code == 0) .success else .compiler_rejected,
        .signal, .stopped, .unknown => .compiler_terminated,
    };
}

test "compile checking classifies process termination" {
    try std.testing.expectEqual(Termination.success, classifyTerm(.{ .exited = 0 }));
    try std.testing.expectEqual(Termination.compiler_rejected, classifyTerm(.{ .exited = 1 }));
    try std.testing.expectEqual(Termination.compiler_terminated, classifyTerm(.{ .signal = std.posix.SIG.TERM }));
    try std.testing.expectEqual(Termination.compiler_terminated, classifyTerm(.{ .stopped = std.posix.SIG.TERM }));
    try std.testing.expectEqual(Termination.compiler_terminated, classifyTerm(.{ .unknown = 1 }));
}

test "compile checking normalizes staged source paths in diagnostics" {
    const allocator = std.testing.allocator;
    const staged_name = ".semantic-lifter-check-0123456789abcdef.luau";
    const staged_path = try std.fs.path.join(allocator, &.{ "testdata", staged_name });
    defer allocator.free(staged_path);
    const output_path = try std.fs.path.join(allocator, &.{ "testdata", "readable.luau" });
    defer allocator.free(output_path);
    const compiler_output = try std.fmt.allocPrint(
        allocator,
        "exact={s}:1\nbasename={s}:2\n",
        .{ staged_path, staged_name },
    );
    defer allocator.free(compiler_output);
    const expected = try std.fmt.allocPrint(
        allocator,
        "exact={s}:1\nbasename=readable.luau:2\n",
        .{output_path},
    );
    defer allocator.free(expected);

    const normalized = try normalizeSourcePathAlloc(allocator, compiler_output, staged_path, output_path);
    defer allocator.free(normalized);
    try std.testing.expectEqualStrings(expected, normalized);
}
