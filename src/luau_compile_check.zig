const std = @import("std");

pub const max_output_bytes: usize = 1024 * 1024;
pub const timeout_nanoseconds: u64 = 30 * std.time.ns_per_s;

pub const Result = struct {
    allocator: std.mem.Allocator,
    term: std.process.Child.Term,
    stdout: []u8,
    stderr: []u8,
    /// The optimisation level the compile ran at; a refusal of the publication gate names it.
    level: Level = .default,

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

/// The optimisation levels the publication gate compiles at: the compiler's default level, then -O0.
pub const Level = enum {
    default,
    O0,
};

/// The compiler argv for one level, held by value so the slice never outlives its array.
pub const GateArgv = struct {
    items: [4][]const u8,
    len: usize,

    pub fn slice(self: *const GateArgv) []const []const u8 {
        return self.items[0..self.len];
    }
};

pub fn gateArgv(compiler_path: []const u8, source_path: []const u8, level: Level) GateArgv {
    return switch (level) {
        .default => .{ .items = .{ compiler_path, "--null", source_path, "" }, .len = 3 },
        .O0 => .{ .items = .{ compiler_path, "--null", "-O0", source_path }, .len = 4 },
    };
}

pub fn run(
    allocator: std.mem.Allocator,
    io: std.Io,
    compiler_path: []const u8,
    source_path: []const u8,
    diagnostic_source_path: []const u8,
    level: Level,
) !Result {
    const argv = gateArgv(compiler_path, source_path, level);
    const process_result = try std.process.run(allocator, io, .{
        .argv = argv.slice(),
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
        .level = level,
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

test "the gate argv names the optimisation level" {
    const default_argv = gateArgv("luau-compile", "staged.luau", .default);
    const default_items = default_argv.slice();
    try std.testing.expectEqual(@as(usize, 3), default_items.len);
    try std.testing.expectEqualStrings("luau-compile", default_items[0]);
    try std.testing.expectEqualStrings("--null", default_items[1]);
    try std.testing.expectEqualStrings("staged.luau", default_items[2]);

    const o0_argv = gateArgv("luau-compile", "staged.luau", .O0);
    const o0_items = o0_argv.slice();
    try std.testing.expectEqual(@as(usize, 4), o0_items.len);
    try std.testing.expectEqualStrings("luau-compile", o0_items[0]);
    try std.testing.expectEqualStrings("--null", o0_items[1]);
    try std.testing.expectEqualStrings("-O0", o0_items[2]);
    try std.testing.expectEqualStrings("staged.luau", o0_items[3]);
}
