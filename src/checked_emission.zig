const std = @import("std");
const luau_compile_check = @import("luau_compile_check.zig");

pub const Outcome = union(enum) {
    published: void,
    staging_error: anyerror,
    compiler_process_error: anyerror,
    compiler_rejected: luau_compile_check.Result,
    compiler_terminated: luau_compile_check.Result,
    publication_error: anyerror,

    pub fn deinit(self: *Outcome) void {
        switch (self.*) {
            .compiler_rejected => |*result| result.deinit(),
            .compiler_terminated => |*result| result.deinit(),
            else => {},
        }
        self.* = undefined;
    }

    pub fn succeeded(self: Outcome) bool {
        return self == .published;
    }
};

const Runner = struct {
    context: ?*anyopaque = null,
    run_fn: *const fn (
        context: ?*anyopaque,
        allocator: std.mem.Allocator,
        io: std.Io,
        compiler_path: []const u8,
        source_path: []const u8,
        diagnostic_source_path: []const u8,
    ) anyerror!luau_compile_check.Result,

    fn run(
        self: Runner,
        allocator: std.mem.Allocator,
        io: std.Io,
        compiler_path: []const u8,
        source_path: []const u8,
        diagnostic_source_path: []const u8,
    ) !luau_compile_check.Result {
        return self.run_fn(self.context, allocator, io, compiler_path, source_path, diagnostic_source_path);
    }
};

pub fn publish(
    allocator: std.mem.Allocator,
    io: std.Io,
    output_path: []const u8,
    compiler_path: []const u8,
    source: []const u8,
) Outcome {
    return publishWithRunner(allocator, io, output_path, compiler_path, source, .{ .run_fn = runCompiler });
}

fn publishWithRunner(
    allocator: std.mem.Allocator,
    io: std.Io,
    output_path: []const u8,
    compiler_path: []const u8,
    source: []const u8,
    runner: Runner,
) Outcome {
    const staging_path = writeStagedFileAlloc(io, allocator, output_path, source) catch |err| {
        return .{ .staging_error = err };
    };
    defer allocator.free(staging_path);
    defer std.Io.Dir.cwd().deleteFile(io, staging_path) catch {};

    var result = runner.run(allocator, io, compiler_path, staging_path, output_path) catch |err| {
        return .{ .compiler_process_error = err };
    };
    switch (luau_compile_check.classifyTerm(result.term)) {
        .compiler_rejected => return .{ .compiler_rejected = result },
        .compiler_terminated => return .{ .compiler_terminated = result },
        .success => result.deinit(),
    }

    std.Io.Dir.cwd().rename(staging_path, std.Io.Dir.cwd(), output_path, io) catch |err| {
        return .{ .publication_error = err };
    };
    return .{ .published = {} };
}

fn runCompiler(
    _: ?*anyopaque,
    allocator: std.mem.Allocator,
    io: std.Io,
    compiler_path: []const u8,
    source_path: []const u8,
    diagnostic_source_path: []const u8,
) !luau_compile_check.Result {
    return luau_compile_check.run(allocator, io, compiler_path, source_path, diagnostic_source_path);
}

fn writeFileWithOptions(
    io: std.Io,
    path: []const u8,
    bytes: []const u8,
    options: std.Io.Dir.CreateFileOptions,
) !void {
    if (std.fs.path.dirname(path)) |directory| {
        _ = try std.Io.Dir.cwd().createDirPathStatus(io, directory, .default_dir);
    }
    const file = try std.Io.Dir.cwd().createFile(io, path, options);
    defer file.close(io);
    var buffer: [8192]u8 = undefined;
    var writer_state = file.writer(io, &buffer);
    const writer = &writer_state.interface;
    try writer.writeAll(bytes);
    try writer.flush();
}

fn stagingPathAlloc(io: std.Io, allocator: std.mem.Allocator, output_path: []const u8) ![]u8 {
    var nonce: [16]u8 = undefined;
    io.random(&nonce);
    const nonce_hex = std.fmt.bytesToHex(nonce, .lower);
    // Keep the staging file a normal Luau filename. Some Windows-hosted
    // compiler tools reject dot-prefixed paths even though the file exists.
    const basename = try std.fmt.allocPrint(allocator, "semantic-lifter-check-{s}.luau", .{&nonce_hex});
    defer allocator.free(basename);
    const directory = std.fs.path.dirname(output_path) orelse return allocator.dupe(u8, basename);
    return std.fs.path.join(allocator, &.{ directory, basename });
}

fn writeStagedFileAlloc(
    io: std.Io,
    allocator: std.mem.Allocator,
    output_path: []const u8,
    bytes: []const u8,
) ![]u8 {
    var attempt: usize = 0;
    while (attempt < 8) : (attempt += 1) {
        const staging_path = try stagingPathAlloc(io, allocator, output_path);
        writeFileWithOptions(io, staging_path, bytes, .{
            .truncate = false,
            .exclusive = true,
        }) catch |err| switch (err) {
            error.PathAlreadyExists => {
                allocator.free(staging_path);
                continue;
            },
            else => {
                allocator.free(staging_path);
                return err;
            },
        };
        return staging_path;
    }
    return error.StagingPathUnavailable;
}

fn fakeResult(
    allocator: std.mem.Allocator,
    term: std.process.Child.Term,
    stderr_text: []const u8,
) !luau_compile_check.Result {
    const stdout = try allocator.dupe(u8, "");
    errdefer allocator.free(stdout);
    return .{
        .allocator = allocator,
        .term = term,
        .stdout = stdout,
        .stderr = try allocator.dupe(u8, stderr_text),
    };
}

fn acceptCompiler(
    _: ?*anyopaque,
    allocator: std.mem.Allocator,
    _: std.Io,
    _: []const u8,
    _: []const u8,
    _: []const u8,
) !luau_compile_check.Result {
    return fakeResult(allocator, .{ .exited = 0 }, "");
}

fn rejectCompiler(
    _: ?*anyopaque,
    allocator: std.mem.Allocator,
    _: std.Io,
    _: []const u8,
    _: []const u8,
    _: []const u8,
) !luau_compile_check.Result {
    return fakeResult(allocator, .{ .exited = 1 }, "rejected");
}

fn unavailableCompiler(
    _: ?*anyopaque,
    _: std.mem.Allocator,
    _: std.Io,
    _: []const u8,
    _: []const u8,
    _: []const u8,
) !luau_compile_check.Result {
    return error.TestCompilerUnavailable;
}

fn terminateCompiler(
    _: ?*anyopaque,
    allocator: std.mem.Allocator,
    _: std.Io,
    _: []const u8,
    _: []const u8,
    _: []const u8,
) !luau_compile_check.Result {
    return fakeResult(allocator, .{ .signal = std.posix.SIG.TERM }, "terminated");
}

fn tempChildPathAlloc(allocator: std.mem.Allocator, temp: *const std.testing.TmpDir, child: []const u8) ![]u8 {
    return std.fs.path.join(allocator, &.{ ".zig-cache", "tmp", temp.sub_path[0..], child });
}

fn readTempOutputAlloc(allocator: std.mem.Allocator, temp: *const std.testing.TmpDir) ![]u8 {
    return temp.dir.readFileAlloc(std.testing.io, "checked.luau", allocator, .limited(1024));
}

fn expectNoStagedFiles(temp: *const std.testing.TmpDir) !void {
    var iterator = temp.dir.iterate();
    while (try iterator.next(std.testing.io)) |entry| {
        try std.testing.expect(!std.mem.startsWith(u8, entry.name, "semantic-lifter-check-"));
    }
}

test "checked publication is transactional across acceptance rejection and process failure" {
    const allocator = std.testing.allocator;
    var temp = std.testing.tmpDir(.{ .iterate = true });
    defer temp.cleanup();
    const output_path = try tempChildPathAlloc(allocator, &temp, "checked.luau");
    defer allocator.free(output_path);

    var accepted = publishWithRunner(allocator, std.testing.io, output_path, "fake", "accepted", .{ .run_fn = acceptCompiler });
    defer accepted.deinit();
    try std.testing.expect(accepted.succeeded());
    const accepted_source = try readTempOutputAlloc(allocator, &temp);
    defer allocator.free(accepted_source);
    try std.testing.expectEqualStrings("accepted", accepted_source);
    try expectNoStagedFiles(&temp);

    var rejected = publishWithRunner(allocator, std.testing.io, output_path, "fake", "rejected source", .{ .run_fn = rejectCompiler });
    defer rejected.deinit();
    try std.testing.expect(rejected == .compiler_rejected);
    try std.testing.expectEqualStrings("rejected", rejected.compiler_rejected.stderr);
    const preserved_after_rejection = try readTempOutputAlloc(allocator, &temp);
    defer allocator.free(preserved_after_rejection);
    try std.testing.expectEqualStrings("accepted", preserved_after_rejection);
    try expectNoStagedFiles(&temp);

    var unavailable = publishWithRunner(allocator, std.testing.io, output_path, "fake", "unavailable source", .{ .run_fn = unavailableCompiler });
    defer unavailable.deinit();
    try std.testing.expect(unavailable == .compiler_process_error);
    try std.testing.expectEqual(error.TestCompilerUnavailable, unavailable.compiler_process_error);
    const preserved_after_failure = try readTempOutputAlloc(allocator, &temp);
    defer allocator.free(preserved_after_failure);
    try std.testing.expectEqualStrings("accepted", preserved_after_failure);
    try expectNoStagedFiles(&temp);

    var terminated = publishWithRunner(allocator, std.testing.io, output_path, "fake", "terminated source", .{ .run_fn = terminateCompiler });
    defer terminated.deinit();
    try std.testing.expect(terminated == .compiler_terminated);
    try std.testing.expectEqualStrings("terminated", terminated.compiler_terminated.stderr);
    const preserved_after_termination = try readTempOutputAlloc(allocator, &temp);
    defer allocator.free(preserved_after_termination);
    try std.testing.expectEqualStrings("accepted", preserved_after_termination);
    try expectNoStagedFiles(&temp);
}

test "checked publication types staging and publication failures" {
    const allocator = std.testing.allocator;
    var temp = std.testing.tmpDir(.{ .iterate = true });
    defer temp.cleanup();

    const parent_file = try temp.dir.createFile(std.testing.io, "parent", .{});
    parent_file.close(std.testing.io);
    const blocked_path = try tempChildPathAlloc(allocator, &temp, "parent/checked.luau");
    defer allocator.free(blocked_path);
    var staging_failure = publishWithRunner(allocator, std.testing.io, blocked_path, "fake", "source", .{ .run_fn = acceptCompiler });
    defer staging_failure.deinit();
    try std.testing.expect(staging_failure == .staging_error);

    try temp.dir.createDir(std.testing.io, "destination.luau", .default_dir);
    const directory_path = try tempChildPathAlloc(allocator, &temp, "destination.luau");
    defer allocator.free(directory_path);
    var publication_failure = publishWithRunner(allocator, std.testing.io, directory_path, "fake", "source", .{ .run_fn = acceptCompiler });
    defer publication_failure.deinit();
    try std.testing.expect(publication_failure == .publication_error);
    try expectNoStagedFiles(&temp);
}
