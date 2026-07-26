const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const loop_continue_shape = @import("loop_continue_shape.zig");
const loop_exit_shape = @import("loop_exit_shape.zig");
const natural_loop = @import("natural_loop.zig");

pub fn collectSupportedPostTestedLoop(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    header: ir.BlockId,
    return_block: ir.BlockId,
) std.mem.Allocator.Error!?natural_loop.Membership {
    var membership = natural_loop.collect(allocator, analysis, header) catch |err| switch (err) {
        error.UnsupportedShape => return null,
        error.OutOfMemory => return error.OutOfMemory,
    } orelse return null;
    var accepted = false;
    defer if (!accepted) membership.deinit();

    const shape = natural_loop.classifyPostTested(analysis, header, membership.bits) catch |err| switch (err) {
        error.UnsupportedShape => return null,
        error.OutOfMemory => return error.OutOfMemory,
    } orelse return null;
    if (shape.latch_count == 0 or shape.exit != return_block) return null;
    var exit_latches = natural_loop.collectExitLatches(
        allocator,
        analysis,
        header,
        membership.bits,
        shape.exit,
    ) catch |err| switch (err) {
        error.UnsupportedShape => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer exit_latches.deinit();
    if (exit_latches.count != shape.latch_count) return null;
    const shared_exit_paths = loop_exit_shape.auditSharedAlloc(
        allocator,
        analysis,
        header,
        membership.bits,
        exit_latches.bits,
        shape.exit,
    ) catch |err| switch (err) {
        error.UnsupportedShape => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer if (shared_exit_paths) |paths| paths.deinit(allocator);
    if (shape.has_non_latch_backedge) {
        const shared_paths = loop_continue_shape.auditAlloc(
            allocator,
            analysis,
            header,
            membership.bits,
            exit_latches.bits,
        ) catch |err| switch (err) {
            error.UnsupportedShape => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer if (shared_paths) |paths| paths.deinit(allocator);
    }

    switch (natural_loop.classifyExit(analysis, membership.bits) catch |err| switch (err) {
        error.UnsupportedShape => return null,
        error.OutOfMemory => return error.OutOfMemory,
    }) {
        .unique => |exit| if (exit != return_block) return null,
        .closed, .multiple => return null,
    }

    accepted = true;
    return membership;
}
