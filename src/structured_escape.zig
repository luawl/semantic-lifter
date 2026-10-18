const std = @import("std");
const ir = @import("ir.zig");
const structure = @import("structure.zig");

pub fn regionOwnsEscape(region: *const structure.Region) bool {
    return structure.regionOwnsEscape(region);
}

pub fn regionHasNestedEscapeTo(region: *const structure.Region, target: ir.BlockId) bool {
    return structure.regionHasNestedEscapeTo(region, target);
}

pub fn regionHasLoopBoundaryExitTo(region: *const structure.Region, target: ir.BlockId) bool {
    return structure.regionHasLoopBoundaryExitTo(region, target);
}

pub fn regionHasLoopBoundaryContinueNotTo(region: *const structure.Region, stop: ir.BlockId) bool {
    return structure.regionHasLoopBoundaryContinueNotTo(region, stop);
}

pub fn regionHasUnflaggedLoopExitBreak(program: *const ir.Program, region: *const structure.Region) bool {
    return structure.regionHasUnflaggedLoopExitBreak(program, region);
}

pub fn loopBoundaryExitTargetsAlloc(
    allocator: std.mem.Allocator,
    region: *const structure.Region,
) std.mem.Allocator.Error![]ir.BlockId {
    return structure.loopBoundaryExitTargetsAlloc(allocator, region);
}

pub fn regionNeedsTransferWrapper(
    allocator: std.mem.Allocator,
    region: *const structure.Region,
) std.mem.Allocator.Error!bool {
    if (region.stop == null) return false;
    const targets = try structure.regionFreeTargetsAlloc(allocator, region);
    defer allocator.free(targets);
    return targets.len != 0;
}

pub fn regionFreeTargetsAlloc(
    allocator: std.mem.Allocator,
    region: *const structure.Region,
) std.mem.Allocator.Error![]ir.BlockId {
    return structure.regionFreeTargetsAlloc(allocator, region);
}

pub fn loopFreeTargetsAlloc(
    allocator: std.mem.Allocator,
    node: structure.Node,
) std.mem.Allocator.Error![]ir.BlockId {
    return structure.loopFreeTargetsAlloc(allocator, node);
}

pub fn maxOwnedDepth(region: *const structure.Region) usize {
    return maxRegionDepth(region, 0);
}

fn maxRegionDepth(region: *const structure.Region, depth: usize) usize {
    const nested_depth = depth + @intFromBool(regionOwnsEscape(region));
    var maximum = nested_depth;
    for (region.nodes) |node| maximum = @max(maximum, maxNodeDepth(node, nested_depth));
    return maximum;
}

fn maxNodeDepth(node: structure.Node, depth: usize) usize {
    return switch (node) {
        .block, .loop_control, .loop_terminal => depth,
        .branch => |branch| @max(
            maxRegionDepth(branch.then_region, depth),
            maxRegionDepth(branch.else_region, depth),
        ),
        .loop => |loop| maxRegionDepth(loop.body_region, depth),
        .latch_loop => |loop| maxRegionDepth(loop.body_region, depth),
        .infinite_loop => |loop| @max(
            maxRegionDepth(loop.body_region, depth),
            if (loop.shared_side_exit) |side_exit| maxSharedSideExitDepth(side_exit, depth + 1) else depth,
        ),
        .loop_boundary => |control| maximum: {
            var value = maxRegionDepth(control.body_region, depth);
            if (control.boundary == .side_exit) {
                value = @max(value, maxRegionDepth(control.boundary.side_exit.region, depth));
            } else if (control.boundary == .side_escape) {
                value = @max(value, maxRegionDepth(control.boundary.side_escape.region, depth));
            }
            break :maximum value;
        },
    };
}

fn maxSharedSideExitDepth(side_exit: structure.SharedSideExit, depth: usize) usize {
    var value = depth;
    for (side_exit.entries) |entry| value = @max(value, maxRegionDepth(entry.region, depth));
    return value;
}
