const std = @import("std");
const ir = @import("ir.zig");
const structure = @import("structure.zig");

pub fn regionOwnsEscape(region: *const structure.Region) bool {
    return structure.regionOwnsEscape(region);
}

pub fn regionWritesOwnedEscape(region: *const structure.Region) bool {
    return structure.regionWritesOwnedEscape(region);
}

pub fn regionSideEscapeFallsThrough(region: *const structure.Region) bool {
    return structure.regionSideEscapeFallsThrough(region);
}

pub fn regionIsWrapped(allocator: std.mem.Allocator, region: *const structure.Region) std.mem.Allocator.Error!bool {
    return structure.regionIsWrapped(allocator, region);
}

pub fn regionHasNestedEscapeTo(region: *const structure.Region, target: ir.BlockId) bool {
    return structure.regionHasNestedEscapeTo(region, target);
}

pub fn loopOwnedExitFlag(holding_region: *const structure.Region, node: structure.Node) ?ir.BlockId {
    return structure.loopOwnedExitFlag(holding_region, node);
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

pub fn joinlessBranchArmLeavesPastStop(program: *const ir.Program, holder: *const structure.Region, branch: structure.Branch) bool {
    return structure.joinlessBranchArmLeavesPastStop(program, holder, branch);
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
    // An infinite loop with a shared side exit declares one flag per entry before its `while true do`, at this
    // region's level (`emitInfiniteLoop`): each is a register through the loop's body, its side regions and the
    // region's later nodes, whatever flag of the same name a region in the body declares again.
    var side_flags: usize = 0;
    // A loop that declares its owned exit's flag at the top of each pass holds one more flag through its body.
    for (region.nodes) |node| {
        side_flags += sharedSideFlagCount(node);
        maximum = @max(maximum, maxNodeDepth(node, nested_depth + side_flags + @intFromBool(loopOwnedExitFlag(region, node) != null)));
    }
    return maximum;
}

fn sharedSideFlagCount(node: structure.Node) usize {
    return switch (node) {
        .infinite_loop => |loop| if (loop.shared_side_exit) |side_exit| side_exit.entries.len else 0,
        else => 0,
    };
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
        // `depth` already holds the loop's side-exit flags (`maxRegionDepth`).
        .infinite_loop => |loop| @max(
            maxRegionDepth(loop.body_region, depth),
            if (loop.shared_side_exit) |side_exit| maxSharedSideExitDepth(side_exit, depth) else depth,
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
