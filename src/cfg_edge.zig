const ir = @import("ir.zig");

pub fn target(program: *const ir.Program, edge: ir.CfgEdgeRef) ?ir.BlockId {
    const current = value(program, edge) orelse return null;
    return if (current.target == edge.target) edge.target else null;
}

pub fn value(program: *const ir.Program, edge: ir.CfgEdgeRef) ?ir.Edge {
    if (edge.source.index() >= program.blocks.len) return null;
    return switch (program.blocks[edge.source.index()].terminator) {
        .jump => |jump_edge| if (edge.kind == .jump) jump_edge else null,
        .branch => |branch| switch (edge.kind) {
            .branch_then => branch.then_edge,
            .branch_else => branch.else_edge,
            .jump => null,
        },
        else => null,
    };
}

pub fn isValid(program: *const ir.Program, edge: ir.CfgEdgeRef) bool {
    return edge.target.index() < program.blocks.len and value(program, edge) != null;
}

pub fn isCurrent(program: *const ir.Program, edge: ir.CfgEdgeRef) bool {
    return target(program, edge) != null;
}

test "edge references distinguish branch arms and reject mismatched kinds" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    try @import("std").testing.expectEqual(
        fixture.b_negative,
        target(&fixture.program, .{ .source = fixture.b_entry, .kind = .branch_then, .target = fixture.b_negative }).?,
    );
    try @import("std").testing.expectEqual(
        fixture.b_nonnegative,
        target(&fixture.program, .{ .source = fixture.b_entry, .kind = .branch_else, .target = fixture.b_nonnegative }).?,
    );
    try @import("std").testing.expect(target(&fixture.program, .{ .source = fixture.b_entry, .kind = .jump, .target = fixture.b_negative }) == null);
}
