const std = @import("std");
const ir = @import("ir.zig");
const cfg_edge = @import("cfg_edge.zig");
const control_flow = @import("control_flow.zig");
const forwarding_history_cut = @import("forwarding_history_cut.zig");
const loop_continue_shape = @import("loop_continue_shape.zig");
const structure = @import("structure.zig");
const emission_scope = @import("emit_luau_scope.zig");
const emission_planning = @import("emit_luau_plan.zig");
const branch_expression = @import("emit_luau_branch_expr.zig");

pub fn validatedStructuredEdgeAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    reference: ir.CfgEdgeRef,
    raw: ir.Edge,
    edge_override: ?structure.EdgeOverride,
    shared_reentry: ?loop_continue_shape.SharedPaths.EntryRef,
) (error{UnsupportedControlFlow} || std.mem.Allocator.Error)!ir.Edge {
    if (edge_override != null and shared_reentry != null) return error.UnsupportedControlFlow;
    if (shared_reentry) |entry_ref| return validateSharedEntryAlloc(allocator, program, reference, raw, entry_ref);
    const expected = edge_override orelse return raw;
    switch (expected) {
        .history_cut => |cut| {
            const replayed = try forwarding_history_cut.findAlloc(allocator, program, reference, cut.edge.target) orelse
                return error.UnsupportedControlFlow;
            if (replayed.prefix_len != cut.prefix_len or replayed.edge.target != cut.edge.target or
                !std.mem.eql(ir.ValueId, replayed.edge.arguments, cut.edge.arguments))
            {
                return error.UnsupportedControlFlow;
            }
            return cut.edge;
        },
        .forwarding => |forwarding| {
            var replayed = try control_flow.replayForwardingPathTo(
                allocator,
                program,
                raw,
                forwarding.edge.target,
            ) orelse return error.UnsupportedControlFlow;
            defer replayed.deinit(allocator);
            if (replayed.edge.target != forwarding.edge.target or
                !std.mem.eql(ir.ValueId, replayed.edge.arguments, forwarding.edge.arguments) or
                !std.mem.eql(ir.BlockId, replayed.blocks, forwarding.blocks))
            {
                return error.UnsupportedControlFlow;
            }
            return forwarding.edge;
        },
    }
}

pub fn validateSharedPathsAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    shared: *const loop_continue_shape.SharedPaths,
) (error{UnsupportedControlFlow} || std.mem.Allocator.Error)!void {
    if (shared.blocks.len == 0 or shared.entries.len < 2) return error.UnsupportedControlFlow;
    const used_blocks = try allocator.alloc(bool, shared.blocks.len);
    defer allocator.free(used_blocks);
    @memset(used_blocks, false);

    for (shared.blocks, 0..) |block_id, index| {
        if (block_id.index() >= program.blocks.len) return error.UnsupportedControlFlow;
        for (shared.blocks[0..index]) |previous| if (previous == block_id) return error.UnsupportedControlFlow;
    }
    for (shared.entries, 0..) |entry, index| {
        for (shared.entries[0..index]) |previous| {
            if (std.meta.eql(previous.reference, entry.reference)) return error.UnsupportedControlFlow;
        }
        const raw = cfg_edge.value(program, entry.reference) orelse return error.UnsupportedControlFlow;
        _ = try validateSharedEntryAlloc(
            allocator,
            program,
            entry.reference,
            raw,
            .{ .owner = shared, .index = @intCast(index) },
        );
        const route = shared.route(entry) orelse return error.UnsupportedControlFlow;
        for (route) |block_index| {
            if (block_index >= used_blocks.len) return error.UnsupportedControlFlow;
            used_blocks[block_index] = true;
        }
    }
    for (used_blocks) |used| if (!used) return error.UnsupportedControlFlow;
}

fn validateSharedEntryAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    reference: ir.CfgEdgeRef,
    raw: ir.Edge,
    entry_ref: loop_continue_shape.SharedPaths.EntryRef,
) (error{UnsupportedControlFlow} || std.mem.Allocator.Error)!ir.Edge {
    const entry = entry_ref.value() orelse return error.UnsupportedControlFlow;
    if (!std.meta.eql(entry.reference, reference) or entry.edge.target != entry_ref.owner.header) {
        return error.UnsupportedControlFlow;
    }
    if (cfg_edge.target(program, reference) != reference.target) return error.UnsupportedControlFlow;
    const current = cfg_edge.value(program, reference) orelse return error.UnsupportedControlFlow;
    if (current.target != raw.target or !std.mem.eql(ir.ValueId, current.arguments, raw.arguments)) {
        return error.UnsupportedControlFlow;
    }
    var replayed = try control_flow.replayForwardingPathTo(
        allocator,
        program,
        raw,
        entry_ref.owner.header,
    ) orelse return error.UnsupportedControlFlow;
    defer replayed.deinit(allocator);
    if (replayed.edge.target != entry.edge.target or
        !std.mem.eql(ir.ValueId, replayed.edge.arguments, entry.edge.arguments))
    {
        return error.UnsupportedControlFlow;
    }
    const route = entry_ref.owner.route(entry) orelse return error.UnsupportedControlFlow;
    if (route.len != replayed.blocks.len) return error.UnsupportedControlFlow;
    for (route, replayed.blocks) |block_index, block_id| {
        if (block_index >= entry_ref.owner.blocks.len or entry_ref.owner.blocks[block_index] != block_id) {
            return error.UnsupportedControlFlow;
        }
    }
    return entry.edge;
}

pub fn matchElseIf(
    program: *const ir.Program,
    emission_plan: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    edge: ir.Edge,
    region: *const structure.Region,
    join: ?ir.BlockId,
) ?structure.Branch {
    if (region.continue_projection != null) return null;
    const join_id = join orelse return null;
    if (region.stop == null or region.stop.? != join_id or region.nodes.len != 1) return null;
    if (edge.target.index() >= program.blocks.len or edge.arguments.len != 0 or program.blocks[edge.target.index()].parameters.len != 0) return null;

    const node = &region.nodes[0];
    const structured = switch (node.*) {
        .branch => |value| value,
        else => return null,
    };
    if (structured.then_edge_override != null or structured.else_edge_override != null or
        structured.then_shared_reentry != null or structured.else_shared_reentry != null) return null;
    if (structured.block != edge.target) return null;
    if (structured.join) |nested_join| {
        if (nested_join != join_id) return null;
    } else if (structured.then_region.stop == null or structured.then_region.stop.? != join_id or
        structured.else_region.stop == null or structured.else_region.stop.? != join_id)
    {
        return null;
    }
    const group = scopes.nodeContainerScope(node) orelse return null;
    const scope = scopes.nodeScope(node) orelse return null;
    if (scopes.declarationCount(group) != 0 or scopes.declarationCount(scope) != 0) return null;

    const block = program.blocks[structured.block.index()];
    const branch = switch (block.terminator) {
        .branch => |value| value,
        else => return null,
    };
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return null;
        const instruction = program.instructions[instruction_id.index()];
        if (emission_plan.instructionMayEmit(instruction) and !scopes.instructionIsMovedLiteralInitializer(instruction.id)) return null;
    }
    if (branch_expression.match(program, emission_plan, scopes, branch, structured) != null) return null;
    if (armIsStructurallyEmpty(program, branch.then_edge, structured.then_region, structured.join)) return null;
    return structured;
}

pub fn armIsStructurallyEmpty(
    program: *const ir.Program,
    edge: ir.Edge,
    region: *const structure.Region,
    join: ?ir.BlockId,
) bool {
    if (region.terminal_projection != null or region.continue_projection != null or region.escape_projection != null) return false;
    const boundary_id = join orelse region.stop orelse return false;
    if (boundary_id.index() >= program.blocks.len or edge.arguments.len != 0 or program.blocks[boundary_id.index()].parameters.len != 0) return false;
    var expected = edge.target;
    for (region.nodes) |node| {
        const block_id = switch (node) {
            .block => |value| value,
            else => return false,
        };
        if (block_id != expected or block_id.index() >= program.blocks.len) return false;
        const block = program.blocks[block_id.index()];
        if (block.parameters.len != 0 or block.instructions.len != 0) return false;
        const jump = switch (block.terminator) {
            .jump => |value| value,
            else => return false,
        };
        if (jump.arguments.len != 0) return false;
        expected = jump.target;
    }
    return expected == boundary_id;
}
