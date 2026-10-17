const std = @import("std");
const diagnostics = @import("diagnostics.zig");
const emission_planning = @import("emit_luau_plan.zig");
const ir = @import("ir.zig");
const luau_runtime = @import("luau_runtime.zig");
const readable_scope = @import("readable_scope.zig");
const runtime_uses = @import("runtime_uses.zig");
const structure = @import("structure.zig");

pub fn validate(
    report: *diagnostics.Report,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
    function: ir.Function,
    structured: *const structure.Plan,
) std.mem.Allocator.Error!void {
    if (!regionHasEncodedJump(program, emission, structured.root)) return;
    if (emissionUnitCount(program, readable, emission, function) > luau_runtime.max_jump_emission_units) {
        try report.add(.unsupported_readable_jump_distance, function.id.index());
    }
}

/// A unit covers at most eight words under the pinned O1 lowering. Fixed
/// entity units cover declarations, instructions, terminators, and control;
/// use units cover moves, auxiliary operands, captures, fields, and packs.
pub fn emissionUnitCount(
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
    function: ir.Function,
) usize {
    var units: usize = 16;
    add(&units, function.parameters.len);
    add(&units, function.captures.len);
    add(&units, function.local_places.len);
    add(&units, @intFromBool(function.is_variadic));

    if (function.id == program.entry_function) {
        addProduct(&units, program.external_bindings.len, 2);
        addProduct(&units, program.entry_bindings.len, 2);
        for (emission.runtime.required.flags) |required| {
            if (required) add(&units, 2);
        }
        for (program.functions) |candidate| {
            if (candidate.id != program.entry_function and candidate.lexical_parent == null) add(&units, 2);
        }
    }

    for (function.blocks) |block_id| {
        if (block_id.index() >= program.blocks.len or !readable.block(block_id)) continue;
        const block = program.blocks[block_id.index()];
        add(&units, 1);
        add(&units, block.parameters.len);

        for (block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len or !readable.instruction(instruction_id)) continue;
            if (emission.dead.contains(instruction_id) and !emission.dead.isInlined(instruction_id)) continue;
            const instruction = program.instructions[instruction_id.index()];
            add(&units, 1);
            add(&units, instruction.results.len);
            add(&units, @intFromBool(instruction.pack_result != null));
            runtime_uses.visitOperationUses(instruction.operation, UseCounter{ .units = &units });
        }

        add(&units, 1);
        runtime_uses.visitTerminatorUses(block.terminator, UseCounter{ .units = &units });
    }
    return units;
}

fn regionHasEncodedJump(
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    region: *const structure.Region,
) bool {
    // A flat (arbitrary-CFG) root is emitted inside `while true do` plus a dispatch tree, whose whole-body back
    // jump the structured loop layout budgets at the `.loop` arm below; budget it here too.
    if (region.arbitrary_cfg) return true;
    for (region.nodes) |node| switch (node) {
        .block => {},
        .branch => |branch| {
            if (branch.block.index() >= program.blocks.len) return true;
            if (!emission.branchEdgesAreIdentical(program.blocks[branch.block.index()])) return true;
            if (regionHasEncodedJump(program, emission, branch.then_region) or
                regionHasEncodedJump(program, emission, branch.else_region)) return true;
        },
        .loop, .latch_loop, .infinite_loop, .loop_control, .loop_boundary, .loop_terminal => return true,
    };
    return false;
}

const UseCounter = struct {
    units: *usize,

    pub fn value(self: UseCounter, _: ir.ValueId) void {
        add(self.units, 1);
    }

    pub fn pack(self: UseCounter, _: ir.ValuePackId) void {
        add(self.units, 1);
    }

    pub fn place(self: UseCounter, _: ir.PlaceId) void {
        add(self.units, 1);
    }
};

fn add(total: *usize, amount: usize) void {
    total.* = std.math.add(usize, total.*, amount) catch std.math.maxInt(usize);
}

fn addProduct(total: *usize, count: usize, weight: usize) void {
    add(total, std.math.mul(usize, count, weight) catch std.math.maxInt(usize));
}

test "jump emission unit limit retains strict long-jump headroom" {
    try std.testing.expectEqual(@as(usize, 1_048_575), luau_runtime.max_jump_emission_units);
    try std.testing.expect(luau_runtime.max_jump_emission_units * luau_runtime.max_bytecode_words_per_emission_unit < luau_runtime.max_long_jump_distance);
    try std.testing.expect(luau_runtime.max_long_jump_distance < luau_runtime.max_function_instructions);
}
