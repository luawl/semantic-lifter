const std = @import("std");
const ir = @import("ir.zig");
const diagnostics = @import("diagnostics.zig");
const validation = @import("validate.zig");
const proof_validation = @import("validate_proofs.zig");
const effect_validation = @import("validate_effects.zig");

pub fn validateAlloc(allocator: std.mem.Allocator, program: *const ir.Program) !diagnostics.Report {
    var core = try validation.validate(allocator, program, .core);
    if (core.isClean()) return core;

    var report = diagnostics.Report.init(allocator);
    errdefer report.deinit();
    for (core.diagnostics.items) |diagnostic| {
        if (isDeferredPendingProof(program, diagnostic)) continue;
        const entity_index: ?usize = if (diagnostic.entity_index) |index| @intCast(index) else null;
        try report.add(diagnostic.code, entity_index);
    }
    core.deinit();
    return report;
}

fn isDeferredPendingProof(program: *const ir.Program, diagnostic: diagnostics.Diagnostic) bool {
    const entity_index: usize = @intCast(diagnostic.entity_index orelse return false);
    return switch (diagnostic.code) {
        .open_profile_obligation => proof_validation.hasPendingCoreObligation(program, entity_index),
        .understated_call_effects,
        .understated_operator_effects,
        .unproved_primitive_operator_domain,
        .understated_table_get_effects,
        .understated_table_set_effects,
        .understated_environment_get_effects,
        .understated_environment_set_effects,
        => blk: {
            if (entity_index >= program.instructions.len) break :blk false;
            const instruction = program.instructions[entity_index];
            if (instruction.id.index() != entity_index) break :blk false;
            break :blk effect_validation.pendingAuthorityResolves(program, instruction, diagnostic.code);
        },
        else => false,
    };
}
