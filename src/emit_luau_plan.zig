const std = @import("std");
const ir = @import("ir.zig");
const luau_runtime = @import("luau_runtime.zig");
const readable_scope = @import("readable_scope.zig");
const pack_plan = @import("pack_plan.zig");
const dead_code = @import("dead_code.zig");
const place_write_fusion = @import("place_write_fusion.zig");
const place_read_fusion = @import("place_read_fusion.zig");
const value_fusion = @import("value_fusion.zig");
const closure_store_fusion = @import("closure_store_fusion.zig");
const place_render = @import("emit_luau_place.zig");
const render = @import("emit_luau_expr.zig");
const name_plan = @import("name_plan.zig");
const stage_trace = @import("stage_trace.zig");

pub const NativeIterationCompletion = struct {
    header: ir.BlockId,
    flag_name: []const u8,
    parent: ?*NativeIterationCompletion = null,
};

/// The innermost Luau loop statement around the text being written, which a lexical `continue` binds to: a
/// transfer wrapper (`repeat ... until true`), whose end reaches its `stop`; a loop, whose next pass starts at its
/// `header` (`stop` is its body region's stop: the header, or a block that forwards to it); or a `for` written to
/// run its body once, which binds no `continue`. `parent` is the statement around it. A region written without the
/// transfer wrapper that would only forward its flags pushes a `forwarded` binder, which writes no statement: a
/// `continue` or `break` written under it binds to the statement around it.
pub const ContinueBinder = struct {
    kind: Kind,
    header: ?ir.BlockId = null,
    stop: ?ir.BlockId = null,
    parent: ?*const ContinueBinder = null,

    pub const Kind = enum { wrapper, loop, one_shot, forwarded };
};

pub const EmitState = struct {
    native_iteration_completion: ?*NativeIterationCompletion = null,
    continue_binder: ?*const ContinueBinder = null,
};

pub const Plan = struct {
    force_dispatcher: bool = false,
    state: *EmitState,
    runtime: luau_runtime.Plan,
    names: name_plan.Plan,
    packs: pack_plan.Plan,
    dead: dead_code.Plan,
    place_writes: place_write_fusion.Plan,
    place_reads: place_read_fusion.Plan,
    fused_values: value_fusion.Plan,
    closure_stores: closure_store_fusion.Plan,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program, target: luau_runtime.Target) !Plan {
        if (stage_trace.enabled) std.debug.print("emission_plan stage=scope_begin\n", .{});
        var scope = try readable_scope.Scope.init(allocator, program);
        defer scope.deinit();
        if (stage_trace.enabled) std.debug.print("emission_plan stage=scope_done\n", .{});
        if (stage_trace.enabled) std.debug.print("emission_plan stage=packs_begin\n", .{});
        var packs = try pack_plan.Plan.init(allocator, program);
        errdefer packs.deinit();
        if (stage_trace.enabled) std.debug.print("emission_plan stage=packs_done\n", .{});
        if (stage_trace.enabled) std.debug.print("emission_plan stage=dead_begin\n", .{});
        var dead = try dead_code.Plan.init(allocator, program, &packs);
        errdefer dead.deinit();
        if (stage_trace.enabled) std.debug.print("emission_plan stage=dead_done\n", .{});
        if (stage_trace.enabled) std.debug.print("emission_plan stage=place_writes_begin\n", .{});
        var place_writes = try place_write_fusion.Plan.init(allocator, program, &packs, &dead);
        errdefer place_writes.deinit();
        if (stage_trace.enabled) std.debug.print("emission_plan stage=place_writes_done\n", .{});
        if (stage_trace.enabled) std.debug.print("emission_plan stage=place_reads_begin\n", .{});
        var place_reads = try place_read_fusion.Plan.init(allocator, program, &packs, &dead);
        errdefer place_reads.deinit();
        if (stage_trace.enabled) std.debug.print("emission_plan stage=place_reads_done\n", .{});
        if (stage_trace.enabled) std.debug.print("emission_plan stage=closure_stores_begin\n", .{});
        var closure_stores = try closure_store_fusion.Plan.init(allocator, program, &dead);
        errdefer closure_stores.deinit();
        if (stage_trace.enabled) std.debug.print("emission_plan stage=closure_stores_done\n", .{});
        if (stage_trace.enabled) std.debug.print("emission_plan stage=fused_values_begin\n", .{});
        var fused_values = try value_fusion.Plan.init(allocator, program, &packs, &dead, &place_writes, &place_reads);
        errdefer fused_values.deinit();
        if (stage_trace.enabled) std.debug.print("emission_plan stage=fused_values_done\n", .{});
        var runtime = luau_runtime.Plan.initForEmission(target, program, &scope, &dead);
        for (program.instructions) |instruction| {
            if (packs.role(instruction.id) != .stored_invocation_producer) continue;
            runtime.require(.rawget);
            runtime.require(.rawset);
            runtime.require(.select);
            runtime.require(.table_unpack);
            break;
        }
        var names = try name_plan.Plan.initWithRuntime(allocator, program, &scope, runtime);
        errdefer names.deinit();
        const state = try allocator.create(EmitState);
        errdefer allocator.destroy(state);
        state.* = .{};
        return .{
            .state = state,
            .runtime = runtime,
            .names = names,
            .packs = packs,
            .dead = dead,
            .place_writes = place_writes,
            .place_reads = place_reads,
            .fused_values = fused_values,
            .closure_stores = closure_stores,
        };
    }

    pub fn deinit(self: *Plan) void {
        self.names.allocator.destroy(self.state);
        self.fused_values.deinit();
        self.closure_stores.deinit();
        self.place_reads.deinit();
        self.place_writes.deinit();
        self.dead.deinit();
        self.packs.deinit();
        self.names.deinit();
        self.* = undefined;
    }

    pub fn values(self: *const Plan, place_aliases: []const place_render.Alias) render.ValuePlan {
        return .{
            .names = &self.names,
            .dead = &self.dead,
            .place_reads = &self.place_reads,
            .fused_values = &self.fused_values,
            .packs = &self.packs,
            .place_aliases = place_aliases,
        };
    }

    pub fn instructionMayEmit(self: *const Plan, instruction: ir.Instruction) bool {
        if (self.dead.contains(instruction.id)) return false;
        if (self.place_reads.contains(instruction.id)) return false;
        if (self.fused_values.contains(instruction.id)) return false;
        if (self.closure_stores.consumerForProducer(instruction.id) != null) return false;
        if (self.place_writes.consumerForProducer(instruction.id) != null) return false;
        return switch (self.packs.role(instruction.id)) {
            .fused_invocation_producer, .fused_return_producer, .fused_pack_values_producer, .materialized_pack_values_producer, .fused_pack_values_return_producer => false,
            .materialized_adjustment => false,
            .materialized_adjustment_copy => instruction.results.len != 0,
            .stored_adjustment => instruction.results.len != 0,
            .direct_vararg_adjustment => instruction.results.len != 0,
            .fused_pack_values_adjustment => instruction.results.len != 0,
            else => true,
        };
    }

    pub fn branchEdgesAreIdentical(_: *const Plan, block: ir.Block) bool {
        const branch = switch (block.terminator) {
            .branch => |value| value,
            else => return false,
        };
        return branch.then_edge.target == branch.else_edge.target and
            std.mem.eql(ir.ValueId, branch.then_edge.arguments, branch.else_edge.arguments);
    }

    pub fn discardedBranchConditionNeedsLocal(self: *const Plan, program: *const ir.Program, block: ir.Block) bool {
        if (!self.branchEdgesAreIdentical(block)) return false;
        for (block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) return true;
            const instruction = program.instructions[instruction_id.index()];
            if (!self.instructionMayEmit(instruction) and !effectsAreObservationallyInert(instruction.effects)) return true;
        }
        return false;
    }
};

fn effectsAreObservationallyInert(effects: ir.EffectSummary) bool {
    return effects.precision == .exact and
        !effects.writes_memory and
        !effects.may_throw and
        !effects.may_yield and
        !effects.invokes_unknown_code;
}
