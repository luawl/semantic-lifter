const std = @import("std");
const ir = @import("ir.zig");
const luau_runtime = @import("luau_runtime.zig");
const validation = @import("validate.zig");
const structure = @import("structure.zig");
const structured_escape = @import("structured_escape.zig");
const cfg = @import("cfg.zig");
const iteration_protocol = @import("iteration_protocol.zig");
const render = @import("emit_luau_expr.zig");
const lexical = @import("emit_luau_lexical.zig");
const place_render = @import("emit_luau_place.zig");
const emission_scope = @import("emit_luau_scope.zig");
const emission_planning = @import("emit_luau_plan.zig");
const branch_expression = @import("emit_luau_branch_expr.zig");
const branch_statement = @import("emit_luau_branch_stmt.zig");
const call_emission = @import("emit_luau_call.zig");
const compound_update = @import("compound_update.zig");
const lexical_transfer = @import("lexical_transfer.zig");
const loop_continue_projection = @import("loop_continue_projection.zig");
const loop_exit_shape = @import("loop_exit_shape.zig");
const transparent_stop = @import("transparent_stop.zig");

pub const EmitError = error{
    InvalidIr,
    UnsupportedShape,
    UnsupportedControlFlow,
    UnsupportedOperation,
};

const PlaceAlias = lexical.PlaceAlias;

const EmissionPlan = emission_planning.Plan;

const ContainerGroupWrapper = struct {
    output_start: usize,
    body_start: usize,
};

pub const Target = luau_runtime.Target;

pub const Options = struct {
    force_dispatcher: bool = false,
};

const StableCaptureValues = struct {
    scopes: *const emission_scope.Plan,

    pub fn contains(self: StableCaptureValues, value_id: ir.ValueId) bool {
        return self.scopes.valueHasStableLexicalBinding(value_id);
    }
};

const ClosureDestination = union(enum) {
    value: struct {
        id: ir.ValueId,
        declare: bool,
    },
    place: struct {
        id: ir.PlaceId,
        declare: bool,
    },
    table: ir.TableSet,
    environment: ir.EnvironmentSet,
};

fn valuePlan(emission_plan: *const EmissionPlan, place_aliases: []const PlaceAlias) render.ValuePlan {
    return emission_plan.values(place_aliases);
}

fn composedValuePlan(
    emission_plan: *const EmissionPlan,
    place_aliases: []const PlaceAlias,
    composition: ?*const branch_expression.Composition,
) render.ValuePlan {
    var values = valuePlan(emission_plan, place_aliases);
    if (composition) |value| values.value_override = value.valueOverride();
    return values;
}

fn functionNeedsArbitraryFallback(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function_id: ir.FunctionId,
) (EmitError || std.mem.Allocator.Error)!bool {
    if (function_id.index() >= program.functions.len) return error.UnsupportedControlFlow;
    const function = program.functions[function_id.index()];
    if (structure.Plan.shouldUseArbitraryFallbackForFunction(program, function)) return true;
    var analysis = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
        error.InvalidCfg => return error.UnsupportedControlFlow,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    var plan = structure.Plan.init(allocator, &analysis) catch |err| switch (err) {
        error.UnsupportedShape => return true,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer plan.deinit();
    return false;
}

fn emitRuntimePrelude(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    emission_plan: *const EmissionPlan,
    program: *const ir.Program,
) !void {
    switch (emission_plan.runtime.target) {
        .standard_luau, .direct_locals_luau => {},
    }
    var wrote_capture = false;
    for (luau_runtime.capabilities) |capability| {
        const capture = emission_plan.names.runtimeCapability(capability) orelse continue;
        const source = capability.source();
        try output.appendSlice(allocator, "local ");
        try render.globalIdentifier(output, allocator, capture);
        try output.appendSlice(allocator, " = ");
        try render.globalIdentifier(output, allocator, source.global.name());
        if (source.method) |method| {
            try output.append(allocator, '.');
            try render.globalIdentifier(output, allocator, method);
        }
        try output.append(allocator, '\n');
        wrote_capture = true;
    }
    if (wrote_capture) try output.append(allocator, '\n');

    // The crackme lift represents the VM's dynamic function-factory handler as
    // an explicit ambient helper. Keep that dependency in the emitted module
    // instead of assuming the host happens to provide it. Native IR closures
    // continue through emitClosure; this helper is only for wrappers whose
    // callable is selected dynamically at runtime.
    var needs_dynamic_closure_helper = false;
    for (program.instructions) |instruction| {
        switch (instruction.operation) {
            .environment_get => |get| {
                if (get.mode != .semantic) continue;
                switch (get.target) {
                    .ambient => {
                        if (std.mem.eql(u8, get.name, "__make_closure")) {
                            needs_dynamic_closure_helper = true;
                        }
                    },
                    .value => {},
                }
            },
            else => {},
        }
        if (needs_dynamic_closure_helper) break;
    }
    if (needs_dynamic_closure_helper) {
        try output.appendSlice(
            allocator,
            "local __closure_frames = {}\n" ++
                "local function __make_closure(target, registers, capture_index, scope, owner, pc, slot)\n" ++
                "  return function(...)\n" ++
                "    local callable = target\n" ++
                "    if callable == nil and registers ~= nil then callable = registers[capture_index] end\n" ++
                "    if type(callable) ~= \"function\" then return nil end\n" ++
                "    local active = __closure_frames[owner]\n" ++
                "    if active then\n" ++
                "      error(\"re-entrant VM closure frame\", 0)\n" ++
                "    end\n" ++
                "    __closure_frames[owner] = { pc, slot, scope }\n" ++
                "    local results = table.pack(pcall(callable, ...))\n" ++
                "    __closure_frames[owner] = nil\n" ++
                "    if not results[1] then error(results[2], 0) end\n" ++
                "    return table.unpack(results, 2, results.n)\n" ++
                "  end\n" ++
                "end\n\n",
        );
    }
}

fn emitFunctionParameters(output: *std.ArrayList(u8), allocator: std.mem.Allocator, emission_plan: *const EmissionPlan, function: ir.Function) !void {
    for (function.parameters, 0..) |parameter, index| {
        if (index != 0) try output.appendSlice(allocator, ", ");
        try render.valueName(output, allocator, &emission_plan.names, parameter);
    }
    if (function.is_variadic) {
        if (function.parameters.len != 0) try output.appendSlice(allocator, ", ");
        try output.appendSlice(allocator, "...");
    }
}

fn emitEntryParameters(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    entry: ir.Function,
) !void {
    if (program.external_bindings.len == 0 and entry.parameters.len == 0) return;
    try output.appendSlice(allocator, "local ");
    var wrote_name = false;
    for (program.external_bindings) |binding| {
        if (wrote_name) try output.appendSlice(allocator, ", ");
        try place_render.emitExternalBindingName(output, allocator, &emission_plan.names, binding.id);
        wrote_name = true;
    }
    for (entry.parameters, 0..) |parameter, index| {
        _ = index;
        if (wrote_name) try output.appendSlice(allocator, ", ");
        try render.valueName(output, allocator, &emission_plan.names, parameter);
        wrote_name = true;
    }
    try output.appendSlice(allocator, " = ...\n");
}

fn emitEntryValueBindings(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    emission_plan: *const EmissionPlan,
    bindings: []const lexical.EntryValueBinding,
) !void {
    for (bindings) |binding| {
        try output.appendSlice(allocator, "local ");
        try render.valueName(output, allocator, &emission_plan.names, binding.captured);
        try output.appendSlice(allocator, " = ");
        try place_render.emitExternalBindingName(output, allocator, &emission_plan.names, binding.source);
        try output.append(allocator, '\n');
    }
}

fn emitArbitraryCfgDeclarations(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    function: ir.Function,
    indent: []const u8,
) (EmitError || std.mem.Allocator.Error)!void {
    var bare_count: usize = 0;
    for (function.local_places) |place_id| {
        if (place_id.index() >= program.places.len or emission_plan.names.placeUsesStorage(place_id)) continue;
        const place = program.places[place_id.index()];
        switch (place.origin) {
            .local, .instruction => {},
            .capture => continue,
        }
        const name = emission_plan.names.place(place_id) orelse return error.UnsupportedOperation;
        if (scopes.placeMovedLiteralInitializer(place_id)) |literal| {
            try flushBareDeclarations(output, allocator, &bare_count);
            try output.appendSlice(allocator, indent);
            try output.appendSlice(allocator, "local ");
            try output.appendSlice(allocator, name);
            try output.appendSlice(allocator, " = ");
            try render.literal(output, allocator, literal);
            try output.append(allocator, '\n');
        } else {
            try appendBareDeclaration(output, allocator, indent, name, &bare_count);
        }
    }

    for (program.values) |value| {
        if (value.function != function.id) continue;
        if (emission_plan.names.valueUsesStorage(value.id)) continue;
        switch (value.origin) {
            .parameter, .capture => continue,
            .block_parameter, .instruction_result => {},
        }
        if (emission_plan.names.value(value.id)) |name| {
            try appendBareDeclaration(output, allocator, indent, name, &bare_count);
        }
    }
    for (program.value_packs) |pack| {
        if (pack.function != function.id) continue;
        if (emission_plan.names.valuePack(pack.id)) |name| {
            try appendBareDeclaration(output, allocator, indent, name, &bare_count);
        }
    }
    try flushBareDeclarations(output, allocator, &bare_count);
}

fn emitArbitraryTerminator(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    block: ir.Block,
    pc_name: []const u8,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    switch (block.terminator) {
        .jump => |edge| {
            if (edge.target.index() >= program.blocks.len) return error.UnsupportedControlFlow;
            try emitEdgeParametersUnlessConsumed(output, allocator, program, emission_plan, scopes, program.blocks[edge.target.index()], edge.arguments, indent, false, place_aliases);
            try output.appendSlice(allocator, indent);
            try output.appendSlice(allocator, pc_name);
            try output.appendSlice(allocator, " = ");
            try output.print(allocator, "{d}\n", .{edge.target.index()});
        },
        .branch => |branch| {
            if (branch.then_edge.target.index() >= program.blocks.len or branch.else_edge.target.index() >= program.blocks.len) return error.UnsupportedControlFlow;
            try output.appendSlice(allocator, indent);
            try output.appendSlice(allocator, "if ");
            try branch_expression.emitCondition(output, allocator, program, emission_plan, branch.condition, null, false, place_aliases);
            try output.appendSlice(allocator, " then\n");
            const arm_indent = try allocDeeperIndent(allocator, indent);
            defer allocator.free(arm_indent);
            try emitEdgeParametersUnlessConsumed(output, allocator, program, emission_plan, scopes, program.blocks[branch.then_edge.target.index()], branch.then_edge.arguments, arm_indent, false, place_aliases);
            try output.appendSlice(allocator, arm_indent);
            try output.appendSlice(allocator, pc_name);
            try output.appendSlice(allocator, " = ");
            try output.print(allocator, "{d}\n", .{branch.then_edge.target.index()});
            try output.appendSlice(allocator, indent);
            try output.appendSlice(allocator, "else\n");
            try emitEdgeParametersUnlessConsumed(output, allocator, program, emission_plan, scopes, program.blocks[branch.else_edge.target.index()], branch.else_edge.arguments, arm_indent, false, place_aliases);
            try output.appendSlice(allocator, arm_indent);
            try output.appendSlice(allocator, pc_name);
            try output.appendSlice(allocator, " = ");
            try output.print(allocator, "{d}\n", .{branch.else_edge.target.index()});
            try output.appendSlice(allocator, indent);
            try output.appendSlice(allocator, "end\n");
        },
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => try call_emission.terminator(
            output,
            allocator,
            program,
            emission_plan,
            block,
            indent,
            valuePlan(emission_plan, place_aliases),
        ),
    }
}

fn trimTrailingEmptyReturn(output: *std.ArrayList(u8), indent: []const u8) void {
    const statement = "return\n";
    const suffix_len = indent.len + statement.len;
    if (output.items.len < suffix_len) return;
    const suffix = output.items[output.items.len - suffix_len ..];
    if (!std.mem.eql(u8, suffix[0..indent.len], indent) or !std.mem.eql(u8, suffix[indent.len..], statement)) return;
    if (output.items.len != suffix_len and output.items[output.items.len - suffix_len - 1] != '\n') return;
    output.items.len -= suffix_len;
}

fn closeContainerGroupWrapper(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    region_indent: []const u8,
    wrapper: ContainerGroupWrapper,
) std.mem.Allocator.Error!void {
    if (output.items.len == wrapper.body_start) {
        output.shrinkRetainingCapacity(wrapper.output_start);
        return;
    }
    try output.appendSlice(allocator, region_indent);
    try output.appendSlice(allocator, "end\n");
}

fn validatedStopForwardingEdge(program: *const ir.Program, region: *const structure.Region) EmitError!?ir.Edge {
    const entry = region.stop_forwarding orelse return null;
    const stop = region.stop orelse return error.UnsupportedControlFlow;
    return try transparent_stop.validateEdge(program, entry, stop);
}

const ValidatedContinueProjection = struct {
    source_edge: ir.Edge,
    target_edge: ir.Edge,
    nonlocal: bool,
};

fn regionOwnsTransferredContinue(region: *const structure.Region, target: ir.BlockId) bool {
    if (region.nodes.len == 0) return false;
    return switch (region.nodes[region.nodes.len - 1]) {
        .branch => |branch| branch.join != null and branch.join.? == target,
        .latch_loop => |loop| loop.exit == target,
        .infinite_loop => |loop| loop.exit != null and loop.exit.? == target,
        else => false,
    };
}

// An authenticated clone boundary can replace an entire empty branch arm.
// The incoming edge still enters the clone, while the projection edge enters
// the canonical continuation with the same tuple. Validate both sides before
// omitting the clone body; ordinary empty arms remain on the existing path.
fn validateEmptyProjectedContinue(
    program: *const ir.Program,
    region: *const structure.Region,
    entry: ir.Edge,
) (EmitError)!?ir.Edge {
    if (region.nodes.len != 0) return null;
    const projection = region.continue_projection orelse return null;
    if (projection.forwarding != null) return error.UnsupportedControlFlow;
    const projected_edge = projection.edge orelse return null;
    if (projected_edge.target != projection.target or
        !std.mem.eql(ir.ValueId, entry.arguments, projected_edge.arguments))
    {
        return error.UnsupportedControlFlow;
    }
    _ = try loop_continue_projection.validateEntry(program, entry.target, entry);
    _ = try loop_continue_projection.validateEntry(program, projection.target, projected_edge);
    return projected_edge;
}

fn validatedContinueProjectionAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    region: *const structure.Region,
) (EmitError || std.mem.Allocator.Error)!?ValidatedContinueProjection {
    const projection = region.continue_projection orelse return null;
    const nonlocal = if (region.continue_target) |continue_target|
        projection.target != continue_target
    else
        true;
    if (nonlocal and projection.forwarding == null) {
        const expected = projection.edge orelse {
            if (!regionOwnsTransferredContinue(region, projection.target)) return error.UnsupportedControlFlow;
            return null;
        };
        if (region.nodes.len == 0) return error.UnsupportedControlFlow;
        const source = switch (region.nodes[region.nodes.len - 1]) {
            .block => |block_id| block_id,
            else => return null,
        };
        const edge = try loop_continue_projection.validateFinal(program, source, projection.target, expected);
        return .{ .source_edge = edge, .target_edge = edge, .nonlocal = true };
    }
    if (projection.forwarding) |forwarding| {
        if (projection.edge != null or region.nodes.len == 0) {
            return error.UnsupportedControlFlow;
        }
        const source = switch (region.nodes[region.nodes.len - 1]) {
            .block => |block_id| block_id,
            else => return error.UnsupportedControlFlow,
        };
        const source_edge = try loop_continue_projection.validateForwardingFinalAlloc(
            allocator,
            program,
            source,
            projection.target,
            forwarding,
        );
        return .{ .source_edge = source_edge, .target_edge = forwarding.edge, .nonlocal = nonlocal };
    }
    const continue_target = region.continue_target orelse return error.UnsupportedControlFlow;
    const expected = projection.edge orelse {
        if (region.nodes.len != 0 and !regionOwnsTransferredContinue(region, continue_target)) return error.UnsupportedControlFlow;
        return null;
    };
    if (region.nodes.len == 0) return error.UnsupportedControlFlow;
    const edge = switch (region.nodes[region.nodes.len - 1]) {
        .block => |block_id| try loop_continue_projection.validateFinal(program, block_id, continue_target, expected),
        .loop => |loop| try loop_continue_projection.validateStructuredLoopExit(
            program,
            loop.header,
            loop.continue_on_true,
            continue_target,
            loop.exit_edge,
            expected,
        ),
        else => return error.UnsupportedControlFlow,
    };
    return .{ .source_edge = edge, .target_edge = edge, .nonlocal = false };
}

fn branchArmIsStructurallyEmpty(
    program: *const ir.Program,
    edge: ir.Edge,
    region: *const structure.Region,
    join: ?ir.BlockId,
) bool {
    return branch_statement.armIsStructurallyEmpty(program, edge, region, join);
}

fn prepareLoopExit(
    _: *std.ArrayList(u8),
    _: std.mem.Allocator,
    _: *const ir.Program,
    _: *const EmissionPlan,
    enclosing_region: *const structure.Region,
    node_index: usize,
    exit: ir.BlockId,
    _: []const u8,
) !void {
    if (node_index < enclosing_region.nodes.len) {
        const is_escape = switch (enclosing_region.nodes[node_index]) {
            .loop => |loop| loop.exit_is_escape and loop.exit_edge.target == exit,
            .latch_loop => |loop| loop.exit_is_escape and loop.exit == exit,
            .infinite_loop => |loop| loop.exit_is_escape and loop.exit != null and loop.exit.? == exit,
            else => false,
        };
        if (is_escape) return;
    }
    const exit_is_region_stop = enclosing_region.stop != null and exit == enclosing_region.stop.?;
    if (exit_is_region_stop) return;
    const exit_is_enclosing_loop_exit = enclosing_region.loop_exit != null and exit == enclosing_region.loop_exit.?;
    if (exit_is_enclosing_loop_exit) return;
    const exit_is_projected_continue = node_index + 1 == enclosing_region.nodes.len and
        enclosing_region.continue_projection != null and
        enclosing_region.continue_projection.?.target == exit;
    if (exit_is_projected_continue) return;
    if (node_index + 1 >= enclosing_region.nodes.len or enclosing_region.nodes[node_index + 1].blockId() != exit) {
        return error.UnsupportedControlFlow;
    }
}

fn escapePropagationIsLoopContinue(target: ir.BlockId, loop_header: ?ir.BlockId) bool {
    return loop_header != null and target == loop_header.?;
}

fn regionOwnedContinueHeader(region: *const structure.Region) ?ir.BlockId {
    const stop = region.stop orelse return null;
    if (region.continue_target == null or region.continue_target.? != stop) return null;
    return stop;
}

const EmptyBoundaryContinue = struct {
    target: ir.BlockId,
    nonlocal: bool,
};

fn validateEmptyBoundaryContinue(
    program: *const ir.Program,
    region: *const structure.Region,
    entry: ir.Edge,
) (EmitError)!?EmptyBoundaryContinue {
    if (region.nodes.len != 0) return null;
    const projection = region.continue_projection orelse return null;
    if (projection.edge != null or projection.forwarding != null) return error.UnsupportedControlFlow;
    _ = try loop_continue_projection.validateEntry(program, projection.target, entry);
    return .{
        .target = projection.target,
        .nonlocal = region.continue_target == null or region.continue_target.? != projection.target,
    };
}

fn appendBareDeclaration(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    indent: []const u8,
    name: []const u8,
    count: *usize,
) !void {
    if (count.* == 0) {
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "local ");
    } else try output.appendSlice(allocator, ", ");
    try output.appendSlice(allocator, name);
    count.* += 1;
    if (count.* == 8) try flushBareDeclarations(output, allocator, count);
}

fn flushBareDeclarations(output: *std.ArrayList(u8), allocator: std.mem.Allocator, count: *usize) !void {
    if (count.* == 0) return;
    try output.append(allocator, '\n');
    count.* = 0;
}

fn emitEdgeParametersUnlessConsumed(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    target: ir.Block,
    arguments: []const ir.ValueId,
    indent: []const u8,
    declare: bool,
    place_aliases: []const PlaceAlias,
) !void {
    if (scopes.nativeIterationConsumesParameters(target.id)) return;
    try emitEdgeParameters(output, allocator, program, emission_plan, target, arguments, indent, declare, place_aliases);
}

fn emitEdgeParameters(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, emission_plan: *const EmissionPlan, target: ir.Block, arguments: []const ir.ValueId, indent: []const u8, declare: bool, place_aliases: []const PlaceAlias) !void {
    _ = declare;
    var remaining: usize = 0;
    for (target.parameters) |parameter| {
        if (!emission_plan.dead.isValueAlias(parameter)) remaining += 1;
    }
    if (remaining == 0) return;
    try output.appendSlice(allocator, indent);
    var wrote_parameter = false;
    for (target.parameters) |parameter| {
        if (emission_plan.dead.isValueAlias(parameter)) continue;
        if (wrote_parameter) try output.appendSlice(allocator, ", ");
        try render.valueName(output, allocator, &emission_plan.names, parameter);
        wrote_parameter = true;
    }
    try output.appendSlice(allocator, " = ");
    var wrote_argument = false;
    for (target.parameters, arguments) |parameter, argument| {
        if (emission_plan.dead.isValueAlias(parameter)) continue;
        if (wrote_argument) try output.appendSlice(allocator, ", ");
        try render.valueUseScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), argument);
        wrote_argument = true;
    }
    try output.append(allocator, '\n');
}

fn allocDeeperIndent(allocator: std.mem.Allocator, indent: []const u8) ![]u8 {
    const result_len = @min(indent.len + 2, luau_runtime.max_source_indent_spaces);
    const result = try allocator.alloc(u8, result_len);
    const copied_len = @min(indent.len, result.len);
    @memcpy(result[0..copied_len], indent[0..copied_len]);
    @memset(result[copied_len..], ' ');
    return result;
}

test "source indentation remains bounded independently of syntax depth" {
    var indent = try std.testing.allocator.alloc(u8, 0);
    defer std.testing.allocator.free(indent);
    for (0..luau_runtime.max_source_indent_spaces) |_| {
        const deeper = try allocDeeperIndent(std.testing.allocator, indent);
        std.testing.allocator.free(indent);
        indent = deeper;
    }
    try std.testing.expectEqual(luau_runtime.max_source_indent_spaces, indent.len);
}

test "propagated escape to the current loop header continues the loop" {
    const header = ir.BlockId.fromIndex(17);
    const outer = ir.BlockId.fromIndex(23);
    try std.testing.expect(escapePropagationIsLoopContinue(header, header));
    try std.testing.expect(!escapePropagationIsLoopContinue(outer, header));
    try std.testing.expect(!escapePropagationIsLoopContinue(header, null));
}

test "wrapped region exposes only its owning loop continuation" {
    const stop = ir.BlockId.fromIndex(31);
    const other = ir.BlockId.fromIndex(32);
    var nodes = [_]structure.Node{};
    var region = structure.Region{
        .nodes = &nodes,
        .stop = stop,
        .loop_exit = other,
        .continue_target = stop,
    };
    try std.testing.expectEqual(stop, regionOwnedContinueHeader(&region).?);

    region.continue_target = other;
    try std.testing.expect(regionOwnedContinueHeader(&region) == null);
    region.continue_target = null;
    try std.testing.expect(regionOwnedContinueHeader(&region) == null);
}

test "loop exits may target the enclosing loop boundary" {
    const first = ir.BlockId.fromIndex(0);
    const loop = ir.BlockId.fromIndex(1);
    const exit = ir.BlockId.fromIndex(2);
    const stop = ir.BlockId.fromIndex(3);
    var nodes = [_]structure.Node{ .{ .block = first }, .{ .block = loop } };
    const region: structure.Region = .{
        .nodes = &nodes,
        .stop = stop,
        .loop_exit = exit,
    };

    try prepareLoopExit(undefined, undefined, undefined, undefined, &region, 1, exit, "");
}

test "nonlocal transferred continuation may omit a local target" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const wrong_target = ir.BlockId.fromIndex(2);
    var then_nodes = [_]structure.Node{};
    var else_nodes = [_]structure.Node{};
    var then_region = structure.Region{ .nodes = &then_nodes, .stop = target, .loop_exit = null };
    var else_region = structure.Region{ .nodes = &else_nodes, .stop = target, .loop_exit = null };
    var nodes = [_]structure.Node{.{ .branch = .{
        .block = source,
        .then_region = &then_region,
        .else_region = &else_region,
        .join = target,
    } }};
    var region = structure.Region{
        .nodes = &nodes,
        .stop = null,
        .loop_exit = null,
        .continue_projection = .{ .target = target, .edge = null },
    };
    const program: ir.Program = .{
        .program_id = "nonlocal-transferred-continuation",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
    };

    try std.testing.expect((try validatedContinueProjectionAlloc(std.testing.allocator, &program, &region)) == null);
    region.continue_projection = .{ .target = wrong_target, .edge = null };
    try std.testing.expectError(
        error.UnsupportedControlFlow,
        validatedContinueProjectionAlloc(std.testing.allocator, &program, &region),
    );
}

test "empty loop-boundary continuation authenticates its entry edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const local_stop = ir.BlockId.fromIndex(2);
    const parameter = ir.ValueId.fromIndex(0);
    const argument = ir.ValueId.fromIndex(1);
    const target_parameters = [_]ir.ValueId{parameter};
    const arguments = [_]ir.ValueId{argument};
    const blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = target, .function = function_id, .parameters = &target_parameters, .terminator = .{ .return_values = &.{} } },
        .{ .id = local_stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const program: ir.Program = .{
        .program_id = "empty-loop-boundary-continuation",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var nodes = [_]structure.Node{};
    var region = structure.Region{
        .nodes = &nodes,
        .stop = local_stop,
        .loop_exit = null,
        .continue_target = local_stop,
        .continue_projection = .{ .target = target, .edge = null },
    };
    const edge: ir.Edge = .{ .target = target, .arguments = &arguments };

    const nonlocal = (try validateEmptyBoundaryContinue(&program, &region, edge)).?;
    try std.testing.expectEqual(target, nonlocal.target);
    try std.testing.expect(nonlocal.nonlocal);

    region.continue_target = target;
    const local = (try validateEmptyBoundaryContinue(&program, &region, edge)).?;
    try std.testing.expectEqual(target, local.target);
    try std.testing.expect(!local.nonlocal);

    const wrong_edge: ir.Edge = .{ .target = local_stop, .arguments = &.{} };
    try std.testing.expectError(error.UnsupportedControlFlow, validateEmptyBoundaryContinue(&program, &region, wrong_edge));
}

test "empty branch arm clone continuation authenticates its mapped edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const clone = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const stop = ir.BlockId.fromIndex(2);
    const clone_parameter = ir.ValueId.fromIndex(0);
    const target_parameter = ir.ValueId.fromIndex(1);
    const argument = ir.ValueId.fromIndex(2);
    const clone_parameters = [_]ir.ValueId{clone_parameter};
    const target_parameters = [_]ir.ValueId{target_parameter};
    const blocks = [_]ir.Block{
        .{ .id = clone, .function = function_id, .parameters = &clone_parameters, .terminator = .{ .return_values = &.{} } },
        .{ .id = target, .function = function_id, .parameters = &target_parameters, .terminator = .{ .return_values = &.{} } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const program: ir.Program = .{
        .program_id = "empty-branch-arm-clone-continuation",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var nodes = [_]structure.Node{};
    var region = structure.Region{
        .nodes = &nodes,
        .stop = stop,
        .loop_exit = null,
        .continue_target = null,
        .continue_projection = .{
            .target = target,
            .edge = .{ .target = target, .arguments = &.{argument} },
        },
    };
    const entry = ir.Edge{ .target = clone, .arguments = &.{argument} };
    const projected = (try validateEmptyProjectedContinue(&program, &region, entry)).?;
    try std.testing.expectEqual(target, projected.target);
    try std.testing.expectEqualSlices(ir.ValueId, &.{argument}, projected.arguments);

    region.continue_projection.?.edge = .{ .target = target, .arguments = &.{target_parameter} };
    try std.testing.expectError(
        error.UnsupportedControlFlow,
        validateEmptyProjectedContinue(&program, &region, entry),
    );
    region.continue_projection.?.edge = .{ .target = target, .arguments = &.{argument} };
    const wrong_entry = ir.Edge{ .target = clone, .arguments = &.{target_parameter} };
    try std.testing.expectError(
        error.UnsupportedControlFlow,
        validateEmptyProjectedContinue(&program, &region, wrong_entry),
    );
}

test "empty branch arm requires a parameter-free jump to its join" {
    const function_id = ir.FunctionId.fromIndex(0);
    const empty_id = ir.BlockId.fromIndex(0);
    const join_id = ir.BlockId.fromIndex(1);
    const blocks = [_]ir.Block{
        .{ .id = empty_id, .function = function_id, .terminator = .{ .jump = .{ .target = join_id } } },
        .{ .id = join_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const program: ir.Program = .{
        .program_id = "empty-branch-arm-test",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var nodes = [_]structure.Node{.{ .block = empty_id }};
    const region: structure.Region = .{ .nodes = &nodes, .stop = join_id, .loop_exit = null };

    try std.testing.expect(branchArmIsStructurallyEmpty(&program, .{ .target = empty_id }, &region, join_id));
    try std.testing.expect(!branchArmIsStructurallyEmpty(&program, .{ .target = empty_id, .arguments = &.{ir.ValueId.fromIndex(0)} }, &region, join_id));
}
