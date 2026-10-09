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

fn regionAlwaysFunctionTerminates(program: *const ir.Program, region: *const structure.Region) bool {
    if (region.terminal_projection != null) return true;
    if (region.escape_projection != null) return false;
    if (region.nodes.len == 0) return false;
    return nodeAlwaysFunctionTerminates(program, region.nodes[region.nodes.len - 1]);
}

fn nodeAlwaysFunctionTerminates(program: *const ir.Program, node: structure.Node) bool {
    return switch (node) {
        .block => |block_id| switch (program.blocks[block_id.index()].terminator) {
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => true,
            else => false,
        },
        .branch => |branch| branch.join == null and
            regionAlwaysFunctionTerminates(program, branch.then_region) and
            regionAlwaysFunctionTerminates(program, branch.else_region),
        else => false,
    };
}

fn sameEdge(left: ir.Edge, right: ir.Edge) bool {
    return left.target == right.target and std.mem.eql(ir.ValueId, left.arguments, right.arguments);
}

fn branchArmIsStructurallyEmpty(
    program: *const ir.Program,
    edge: ir.Edge,
    region: *const structure.Region,
    join: ?ir.BlockId,
) bool {
    return branch_statement.armIsStructurallyEmpty(program, edge, region, join);
}

fn genericInitializerCount(program: *const ir.Program, emission_plan: *const EmissionPlan, arguments: []const ir.ValueId) usize {
    var count = arguments.len;
    while (count > 1 and valueIsExactNil(program, emission_plan, arguments[count - 1])) count -= 1;
    return count;
}

fn valueIsExactNil(program: *const ir.Program, emission_plan: *const EmissionPlan, value_id: ir.ValueId) bool {
    const resolved = emission_plan.dead.resolveValue(value_id);
    if (resolved.index() >= program.values.len) return false;
    const origin = switch (program.values[resolved.index()].origin) {
        .instruction_result => |value| value,
        else => return false,
    };
    if (origin.index != 0 or origin.instruction.index() >= program.instructions.len) return false;
    return switch (program.instructions[origin.instruction.index()].operation) {
        .constant => |literal| literal == .nil_value,
        else => false,
    };
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

fn emitLoopExit(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, emission_plan: *const EmissionPlan, edge: ir.Edge, indent: []const u8, place_aliases: []const PlaceAlias) !void {
    try emitEdgeParameters(output, allocator, program, emission_plan, program.blocks[edge.target.index()], edge.arguments, indent, false, place_aliases);
    try emitBreakStatement(output, allocator, indent);
}

fn emitBreakStatement(output: *std.ArrayList(u8), allocator: std.mem.Allocator, indent: []const u8) std.mem.Allocator.Error!void {
    const transfer_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(transfer_indent);
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "do\n");
    try output.appendSlice(allocator, transfer_indent);
    try output.appendSlice(allocator, "break\n");
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

fn escapeFlagNameAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    target: ir.BlockId,
) std.mem.Allocator.Error![]const u8 {
    const base = try std.fmt.allocPrint(allocator, "__lifter_escape_{d}", .{target.index()});
    defer allocator.free(base);
    return emission_plan.names.internalNameAlloc(allocator, program, base);
}

fn emitEscapeFlagDeclaration(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    target: ir.BlockId,
    indent: []const u8,
) std.mem.Allocator.Error!void {
    const flag = try escapeFlagNameAlloc(allocator, program, emission_plan, target);
    defer allocator.free(flag);
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "local ");
    try output.appendSlice(allocator, flag);
    try output.appendSlice(allocator, " = false\n");
}

fn emitEscapeFlagSet(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    target: ir.BlockId,
    indent: []const u8,
) std.mem.Allocator.Error!void {
    const flag = try escapeFlagNameAlloc(allocator, program, emission_plan, target);
    defer allocator.free(flag);
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, flag);
    try output.appendSlice(allocator, " = true\n");
}

fn emitEscapePropagation(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    targets: []const ir.BlockId,
    indent: []const u8,
    loop_header: ?ir.BlockId,
) std.mem.Allocator.Error!void {
    if (targets.len == 0) return;
    const break_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(break_indent);
    for (targets) |target| {
        const flag = try escapeFlagNameAlloc(allocator, program, emission_plan, target);
        defer allocator.free(flag);
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "if ");
        try output.appendSlice(allocator, flag);
        try output.appendSlice(allocator, " then\n");
        try output.appendSlice(allocator, break_indent);
        if (escapePropagationIsLoopContinue(target, loop_header)) {
            try output.appendSlice(allocator, "continue\n");
        } else {
            try output.appendSlice(allocator, "break\n");
        }
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "end\n");
    }
}

fn emitEscapeContinueIfSet(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    target: ir.BlockId,
    indent: []const u8,
) std.mem.Allocator.Error!void {
    const flag = try escapeFlagNameAlloc(allocator, program, emission_plan, target);
    defer allocator.free(flag);
    const body_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(body_indent);
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "if ");
    try output.appendSlice(allocator, flag);
    try output.appendSlice(allocator, " then\n");
    try emitContinueStatement(output, allocator, body_indent);
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

fn escapePropagationIsLoopContinue(target: ir.BlockId, loop_header: ?ir.BlockId) bool {
    return loop_header != null and target == loop_header.?;
}

fn emitLoopEscapePropagation(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    node: structure.Node,
    indent: []const u8,
    consume_header_continue: bool,
) std.mem.Allocator.Error!void {
    const targets = try structured_escape.loopFreeTargetsAlloc(allocator, node);
    defer allocator.free(targets);
    const loop_header = if (consume_header_continue) node.blockId() else null;
    try emitEscapePropagation(output, allocator, program, emission_plan, targets, indent, loop_header);
    if (consume_header_continue and
        !containsBlockId(targets, node.blockId()) and
        loopNodeBodyHasNestedHeaderEscape(node, node.blockId()))
    {
        try emitEscapeContinueIfSet(output, allocator, program, emission_plan, node.blockId(), indent);
    }
}

fn emitRegionEscapePropagation(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    region: *const structure.Region,
    indent: []const u8,
) std.mem.Allocator.Error!void {
    const targets = try structured_escape.regionFreeTargetsAlloc(allocator, region);
    defer allocator.free(targets);
    const loop_header = regionOwnedContinueHeader(region);
    try emitEscapePropagation(output, allocator, program, emission_plan, targets, indent, loop_header);
    if (region.loop_exit) |loop_exit| {
        if (!containsBlockId(targets, loop_exit) and
            structured_escape.regionHasLoopBoundaryExitTo(region, loop_exit))
        {
            // A loop-boundary exit is owned by the surrounding loop and thus
            // intentionally absent from free-target accounting. If a lexical
            // transfer wrapper intercepted its break, forward the saved exit
            // signal now that the temporary repeat has closed.
            const exit_target = [_]ir.BlockId{loop_exit};
            try emitEscapePropagation(output, allocator, program, emission_plan, &exit_target, indent, null);
        }
    }
    if (loop_header != null and
        !containsBlockId(targets, loop_header.?) and
        structured_escape.regionHasNestedEscapeTo(region, loop_header.?))
    {
        // The target is the region's owning loop stop, so consume a nested
        // transfer after the temporary wrapper has closed as a loop continue.
        try emitEscapeContinueIfSet(output, allocator, program, emission_plan, loop_header.?, indent);
    }
}

fn regionOwnedContinueHeader(region: *const structure.Region) ?ir.BlockId {
    const stop = region.stop orelse return null;
    if (region.continue_target == null or region.continue_target.? != stop) return null;
    return stop;
}

fn containsBlockId(targets: []const ir.BlockId, target: ir.BlockId) bool {
    for (targets) |candidate| if (candidate == target) return true;
    return false;
}

fn loopNodeBodyHasNestedHeaderEscape(node: structure.Node, header: ir.BlockId) bool {
    return switch (node) {
        .loop => |loop| structured_escape.regionHasNestedEscapeTo(loop.body_region, header),
        .latch_loop => |loop| structured_escape.regionHasNestedEscapeTo(loop.body_region, header),
        .infinite_loop => |loop| structured_escape.regionHasNestedEscapeTo(loop.body_region, header),
        else => false,
    };
}

fn emitLoopContinue(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    edge: ir.Edge,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) !void {
    try emitEdgeParametersUnlessConsumed(output, allocator, program, emission_plan, scopes, program.blocks[edge.target.index()], edge.arguments, indent, false, place_aliases);
}

fn emitProjectedContinue(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    edge: ir.Edge,
    target: ir.BlockId,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
    nonlocal: bool,
) (EmitError || std.mem.Allocator.Error)!void {
    const validated = try loop_continue_projection.validateEntry(program, target, edge);
    if (nonlocal) {
        try emitEdgeParametersUnlessConsumed(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            program.blocks[target.index()],
            validated.arguments,
            indent,
            false,
            place_aliases,
        );
        try emitEscapeFlagSet(output, allocator, program, emission_plan, target, indent);
        return;
    }
    try emitEdgeParametersUnlessConsumed(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        program.blocks[target.index()],
        validated.arguments,
        indent,
        false,
        place_aliases,
    );
    try emitContinueStatement(output, allocator, indent);
}

fn emitProjectedContinueAfterTransferredEdge(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    edge: ir.Edge,
    target: ir.BlockId,
    indent: []const u8,
) (EmitError || std.mem.Allocator.Error)!void {
    _ = try loop_continue_projection.validateEntry(program, target, edge);
    try emitContinueStatement(output, allocator, indent);
}

fn emitContinueStatement(output: *std.ArrayList(u8), allocator: std.mem.Allocator, indent: []const u8) std.mem.Allocator.Error!void {
    const transfer_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(transfer_indent);
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "do\n");
    try output.appendSlice(allocator, transfer_indent);
    try output.appendSlice(allocator, "continue\n");
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

fn edgeTransferIsStructurallyEmpty(program: *const ir.Program, scopes: *const emission_scope.Plan, edge: ir.Edge) bool {
    return scopes.nativeIterationConsumesParameters(edge.target) or
        (edge.arguments.len == 0 and program.blocks[edge.target.index()].parameters.len == 0);
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

fn emitScopeDeclarations(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    scope: emission_scope.ScopeId,
    indent: []const u8,
) !void {
    var bare_count: usize = 0;
    for (scopes.function.local_places) |place_id| {
        if (emission_plan.names.placeUsesStorage(place_id)) {
            if (scopes.placeScope(place_id) != scope or scopes.placeDeclaredAtInstruction(place_id)) continue;
            try flushBareDeclarations(output, allocator, &bare_count);
            try output.appendSlice(allocator, indent);
            try place_render.emitName(output, allocator, &emission_plan.names, program, place_id, &.{});
            try output.appendSlice(allocator, " = ");
            if (scopes.placeMovedLiteralInitializer(place_id)) |literal| {
                try render.literal(output, allocator, literal);
            } else {
                try output.appendSlice(allocator, "nil");
            }
            try output.append(allocator, '\n');
            continue;
        }
        if (scopes.placeScope(place_id) != scope or scopes.placeDeclaredAtInstruction(place_id)) continue;
        if (scopes.placeMovedLiteralInitializer(place_id)) |literal| {
            if (literal == .nil_value) {
                const name = emission_plan.names.place(place_id) orelse return error.UnsupportedOperation;
                try appendBareDeclaration(output, allocator, indent, name, &bare_count);
                continue;
            }
            try flushBareDeclarations(output, allocator, &bare_count);
            try output.appendSlice(allocator, indent);
            try output.appendSlice(allocator, "local ");
            try render.placeName(output, allocator, &emission_plan.names, place_id);
            try output.appendSlice(allocator, " = ");
            try render.literal(output, allocator, literal);
            try output.append(allocator, '\n');
        } else {
            const name = emission_plan.names.place(place_id) orelse return error.UnsupportedOperation;
            try appendBareDeclaration(output, allocator, indent, name, &bare_count);
        }
    }
    for (program.values) |value| {
        if (value.function != scopes.function.id or
            emission_plan.names.valueUsesStorage(value.id) or
            scopes.valueScope(value.id) != scope or
            scopes.valueDeclaredAtInstruction(value.id) or
            scopes.valueDeclaredAtSyntheticSite(value.id) or
            scopes.valueSuppressedByControl(value.id)) continue;
        const name = emission_plan.names.value(value.id) orelse return error.UnsupportedOperation;
        try appendBareDeclaration(output, allocator, indent, name, &bare_count);
    }
    for (program.value_packs) |pack| {
        if (pack.function != scopes.function.id or scopes.packScope(pack.id) != scope) continue;
        const name = emission_plan.names.valuePack(pack.id) orelse return error.UnsupportedOperation;
        try appendBareDeclaration(output, allocator, indent, name, &bare_count);
    }
    try flushBareDeclarations(output, allocator, &bare_count);
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

fn emitSemanticNormalizedTransition(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    instruction: ir.Instruction,
    operation: ir.NumericForNext,
    indent: []const u8,
    declare_results: bool,
    values: render.ValuePlan,
) !void {
    if (operation.mode != .semantic_normalized or instruction.results.len != 4) return error.UnsupportedOperation;
    const has_value = instruction.results[0];
    const normalized_limit = instruction.results[1];
    const normalized_step = instruction.results[2];
    const next_control = instruction.results[3];

    const any_storage = for (instruction.results) |res| {
        if (emission_plan.names.valueUsesStorage(res)) break true;
    } else false;
    if (declare_results and !any_storage) {
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "local ");
        for (instruction.results, 0..) |result, index| {
            if (index != 0) try output.appendSlice(allocator, ", ");
            try render.valueName(output, allocator, &emission_plan.names, result);
        }
        try output.append(allocator, '\n');
    }

    try output.appendSlice(allocator, indent);
    try render.valueName(output, allocator, &emission_plan.names, normalized_limit);
    try output.appendSlice(allocator, " = ");
    try render.valueUseScalar(output, allocator, program, values, operation.limit);
    try output.append(allocator, '\n');

    try output.appendSlice(allocator, indent);
    try render.valueName(output, allocator, &emission_plan.names, normalized_step);
    try output.appendSlice(allocator, " = ");
    try render.valueUseScalar(output, allocator, program, values, operation.step);
    try output.append(allocator, '\n');

    try output.appendSlice(allocator, indent);
    try render.valueName(output, allocator, &emission_plan.names, next_control);
    try output.appendSlice(allocator, " = ");
    try render.valueUseScalar(output, allocator, program, values, operation.control);
    try output.appendSlice(allocator, " + ");
    try render.valueName(output, allocator, &emission_plan.names, normalized_step);
    try output.append(allocator, '\n');

    const arm_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(arm_indent);
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "if ");
    try render.valueName(output, allocator, &emission_plan.names, normalized_step);
    try output.appendSlice(allocator, " <= 0 then\n");
    try output.appendSlice(allocator, arm_indent);
    try render.valueName(output, allocator, &emission_plan.names, has_value);
    try output.appendSlice(allocator, " = ");
    try render.valueName(output, allocator, &emission_plan.names, next_control);
    try output.appendSlice(allocator, " >= ");
    try render.valueName(output, allocator, &emission_plan.names, normalized_limit);
    try output.append(allocator, '\n');
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "else\n");
    try output.appendSlice(allocator, arm_indent);
    try render.valueName(output, allocator, &emission_plan.names, has_value);
    try output.appendSlice(allocator, " = ");
    try render.valueName(output, allocator, &emission_plan.names, next_control);
    try output.appendSlice(allocator, " <= ");
    try render.valueName(output, allocator, &emission_plan.names, normalized_limit);
    try output.append(allocator, '\n');
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

fn emitCompoundMemoryUpdate(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    instruction: ir.Instruction,
    update: compound_update.MemoryUpdate,
    indent: []const u8,
    values: render.ValuePlan,
) !void {
    _ = emission_plan;
    const needs_separator = render.statementNeedsSeparator(program, values, instruction.operation);
    var statement_indent = indent;
    var allocated_indent: ?[]u8 = null;
    defer if (allocated_indent) |value| allocator.free(value);

    if (needs_separator) {
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "do\n");
        allocated_indent = try allocDeeperIndent(allocator, indent);
        statement_indent = allocated_indent.?;
    }

    try output.appendSlice(allocator, statement_indent);
    switch (update.address) {
        .table => |address| try render.semanticTableAddress(output, allocator, program, values, address.table, address.key),
        .environment => |address| try render.semanticEnvironmentAddress(output, allocator, program, values, address.target, address.name),
    }
    try output.append(allocator, ' ');
    try output.appendSlice(allocator, render.compoundOperator(update.operator) orelse return error.UnsupportedOperation);
    try output.append(allocator, ' ');
    try render.valueUseScalar(output, allocator, program, values, update.right);
    try output.append(allocator, '\n');

    if (needs_separator) {
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "end\n");
    }
}

fn emitTableConstructorInstruction(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    instruction: ir.Instruction,
    constructor: ir.TableConstructor,
    indent: []const u8,
    declare_result: bool,
    values: render.ValuePlan,
) !void {
    if (instruction.results.len != 1 or instruction.results[0].index() >= program.values.len) return error.UnsupportedOperation;
    try output.appendSlice(allocator, indent);
    if (declare_result and !emission_plan.names.valueUsesStorage(instruction.results[0])) try output.appendSlice(allocator, "local ");
    try render.valueName(output, allocator, &emission_plan.names, instruction.results[0]);
    try output.appendSlice(allocator, " = {");

    const item_count = constructor.fields.len + @intFromBool(constructor.tail_pack != null);
    if (item_count == 0) {
        try output.appendSlice(allocator, "}\n");
        return;
    }

    const field_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(field_indent);
    try output.append(allocator, '\n');
    var item_index: usize = 0;
    for (constructor.fields, 0..) |field, field_index| {
        try output.appendSlice(allocator, field_indent);
        switch (field) {
            .list => |value| if (field_index + 1 < constructor.fields.len or constructor.tail_pack != null)
                try render.valueUseScalar(output, allocator, program, values, value)
            else
                try render.valueUseRoot(output, allocator, program, values, value),
            .keyed => |keyed| {
                try render.semanticConstructorKey(output, allocator, program, values, keyed.key);
                try output.appendSlice(allocator, " = ");
                try render.valueUseScalar(output, allocator, program, values, keyed.value);
            },
        }
        item_index += 1;
        if (item_index != item_count) try output.append(allocator, ',');
        try output.append(allocator, '\n');
    }
    if (constructor.tail_pack) |pack_id| {
        try output.appendSlice(allocator, field_indent);
        try emitTableConstructorTail(output, allocator, program, emission_plan, instruction.id, pack_id, values);
        try output.append(allocator, '\n');
    }
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "}\n");
}

fn emitTableConstructorTail(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    consumer: ir.InstructionId,
    pack_id: ir.ValuePackId,
    values: render.ValuePlan,
) !void {
    if (pack_id.index() >= program.value_packs.len) return error.UnsupportedOperation;
    switch (program.value_packs[pack_id.index()].origin) {
        .varargs => try render.directVarargPackExpression(output, allocator, program, values, pack_id),
        .instruction_result => |producer_id| {
            if (producer_id.index() >= program.instructions.len) return error.UnsupportedOperation;
            const producer = program.instructions[producer_id.index()];
            switch (producer.operation) {
                .pack_values => {
                    if (!emission_plan.packs.packValuesServesInstruction(producer_id, consumer)) return error.UnsupportedOperation;
                    try render.plannedPackValues(output, allocator, program, values, producer);
                },
                else => {
                    if (emission_plan.packs.storedPackServesInstruction(producer_id, consumer)) {
                        try render.storedPackExpansion(output, allocator, values, pack_id);
                        return;
                    }
                    const fused_consumer = switch (emission_plan.packs.role(producer_id)) {
                        .fused_invocation_producer => |value| value,
                        else => return error.UnsupportedOperation,
                    };
                    if (fused_consumer != consumer) return error.UnsupportedOperation;
                    try render.plannedInvocation(output, allocator, program, values, &emission_plan.packs, producer);
                },
            }
        },
    }
}

fn emitTableSetPackInstruction(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    instruction: ir.Instruction,
    operation: ir.TableSetPack,
    indent: []const u8,
    values: render.ValuePlan,
) !void {
    const statement_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(statement_indent);
    const loop_indent = try allocDeeperIndent(allocator, statement_indent);
    defer allocator.free(loop_indent);
    const body_indent = try allocDeeperIndent(allocator, loop_indent);
    defer allocator.free(body_indent);

    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "do\n");
    try output.appendSlice(allocator, statement_indent);
    try output.appendSlice(allocator, "(function(__lifter_pack_table_");
    try output.print(allocator, "{d}", .{instruction.id.index()});
    try output.appendSlice(allocator, ", __lifter_pack_first_");
    try output.print(allocator, "{d}", .{instruction.id.index()});
    try output.appendSlice(allocator, ", ...)\n");

    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "for __lifter_pack_offset_");
    try output.print(allocator, "{d}", .{instruction.id.index()});
    try output.appendSlice(allocator, " = 0, ");
    try render.runtimeCallStart(output, allocator, values, .select);
    try output.appendSlice(allocator, "\"#\", ...) - 1 do\n");

    try output.appendSlice(allocator, body_indent);
    try render.runtimeCallStart(output, allocator, values, .rawset);
    try output.appendSlice(allocator, "__lifter_pack_table_");
    try output.print(allocator, "{d}", .{instruction.id.index()});
    try output.appendSlice(allocator, ", __lifter_pack_first_");
    try output.print(allocator, "{d}", .{instruction.id.index()});
    try output.appendSlice(allocator, " + __lifter_pack_offset_");
    try output.print(allocator, "{d}", .{instruction.id.index()});
    try output.appendSlice(allocator, ", (");
    try render.runtimeCallStart(output, allocator, values, .select);
    try output.appendSlice(allocator, "__lifter_pack_offset_");
    try output.print(allocator, "{d}", .{instruction.id.index()});
    try output.appendSlice(allocator, " + 1, ...)))\n");

    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "end\n");
    try output.appendSlice(allocator, statement_indent);
    try output.appendSlice(allocator, "end)(");
    try render.valueUseScalar(output, allocator, program, values, operation.table);
    try output.print(allocator, ", {d}, ", .{operation.first_index});
    try emitTableConstructorTail(output, allocator, program, emission_plan, instruction.id, operation.pack, values);
    try output.appendSlice(allocator, ")\n");
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

fn emitCallRepeatedTableGetInstruction(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    instruction: ir.Instruction,
    operation: ir.CallRepeatedTableGet,
    indent: []const u8,
    declare_results: bool,
    place_aliases: []const PlaceAlias,
    values: render.ValuePlan,
) !void {
    const result_count = switch (operation.result_arity) {
        .fixed => |count| @as(usize, count),
        .variadic => return error.UnsupportedOperation,
    };
    if (result_count != instruction.results.len or instruction.pack_result != null) return error.UnsupportedOperation;

    const statement_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(statement_indent);
    const loop_indent = try allocDeeperIndent(allocator, statement_indent);
    defer allocator.free(loop_indent);
    const body_indent = try allocDeeperIndent(allocator, loop_indent);
    defer allocator.free(body_indent);

    try output.appendSlice(allocator, indent);
    if (instruction.results.len != 0) {
        const any_storage = for (instruction.results) |res| {
            if (emission_plan.names.valueUsesStorage(res)) break true;
        } else false;
        if (declare_results and !any_storage) try output.appendSlice(allocator, "local ");
        for (instruction.results, 0..) |result, index| {
            if (index != 0) try output.appendSlice(allocator, ", ");
            try render.valueName(output, allocator, &emission_plan.names, result);
        }
        try output.appendSlice(allocator, " = ");
    }
    try output.appendSlice(allocator, "(function(__lifter_repeated_callee_");
    try output.print(allocator, "{d}", .{instruction.id.index()});
    for (operation.prefix_arguments, 0..) |_, index| {
        try output.appendSlice(allocator, ", __lifter_repeated_prefix_");
        try output.print(allocator, "{d}_{d}", .{ instruction.id.index(), index });
    }
    try output.appendSlice(allocator, ", __lifter_repeated_table_");
    try output.print(allocator, "{d}, __lifter_repeated_key_", .{instruction.id.index()});
    try output.print(allocator, "{d}, __lifter_repeated_from_", .{instruction.id.index()});
    try output.print(allocator, "{d}, __lifter_repeated_to_", .{instruction.id.index()});
    try output.print(allocator, "{d}, __lifter_repeated_step_", .{instruction.id.index()});
    try output.print(allocator, "{d})\n", .{instruction.id.index()});

    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "local __lifter_repeated_values_");
    try output.print(allocator, "{d} = {{}}\n", .{instruction.id.index()});
    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "local __lifter_repeated_count_");
    try output.print(allocator, "{d} = 0\n", .{instruction.id.index()});

    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "for __lifter_repeated_cursor_");
    try output.print(allocator, "{d} = __lifter_repeated_from_", .{instruction.id.index()});
    try output.print(allocator, "{d}, __lifter_repeated_to_", .{instruction.id.index()});
    try output.print(allocator, "{d}, __lifter_repeated_step_", .{instruction.id.index()});
    try output.print(allocator, "{d} do\n", .{instruction.id.index()});

    try output.appendSlice(allocator, body_indent);
    try output.appendSlice(allocator, "__lifter_repeated_values_");
    try output.print(allocator, "{d}[__lifter_repeated_count_", .{instruction.id.index()});
    try output.print(allocator, "{d} + 1] = __lifter_repeated_table_", .{instruction.id.index()});
    try output.print(allocator, "{d}[__lifter_repeated_key_", .{instruction.id.index()});
    try output.print(allocator, "{d}]\n", .{instruction.id.index()});
    try output.appendSlice(allocator, body_indent);
    try output.appendSlice(allocator, "__lifter_repeated_count_");
    try output.print(allocator, "{d} = __lifter_repeated_count_", .{instruction.id.index()});
    try output.print(allocator, "{d} + 1\n", .{instruction.id.index()});
    if (operation.counter) |counter| {
        try emitRepeatedTableGetCounterIncrement(
            output,
            allocator,
            program,
            emission_plan,
            values,
            counter,
            body_indent,
            place_aliases,
        );
    }
    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "end\n");

    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "return __lifter_repeated_callee_");
    try output.print(allocator, "{d}(", .{instruction.id.index()});
    for (operation.prefix_arguments, 0..) |_, index| {
        if (index != 0) try output.appendSlice(allocator, ", ");
        try output.appendSlice(allocator, "__lifter_repeated_prefix_");
        try output.print(allocator, "{d}_{d}", .{ instruction.id.index(), index });
    }
    if (operation.prefix_arguments.len != 0) try output.appendSlice(allocator, ", ");
    try render.runtimeCallStart(output, allocator, values, .table_unpack);
    try output.appendSlice(allocator, "__lifter_repeated_values_");
    try output.print(allocator, "{d}, 1, __lifter_repeated_count_", .{instruction.id.index()});
    try output.print(allocator, "{d}))\n", .{instruction.id.index()});

    try output.appendSlice(allocator, statement_indent);
    try output.appendSlice(allocator, "end)(");
    try render.valueUseScalar(output, allocator, program, values, operation.callee);
    for (operation.prefix_arguments) |argument| {
        try output.appendSlice(allocator, ", ");
        try render.valueUseScalar(output, allocator, program, values, argument);
    }
    const range_values = [_]ir.ValueId{ operation.table, operation.key, operation.from, operation.to, operation.step };
    for (range_values) |value| {
        try output.appendSlice(allocator, ", ");
        try render.valueUseScalar(output, allocator, program, values, value);
    }
    try output.appendSlice(allocator, ")\n");
}

fn emitRepeatedTableGetCounterIncrement(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    values: render.ValuePlan,
    counter: ir.PlaceId,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) !void {
    const resolved = place_render.resolve(counter, place_aliases) orelse return error.UnsupportedOperation;
    try output.appendSlice(allocator, indent);
    switch (resolved) {
        .place => {
            try lexical.emitPlaceName(output, allocator, &emission_plan.names, program, counter, place_aliases);
            try output.appendSlice(allocator, " = ");
            try lexical.emitPlaceName(output, allocator, &emission_plan.names, program, counter, place_aliases);
            try output.appendSlice(allocator, " + 1\n");
        },
        .external_binding => |binding_id| {
            try render.runtimeCallStart(output, allocator, values, .rawset);
            try place_render.emitExternalBindingName(output, allocator, &emission_plan.names, binding_id);
            try output.appendSlice(allocator, ", 1, ");
            try render.runtimeCallStart(output, allocator, values, .rawget);
            try place_render.emitExternalBindingName(output, allocator, &emission_plan.names, binding_id);
            try output.appendSlice(allocator, ", 1) + 1)\n");
        },
    }
}

fn emitScopedClosureDestinationDeclaration(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    destination: ClosureDestination,
    indent: []const u8,
    parent_place_aliases: []const PlaceAlias,
) !void {
    switch (destination) {
        .value => |value| {
            if (!value.declare) return;
            if (value.id.index() >= program.values.len) return error.UnsupportedOperation;
            if (emission_plan.names.valueUsesStorage(value.id)) return;
            try output.appendSlice(allocator, indent);
            try output.appendSlice(allocator, "local ");
            try render.valueName(output, allocator, &emission_plan.names, value.id);
            try output.append(allocator, '\n');
        },
        .place => |place| {
            if (!place.declare) return;
            const resolved = place_render.resolve(place.id, parent_place_aliases) orelse return error.UnsupportedOperation;
            if (resolved != .place) return error.UnsupportedOperation;
            if (emission_plan.names.placeUsesStorage(resolved.place)) return;
            try output.appendSlice(allocator, indent);
            try output.appendSlice(allocator, "local ");
            try lexical.emitPlaceName(output, allocator, &emission_plan.names, program, place.id, parent_place_aliases);
            try output.append(allocator, '\n');
        },
        .table, .environment => {},
    }
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
