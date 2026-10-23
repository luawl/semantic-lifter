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
const stage_trace = @import("stage_trace.zig");

pub const EmitError = error{
    InvalidIr,
    UnsupportedShape,
    UnsupportedControlFlow,
    UnsupportedOperation,
};

const PlaceAlias = lexical.PlaceAlias;

const EmissionPlan = emission_planning.Plan;
const NativeIterationCompletion = emission_planning.NativeIterationCompletion;
const ContinueBinder = emission_planning.ContinueBinder;

const ContainerGroupWrapper = struct {
    output_start: usize,
    body_start: usize,
};

pub const Target = luau_runtime.Target;

pub const Options = struct {
    force_dispatcher: bool = false,
    /// Target-family ambient helpers: the emitter records each one on its
    /// runtime plan with `luau_runtime.Plan.requireAmbientHelper` and defines it
    /// only when the program reads its name. Neutral emission passes none.
    ambient_helpers: []const luau_runtime.AmbientHelper = &.{},
};

const StableCaptureValues = struct {
    scopes: *const emission_scope.Plan,

    pub fn contains(self: StableCaptureValues, value_id: ir.ValueId) bool {
        return self.scopes.valueHasStableLexicalBinding(value_id);
    }

    pub fn isBoxedPlace(self: StableCaptureValues, place_id: ir.PlaceId) bool {
        return self.scopes.arbitraryPlaceNeedsPerExecutionCell(place_id);
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

/// Convenience entry point for focused tests and embedders that explicitly
/// operate on the standard-Luau runtime contract.
pub fn emitStandardLuauAlloc(allocator: std.mem.Allocator, program: *const ir.Program) (EmitError || std.mem.Allocator.Error)![]u8 {
    return emitAllocForTarget(allocator, program, .standard_luau);
}

pub fn emitAllocForTarget(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    target: Target,
) (EmitError || std.mem.Allocator.Error)![]u8 {
    return emitAllocForTargetWithOptions(allocator, program, target, .{});
}

pub fn emitAllocForTargetWithOptions(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    target: Target,
    options: Options,
) (EmitError || std.mem.Allocator.Error)![]u8 {
    var report = try validation.validateForTargetWithStrategy(
        allocator,
        program,
        .readable_luau,
        target,
        if (options.force_dispatcher) .dispatcher else .automatic,
    );
    defer report.deinit();
    if (!report.isClean()) return error.InvalidIr;
    return emitAdmittedAllocForTargetWithOptions(allocator, program, target, options);
}

/// Emit an IR program after its readable-Luau admission has already been
/// checked by the caller. The public entry point above remains self-validating
/// for direct embedders; the pipeline uses this boundary to avoid validating
/// a large admitted program twice.
pub fn emitAdmittedAllocForTarget(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    target: Target,
) (EmitError || std.mem.Allocator.Error)![]u8 {
    return emitAdmittedAllocForTargetWithOptions(allocator, program, target, .{});
}

pub fn emitAdmittedAllocForTargetWithOptions(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    target: Target,
    options: Options,
) (EmitError || std.mem.Allocator.Error)![]u8 {
    var transfer_arena = std.heap.ArenaAllocator.init(allocator);
    defer transfer_arena.deinit();
    const prepared = lexical_transfer.prepareInArena(transfer_arena.allocator(), program) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.UnsupportedControlFlow => return error.UnsupportedControlFlow,
        error.UnsupportedTransfer => return error.UnsupportedOperation,
    };
    const emission_program = &prepared;
    var emission_plan = try EmissionPlan.init(allocator, emission_program, target);
    defer emission_plan.deinit();
    for (options.ambient_helpers) |helper| emission_plan.runtime.requireAmbientHelper(helper);
    var entry_plan = lexical.EntryPlan.init(allocator, emission_program) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.InvalidEntryBinding => return error.UnsupportedOperation,
    };
    defer entry_plan.deinit();

    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);

    try emitRuntimePrelude(&output, allocator, &emission_plan, emission_program);

    for (emission_program.functions) |function| {
        if (function.id == emission_program.entry_function or function.lexical_parent != null) continue;
        try output.appendSlice(allocator, "local ");
        try render.functionName(&output, allocator, &emission_plan.names, function.id);
        try output.append(allocator, '\n');
    }

    var wrote_function = false;
    for (emission_program.functions) |function| {
        if (function.id == emission_program.entry_function or function.lexical_parent != null) continue;
        if (wrote_function) try output.append(allocator, '\n');
        emission_plan.force_dispatcher = options.force_dispatcher or try functionNeedsArbitraryFallback(
            allocator,
            program,
            function.id,
        );
        emitFunction(&output, allocator, emission_program, &emission_plan, function) catch |err| {
            std.debug.print("emit function={} error={s}\n", .{ function.id.index(), @errorName(err) });
            return err;
        };
        wrote_function = true;
    }

    if (wrote_function) try output.append(allocator, '\n');
    const entry = emission_program.functions[emission_program.entry_function.index()];
    emission_plan.force_dispatcher = options.force_dispatcher or try functionNeedsArbitraryFallback(
        allocator,
        program,
        entry.id,
    );
    try emitEntryParameters(&output, allocator, emission_program, &emission_plan, entry);
    try emitEntryValueBindings(&output, allocator, &emission_plan, entry_plan.value_bindings);
    emitFunctionBody(&output, allocator, emission_program, &emission_plan, entry, "", entry_plan.place_aliases) catch |err| {
        std.debug.print("emit entry_function={} error={s}\n", .{ entry.id.index(), @errorName(err) });
        return err;
    };

    return output.toOwnedSlice(allocator);
}

/// Bounded backend probe for an already-admitted function. This uses the same
/// prepared program and emission plan as full publication while avoiding a
/// whole-program traversal during renderer diagnosis.
pub fn emitAdmittedFunctionAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    target: Target,
    function_id: ir.FunctionId,
) (EmitError || std.mem.Allocator.Error)![]u8 {
    var transfer_arena = std.heap.ArenaAllocator.init(allocator);
    defer transfer_arena.deinit();
    const prepared = lexical_transfer.prepareInArena(transfer_arena.allocator(), program) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.UnsupportedControlFlow => return error.UnsupportedControlFlow,
        error.UnsupportedTransfer => return error.UnsupportedOperation,
    };
    if (function_id.index() >= prepared.functions.len) return error.UnsupportedOperation;
    var emission_plan = try EmissionPlan.init(allocator, &prepared, target);
    defer emission_plan.deinit();
    emission_plan.force_dispatcher = try functionNeedsArbitraryFallback(allocator, program, function_id);

    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try emitRuntimePrelude(&output, allocator, &emission_plan, &prepared);
    try emitFunction(&output, allocator, &prepared, &emission_plan, prepared.functions[function_id.index()]);
    return output.toOwnedSlice(allocator);
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

    // Ambient helpers are target-family runtime definitions that a frontend
    // recorded on the runtime plan (luau_runtime.Plan.requireAmbientHelper).
    // The neutral core records none, so no ambient name has special meaning
    // here: a recorded helper is defined once, and only when the program reads
    // its name through a semantic ambient environment_get.
    for (emission_plan.runtime.ambient_helpers) |helper| {
        var referenced = false;
        for (program.instructions) |instruction| {
            switch (instruction.operation) {
                .environment_get => |get| {
                    if (get.mode != .semantic) continue;
                    switch (get.target) {
                        .ambient => {
                            if (std.mem.eql(u8, get.name, helper.name)) {
                                referenced = true;
                            }
                        },
                        .value => {},
                    }
                },
                else => {},
            }
            if (referenced) break;
        }
        if (referenced) try output.appendSlice(allocator, helper.source);
    }
}

fn emitFunction(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, emission_plan: *const EmissionPlan, function: ir.Function) !void {
    try render.functionName(output, allocator, &emission_plan.names, function.id);
    try output.appendSlice(allocator, " = function(");
    try emitFunctionParameters(output, allocator, emission_plan, function);
    try output.appendSlice(allocator, ")\n");
    try emitFunctionBody(output, allocator, program, emission_plan, function, "  ", &.{});
    try output.appendSlice(allocator, "end\n");
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

fn emitFunctionBody(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    function: ir.Function,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    // A nested function's continues bind only to that function's own loops.
    const enclosing_binder = emission_plan.state.continue_binder;
    emission_plan.state.continue_binder = null;
    defer emission_plan.state.continue_binder = enclosing_binder;
    var analysis = cfg.Analysis.init(allocator, program, function) catch |err| {
        std.debug.print("emit function={} stage=cfg error={s}\n", .{ function.id.index(), @errorName(err) });
        return error.UnsupportedControlFlow;
    };
    defer analysis.deinit();
    var plan = (if (emission_plan.force_dispatcher)
        structure.Plan.initArbitrary(allocator, &analysis)
    else
        structure.Plan.initWithArbitraryFallback(allocator, &analysis)) catch |err| {
        std.debug.print("emit function={} stage=structure error={s}\n", .{ function.id.index(), @errorName(err) });
        return error.UnsupportedControlFlow;
    };
    defer plan.deinit();
    var scopes = emission_scope.Plan.init(
        allocator,
        program,
        function,
        &analysis,
        &plan,
        &emission_plan.packs,
        &emission_plan.dead,
        &emission_plan.place_writes,
        &emission_plan.place_reads,
        &emission_plan.fused_values,
        &emission_plan.closure_stores,
    ) catch |err| {
        std.debug.print("emit function={} stage=scopes error={s}\n", .{ function.id.index(), @errorName(err) });
        return err;
    };
    defer scopes.deinit();
    if (!plan.root.arbitrary_cfg) {
        branch_expression.markDeclarations(program, emission_plan, &scopes, plan.root, true);
    }
    if (emission_plan.names.functionUsesValueStorage(program, function)) {
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "local ");
        try output.appendSlice(allocator, emission_plan.names.valueStorageName() orelse return error.UnsupportedOperation);
        try output.appendSlice(allocator, " = {}\n");
    }
    if (emission_plan.names.functionUsesStorage(function)) {
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "local ");
        try output.appendSlice(allocator, emission_plan.names.placeStorageName() orelse return error.UnsupportedOperation);
        try output.appendSlice(allocator, " = {}\n");
    }
    if (plan.root.arbitrary_cfg) {
        try emitArbitraryCfgDeclarations(output, allocator, program, emission_plan, &scopes, function, indent);
        const body_aliases = try arbitraryBodyPlaceAliases(allocator, program, &scopes, function, place_aliases);
        defer allocator.free(body_aliases);
        emitArbitraryCfgBody(output, allocator, program, emission_plan, &scopes, plan.root, indent, body_aliases) catch |err| {
            std.debug.print("emit function={} stage=arbitrary_cfg error={s}\n", .{ function.id.index(), @errorName(err) });
            return err;
        };
        trimTrailingEmptyReturn(output, indent);
        return;
    }
    const body_start = output.items.len;
    const root_escape_targets = try structured_escape.regionFreeTargetsAlloc(allocator, plan.root);
    defer allocator.free(root_escape_targets);
    const loop_boundary_exit_targets = try structured_escape.loopBoundaryExitTargetsAlloc(allocator, plan.root);
    defer allocator.free(loop_boundary_exit_targets);
    for (root_escape_targets) |target| {
        try emitEscapeFlagDeclaration(output, allocator, program, emission_plan, target, indent);
    }
    for (loop_boundary_exit_targets) |target| {
        if (containsBlockId(root_escape_targets, target)) continue;
        try emitEscapeFlagDeclaration(output, allocator, program, emission_plan, target, indent);
    }
    emitScopeDeclarations(output, allocator, program, emission_plan, &scopes, scopes.rootScope(), indent) catch |err| {
        std.debug.print("emit function={} stage=root_declarations error={s}\n", .{ function.id.index(), @errorName(err) });
        return err;
    };
    emitRegion(output, allocator, program, emission_plan, &scopes, plan.root, indent, place_aliases) catch |err| {
        if (err == error.UnsupportedControlFlow) {
            output.items.len = body_start;
            plan.deinit();
            plan = try structure.Plan.initArbitrary(allocator, &analysis);
            scopes.deinit();
            scopes = try emission_scope.Plan.init(
                allocator,
                program,
                function,
                &analysis,
                &plan,
                &emission_plan.packs,
                &emission_plan.dead,
                &emission_plan.place_writes,
                &emission_plan.place_reads,
                &emission_plan.fused_values,
                &emission_plan.closure_stores,
            );
            try emitArbitraryCfgDeclarations(output, allocator, program, emission_plan, &scopes, function, indent);
            const body_aliases = try arbitraryBodyPlaceAliases(allocator, program, &scopes, function, place_aliases);
            defer allocator.free(body_aliases);
            try emitArbitraryCfgBody(output, allocator, program, emission_plan, &scopes, plan.root, indent, body_aliases);
            trimTrailingEmptyReturn(output, indent);
            return;
        }
        return err;
    };
    trimTrailingEmptyReturn(output, indent);
}

// The flat (dispatcher) layout renders every non-allocation use of a boxed per-execution cell through its
// holder's `[1]` slot. A terminal self-alias per boxed place makes `place_render.resolve`
// report `.boxed_cell`, the same path a captured boxed cell is reached through in a child. Returns a freshly
// allocated list the caller frees: the parent aliases followed by one self-alias per boxed place.
fn arbitraryBodyPlaceAliases(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scopes: *const emission_scope.Plan,
    function: ir.Function,
    place_aliases: []const PlaceAlias,
) std.mem.Allocator.Error![]PlaceAlias {
    var boxed_count: usize = 0;
    for (function.local_places) |place_id| {
        if (place_id.index() >= program.places.len) continue;
        if (scopes.arbitraryPlaceNeedsPerExecutionCell(place_id)) boxed_count += 1;
    }
    const aliases = try allocator.alloc(PlaceAlias, place_aliases.len + boxed_count);
    @memcpy(aliases[0..place_aliases.len], place_aliases);
    var next = place_aliases.len;
    for (function.local_places) |place_id| {
        if (place_id.index() >= program.places.len) continue;
        if (!scopes.arbitraryPlaceNeedsPerExecutionCell(place_id)) continue;
        aliases[next] = .{ .boxed_place = .{ .captured = place_id, .holder = place_id } };
        next += 1;
    }
    return aliases;
}

// A reducible region is preferred for readable output.  When the CFG remains
// irreducible after authenticated normalization, preserve it with a balanced
// dispatcher whose leaves execute the original blocks and edge transfers.
fn emitArbitraryCfgBody(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    region: *const structure.Region,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    if (!region.arbitrary_cfg or region.nodes.len == 0) return error.UnsupportedControlFlow;
    const pc_name = try emission_plan.names.internalNameAlloc(allocator, program, "__lifter_pc");
    defer allocator.free(pc_name);

    const entry = scopes.function.entry_block;
    if (entry.index() >= program.blocks.len) return error.UnsupportedControlFlow;
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "local ");
    try output.appendSlice(allocator, pc_name);
    try output.appendSlice(allocator, " = ");
    try output.print(allocator, "{d}\n", .{entry.index()});

    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "while true do\n");
    const body_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(body_indent);
    try emitArbitraryDispatch(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        region.nodes,
        0,
        region.nodes.len,
        pc_name,
        body_indent,
        place_aliases,
    );
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

fn emitArbitraryDispatch(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    nodes: []const structure.Node,
    start: usize,
    end: usize,
    pc_name: []const u8,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    if (start >= end) return error.UnsupportedControlFlow;
    if (end - start == 1) {
        const block_id = nodes[start].blockId();
        if (block_id.index() >= program.blocks.len) return error.UnsupportedControlFlow;
        const block = program.blocks[block_id.index()];
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "if ");
        try output.appendSlice(allocator, pc_name);
        try output.appendSlice(allocator, " == ");
        try output.print(allocator, "{d} then\n", .{block_id.index()});
        const leaf_indent = try allocDeeperIndent(allocator, indent);
        defer allocator.free(leaf_indent);
        try emitArbitraryBlockInstructions(output, allocator, program, emission_plan, scopes, block, leaf_indent, place_aliases);
        try emitArbitraryTerminator(output, allocator, program, emission_plan, scopes, block, pc_name, leaf_indent, place_aliases);
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "else\n");
        const error_indent = try allocDeeperIndent(allocator, indent);
        defer allocator.free(error_indent);
        try output.appendSlice(allocator, error_indent);
        try output.appendSlice(allocator, "error(\"invalid control state\")\n");
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "end\n");
        return;
    }

    const middle = start + (end - start) / 2;
    const pivot = nodes[middle - 1].blockId().index();
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "if ");
    try output.appendSlice(allocator, pc_name);
    try output.appendSlice(allocator, " <= ");
    try output.print(allocator, "{d} then\n", .{pivot});
    const nested_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(nested_indent);
    try emitArbitraryDispatch(output, allocator, program, emission_plan, scopes, nodes, start, middle, pc_name, nested_indent, place_aliases);
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "else\n");
    try emitArbitraryDispatch(output, allocator, program, emission_plan, scopes, nodes, middle, end, pc_name, nested_indent, place_aliases);
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

/// Count the root list plus the places declared at their allocation leaf, an
/// upper bound on the `local` names declared for the arbitrary-CFG
/// (dispatcher) layout of `function`: every non-storage, non-capture local
/// place (one that `emission_scope.Plan.arbitraryLeafDeclaresPlace` marks is
/// declared at its allocation inside its block's leaf instead of in the root
/// list of `emitArbitraryCfgDeclarations`, and keeps its slot here), every
/// named non-storage block-parameter/instruction-result value, and every named
/// value pack. The register validator budgets this flat count (plus the
/// `__lifter_pc` slot) against the compiler's local-register limit so a
/// forced-dispatcher layout is certified consistently with what is emitted
/// (the dispatcher budget). Keep this in lockstep with `emitArbitraryCfgDeclarations` below.
pub fn arbitraryDeclarationCount(
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    function: ir.Function,
) usize {
    var count: usize = 0;
    for (function.local_places) |place_id| {
        if (place_id.index() >= program.places.len or emission_plan.names.placeUsesStorage(place_id)) continue;
        const place = program.places[place_id.index()];
        switch (place.origin) {
            .local, .instruction => {},
            .capture => continue,
        }
        if (emission_plan.names.place(place_id) != null) count += 1;
    }
    for (program.values) |value| {
        if (value.function != function.id) continue;
        if (emission_plan.names.valueUsesStorage(value.id)) continue;
        switch (value.origin) {
            .parameter, .capture => continue,
            .block_parameter, .instruction_result => {},
        }
        if (emission_plan.names.value(value.id) != null) count += 1;
    }
    for (program.value_packs) |pack| {
        if (pack.function != function.id) continue;
        if (emission_plan.names.valuePack(pack.id) != null) count += 1;
    }
    return count;
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
        // A boxed per-execution cell keeps its holder in the root `local` list, declared
        // once per activation; the allocating origin write reassigns it to a fresh box per execution.
        // Declared at its allocation, inside the allocating block's leaf.
        if (scopes.arbitraryLeafDeclaresPlace(place_id)) continue;
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

fn emitArbitraryBlockInstructions(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    block: ir.Block,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return error.UnsupportedOperation;
        const instruction = program.instructions[instruction_id.index()];
        const declares_place = switch (instruction.operation) {
            .place_write => |write| scopes.arbitraryLeafDeclaresPlace(write.place) and
                program.places[write.place.index()].origin == .instruction and
                program.places[write.place.index()].origin.instruction == instruction_id,
            else => false,
        };
        emitInstruction(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            program.instructions[instruction_id.index()],
            indent,
            false,
            declares_place,
            place_aliases,
            null,
        ) catch |err| {
            std.debug.print("emit arbitrary instruction={} block={} operation={s} error={s}\n", .{
                instruction_id.index(),
                block.id.index(),
                @tagName(program.instructions[instruction_id.index()].operation),
                @errorName(err),
            });
            return err;
        };
    }
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

fn emitBlockInstructions(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, emission_plan: *const EmissionPlan, scopes: *const emission_scope.Plan, block: ir.Block, indent: []const u8, place_aliases: []const PlaceAlias) !void {
    try emitBlockInstructionsWithDeclaration(output, allocator, program, emission_plan, scopes, block, indent, true, place_aliases, null);
}

fn emitBlockInstructionsWithDeclaration(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, emission_plan: *const EmissionPlan, scopes: *const emission_scope.Plan, block: ir.Block, indent: []const u8, declare_results: bool, place_aliases: []const PlaceAlias, composition: ?*const branch_expression.Composition) !void {
    _ = declare_results;
    var index: usize = 0;
    while (index < block.instructions.len) {
        const first_id = block.instructions[index];
        const scope = scopes.instructionScope(first_id) orelse return error.UnsupportedControlFlow;
        var end = index + 1;
        while (end < block.instructions.len and scopes.instructionScope(block.instructions[end]) == scope) : (end += 1) {}

        var has_output = scopes.declarationCount(scope) != 0;
        if (!has_output) {
            for (block.instructions[index..end]) |instruction_id| {
                if (composition) |value| {
                    if (value.instructionIsAbsorbed(instruction_id)) continue;
                }
                if (scopes.instructionSuppressedByControl(instruction_id)) continue;
                const instruction = program.instructions[instruction_id.index()];
                if (emission_plan.instructionMayEmit(instruction) and !scopes.instructionIsMovedLiteralInitializer(instruction.id)) {
                    has_output = true;
                    break;
                }
            }
        }
        if (has_output) {
            const block_scope = scopes.blockScope(block.id) orelse return error.UnsupportedControlFlow;
            const wraps_segment = scope != block_scope;
            var allocated_indent: ?[]u8 = null;
            defer if (allocated_indent) |value| allocator.free(value);
            if (wraps_segment) {
                try output.appendSlice(allocator, indent);
                try output.appendSlice(allocator, "do\n");
                allocated_indent = try allocDeeperIndent(allocator, indent);
                try emitScopeDeclarations(output, allocator, program, emission_plan, scopes, scope, allocated_indent.?);
            }
            const segment_indent = allocated_indent orelse indent;
            for (block.instructions[index..end]) |instruction_id| {
                if (scopes.instructionSuppressedByControl(instruction_id)) continue;
                const instruction = program.instructions[instruction_id.index()];
                const declares_place = switch (instruction.operation) {
                    .place_write => |write| !emission_plan.names.placeUsesStorage(write.place) and
                        scopes.instructionDeclaresPlace(instruction_id, write.place),
                    else => false,
                };
                emitInstruction(
                    output,
                    allocator,
                    program,
                    emission_plan,
                    scopes,
                    instruction,
                    segment_indent,
                    scopes.instructionDeclaresResults(instruction_id),
                    declares_place,
                    place_aliases,
                    composition,
                ) catch |err| {
                    std.debug.print("emit instruction={} block={} operation={s} error={s}\n", .{
                        instruction.id.index(),
                        block.id.index(),
                        @tagName(instruction.operation),
                        @errorName(err),
                    });
                    return err;
                };
            }
            if (wraps_segment) {
                try output.appendSlice(allocator, indent);
                try output.appendSlice(allocator, "end\n");
            }
        }
        index = end;
    }
}

fn emitRegion(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    region: *const structure.Region,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    return emitRegionPredeclared(output, allocator, program, emission_plan, scopes, region, indent, place_aliases, null);
}

/// `emitRegion` with a block whose escape flag is not the region's to declare (`predeclared_block`): when the region
/// is written inside a transfer wrapper that stops there, the wrapper declares no flag of that name, so a set of
/// the flag after the region's text reaches the flag that the owner of that block declares.
fn emitRegionPredeclared(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    region: *const structure.Region,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
    predeclared_block: ?ir.BlockId,
) (EmitError || std.mem.Allocator.Error)!void {
    emitRegionWithPredeclaredBlock(output, allocator, program, emission_plan, scopes, region, indent, place_aliases, predeclared_block) catch |err| {
        std.debug.print(
            "emit region error={s} node={s} first={?d} last={?d} nodes={d} stop={?d} loop_exit={?d} continue_target={?d}\n",
            .{
                @errorName(err),
                if (region.nodes.len == 0) "empty" else @tagName(region.nodes[0]),
                if (region.nodes.len == 0) null else region.nodes[0].blockId().index(),
                if (region.nodes.len == 0) null else region.nodes[region.nodes.len - 1].blockId().index(),
                region.nodes.len,
                if (region.stop) |block| block.index() else null,
                if (region.loop_exit) |block| block.index() else null,
                if (region.continue_target) |block| block.index() else null,
            },
        );
        return err;
    };
}

fn emitRegionWithPredeclaredBlock(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    region: *const structure.Region,
    region_indent: []const u8,
    place_aliases: []const PlaceAlias,
    predeclared_block: ?ir.BlockId,
) (EmitError || std.mem.Allocator.Error)!void {
    // A side escape that falls through to this region's end needs no wrapper
    // (`structure.regionSideEscapeFallsThrough`).
    if (!structured_escape.regionWritesOwnedEscape(region) and
        !try structured_escape.regionNeedsTransferWrapper(allocator, region))
    {
        return emitRegionBodyWithPredeclaredBlock(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            region,
            region_indent,
            place_aliases,
            predeclared_block,
        );
    }

    const target = region.stop orelse return error.UnsupportedControlFlow;
    // A loop boundary's body arm written as a lexical `continue` would bind to this `repeat`; leaving the wrapper
    // reaches `target`, not the loop header. Refuse: emitFunctionBody re-emits the function flat.
    if (structured_escape.regionHasLoopBoundaryContinueNotTo(region, target)) return error.UnsupportedControlFlow;
    // A loop exit written as an unflagged `break` (a side exit that does not end the function, a shared exit or a
    // loop control's exit) would bind to this `repeat`; leaving the wrapper reaches `target`, not the loop exit.
    // Refuse: emitFunctionBody re-emits the function flat instead.
    if (structured_escape.regionHasUnflaggedLoopExitBreak(program, region)) return error.UnsupportedControlFlow;
    const body_indent = try allocDeeperIndent(allocator, region_indent);
    defer allocator.free(body_indent);

    const has_predeclared_stop_flag = (predeclared_block != null and predeclared_block.? == target) or
        structured_escape.regionHasLoopBoundaryExitTo(region, target);
    if (!has_predeclared_stop_flag) {
        try emitEscapeFlagDeclaration(output, allocator, program, emission_plan, target, region_indent);
    }
    try output.appendSlice(allocator, region_indent);
    try output.appendSlice(allocator, "repeat\n");
    {
        // A lexical `continue` in the wrapped body binds to this `repeat`, and leaving it reaches `target`.
        const wrapper_binder: ContinueBinder = .{ .kind = .wrapper, .stop = target, .parent = emission_plan.state.continue_binder };
        emission_plan.state.continue_binder = &wrapper_binder;
        defer emission_plan.state.continue_binder = wrapper_binder.parent;
        try emitRegionBodyWithPredeclaredBlock(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            region,
            body_indent,
            place_aliases,
            predeclared_block,
        );
    }
    try output.appendSlice(allocator, region_indent);
    try output.appendSlice(allocator, "until true\n");
    try emitRegionEscapePropagation(output, allocator, program, emission_plan, region, region_indent);
}

fn emitRegionBodyWithPredeclaredBlock(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    region: *const structure.Region,
    region_indent: []const u8,
    place_aliases: []const PlaceAlias,
    predeclared_block: ?ir.BlockId,
) (EmitError || std.mem.Allocator.Error)!void {
    _ = predeclared_block;
    var trace_stage: []const u8 = "begin";
    errdefer std.debug.print(
        "emit region body failure stage={s} first={?d} nodes={d} stop={?d} loop_exit={?d}\n",
        .{
            trace_stage,
            if (region.nodes.len == 0) null else region.nodes[0].blockId().index(),
            region.nodes.len,
            if (region.stop) |block| block.index() else null,
            if (region.loop_exit) |block| block.index() else null,
        },
    );
    trace_stage = "stop_forwarding";
    const forwarded_stop_edge = try validatedStopForwardingEdge(program, region);
    trace_stage = "continue_projection";
    const projected_continue = try validatedContinueProjectionAlloc(allocator, program, region);
    if (forwarded_stop_edge != null and
        (region.terminal_projection != null or region.continue_projection != null or region.escape_projection != null))
    {
        return error.UnsupportedControlFlow;
    }
    const projection_count = @intFromBool(region.terminal_projection != null) +
        @intFromBool(region.continue_projection != null) +
        @intFromBool(region.escape_projection != null);
    if (projection_count > 1) {
        return error.UnsupportedControlFlow;
    }
    if (region.terminal_projection) |projection| {
        if (projection.edge) |edge| {
            if (region.nodes.len == 0) return error.UnsupportedControlFlow;
            const source_id = switch (region.nodes[region.nodes.len - 1]) {
                .block => |block_id| block_id,
                else => return error.UnsupportedControlFlow,
            };
            if (source_id.index() >= program.blocks.len) return error.UnsupportedControlFlow;
            const source_edge = switch (program.blocks[source_id.index()].terminator) {
                .jump => |jump| jump,
                else => return error.UnsupportedControlFlow,
            };
            if (!sameEdge(source_edge, edge)) return error.UnsupportedControlFlow;
        } else if (region.nodes.len == 0) {
            return error.UnsupportedControlFlow;
        }
    }
    var expression_composition = try branch_expression.Composition.init(allocator, program, emission_plan, scopes, region);
    defer expression_composition.deinit();
    const composition: *const branch_expression.Composition = &expression_composition;
    var group_count: usize = 0;
    var counted_group: emission_scope.ScopeId = emission_scope.invalid_scope;
    for (region.nodes) |*node| {
        trace_stage = "node_scope";
        const group = scopes.nodeContainerScope(node) orelse return error.UnsupportedControlFlow;
        if (group != counted_group) {
            counted_group = group;
            group_count += 1;
        }
    }
    const wraps_groups = group_count > 1;
    var active_group: emission_scope.ScopeId = emission_scope.invalid_scope;
    var active_group_wrapper: ?ContainerGroupWrapper = null;
    var allocated_group_indent: ?[]u8 = null;
    defer if (allocated_group_indent) |value| allocator.free(value);
    for (region.nodes, 0..) |*node, node_index| {
        const group = scopes.nodeContainerScope(node) orelse return error.UnsupportedControlFlow;
        if (group != active_group) {
            if (active_group != emission_scope.invalid_scope and wraps_groups) {
                try closeContainerGroupWrapper(output, allocator, region_indent, active_group_wrapper.?);
                active_group_wrapper = null;
                allocator.free(allocated_group_indent.?);
                allocated_group_indent = null;
            }
            active_group = group;
            if (wraps_groups) {
                const output_start = output.items.len;
                try output.appendSlice(allocator, region_indent);
                try output.appendSlice(allocator, "do\n");
                active_group_wrapper = .{
                    .output_start = output_start,
                    .body_start = output.items.len,
                };
                allocated_group_indent = try allocDeeperIndent(allocator, region_indent);
            }
            try emitScopeDeclarations(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                group,
                allocated_group_indent orelse region_indent,
            );
        }
        const node_scope = scopes.nodeScope(node) orelse return error.UnsupportedControlFlow;
        const indent = allocated_group_indent orelse region_indent;
        try emitScopeDeclarations(output, allocator, program, emission_plan, scopes, node_scope, indent);
        trace_stage = "node_emit";
        switch (node.*) {
            .block => |block_id| {
                const block = program.blocks[block_id.index()];
                try emitBlockInstructionsWithDeclaration(output, allocator, program, emission_plan, scopes, block, indent, false, place_aliases, composition);
                switch (block.terminator) {
                    .jump => |edge| {
                        if (forwarded_stop_edge) |forwarded_edge| {
                            if (node_index + 1 == region.nodes.len and edge.target == region.stop_forwarding.?) {
                                if (edge.arguments.len != 0 or program.blocks[edge.target.index()].parameters.len != 0) {
                                    return error.UnsupportedControlFlow;
                                }
                                try emitEdgeParametersUnlessConsumed(
                                    output,
                                    allocator,
                                    program,
                                    emission_plan,
                                    scopes,
                                    program.blocks[forwarded_edge.target.index()],
                                    forwarded_edge.arguments,
                                    indent,
                                    false,
                                    place_aliases,
                                );
                                continue;
                            }
                        }
                        if (region.terminal_projection) |projection| {
                            if (projection.edge) |projected_edge| {
                                if (node_index + 1 == region.nodes.len and sameEdge(edge, projected_edge)) {
                                    try emitProjectedTerminal(
                                        output,
                                        allocator,
                                        program,
                                        emission_plan,
                                        scopes,
                                        projected_edge,
                                        projection.terminal,
                                        indent,
                                        place_aliases,
                                        composedValuePlan(emission_plan, place_aliases, composition),
                                    );
                                    continue;
                                }
                            }
                        }
                        if (projected_continue) |projection| {
                            if (node_index + 1 == region.nodes.len and sameEdge(edge, projection.source_edge)) {
                                try emitProjectedContinue(
                                    output,
                                    allocator,
                                    program,
                                    emission_plan,
                                    scopes,
                                    projection.target_edge,
                                    region.continue_projection.?.target,
                                    indent,
                                    place_aliases,
                                    projection.nonlocal,
                                );
                                continue;
                            }
                        }
                        if (region.escape_projection) |projection| {
                            if (projection.edge) |projected_edge| {
                                if (node_index + 1 == region.nodes.len and sameEdge(edge, projected_edge)) {
                                    try emitEdgeParametersUnlessConsumed(
                                        output,
                                        allocator,
                                        program,
                                        emission_plan,
                                        scopes,
                                        program.blocks[projected_edge.target.index()],
                                        projected_edge.arguments,
                                        indent,
                                        false,
                                        place_aliases,
                                    );
                                    try emitEscapeFlagSet(output, allocator, program, emission_plan, projection.target, indent);
                                    try emitBreakStatement(output, allocator, indent);
                                    continue;
                                }
                            }
                        }
                        const exits_region = region.stop != null and edge.target == region.stop.?;
                        if (!exits_region) {
                            if (node_index + 1 >= region.nodes.len or region.nodes[node_index + 1].blockId() != edge.target) {
                                return error.UnsupportedControlFlow;
                            }
                        }
                        try emitEdgeParametersUnlessConsumed(
                            output,
                            allocator,
                            program,
                            emission_plan,
                            scopes,
                            program.blocks[edge.target.index()],
                            edge.arguments,
                            indent,
                            !exits_region,
                            place_aliases,
                        );
                    },
                    .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {
                        if (node_index + 1 != region.nodes.len) return error.UnsupportedControlFlow;
                        try call_emission.terminator(
                            output,
                            allocator,
                            program,
                            emission_plan,
                            block,
                            indent,
                            composedValuePlan(emission_plan, place_aliases, composition),
                        );
                    },
                    .branch => return error.UnsupportedControlFlow,
                }
            },
            .branch => |branch_plan| {
                trace_stage = "branch_edges";
                if (scopes.nativeIterationConsumesParameters(branch_plan.block)) {
                    if (try iteration_protocol.matchAcyclicBranch(allocator, program, branch_plan)) |acyclic| {
                        try emitAcyclicNativeIteration(
                            output,
                            allocator,
                            program,
                            emission_plan,
                            scopes,
                            region,
                            node_index,
                            acyclic,
                            indent,
                            place_aliases,
                        );
                        continue;
                    }
                }
                const block = program.blocks[branch_plan.block.index()];
                const branch = switch (block.terminator) {
                    .branch => |value| value,
                    else => return error.UnsupportedControlFlow,
                };
                const then_edge = try branch_statement.validatedStructuredEdgeAlloc(
                    allocator,
                    program,
                    .{ .source = block.id, .kind = .branch_then, .target = branch.then_edge.target },
                    branch.then_edge,
                    branch_plan.then_edge_override,
                    branch_plan.then_shared_reentry,
                );
                const else_edge = try branch_statement.validatedStructuredEdgeAlloc(
                    allocator,
                    program,
                    .{ .source = block.id, .kind = .branch_else, .target = branch.else_edge.target },
                    branch.else_edge,
                    branch_plan.else_edge_override,
                    branch_plan.else_shared_reentry,
                );
                trace_stage = "branch_block";
                try emitBlockInstructionsWithDeclaration(output, allocator, program, emission_plan, scopes, block, indent, false, place_aliases, composition);

                if (branch_plan.join) |join_id| {
                    const join_is_region_stop = region.stop != null and join_id == region.stop.?;
                    const join_is_terminal_projection = if (region.terminal_projection) |projection|
                        projection.edge == null and projection.terminal == join_id and node_index + 1 == region.nodes.len
                    else
                        false;
                    const join_is_continue_projection = if (region.continue_projection) |projection|
                        projection.edge == null and projection.forwarding == null and
                            projection.target == join_id and node_index + 1 == region.nodes.len
                    else
                        false;
                    const join_is_escape_projection = if (region.escape_projection) |projection|
                        projection.edge == null and projection.target == join_id and node_index + 1 == region.nodes.len
                    else
                        false;
                    const join_is_forwarded_stop = region.stop_forwarding != null and
                        join_id == region.stop_forwarding.? and node_index + 1 == region.nodes.len;
                    if (!join_is_region_stop and !join_is_terminal_projection and !join_is_continue_projection and
                        !join_is_escape_projection and !join_is_forwarded_stop)
                    {
                        if (node_index + 1 >= region.nodes.len or region.nodes[node_index + 1].blockId() != join_id) {
                            return error.UnsupportedControlFlow;
                        }
                    }
                } else if (node_index + 1 != region.nodes.len) {
                    return error.UnsupportedControlFlow;
                }

                branch_emission: {
                    trace_stage = "branch_emission";
                    if (stage_trace.enabled) std.debug.print(
                        "emit branch block={} join={?d} then_target={} else_target={} then_nodes={} else_nodes={}\n",
                        .{
                            branch_plan.block.index(),
                            if (branch_plan.join) |join| join.index() else null,
                            then_edge.target.index(),
                            else_edge.target.index(),
                            branch_plan.then_region.nodes.len,
                            branch_plan.else_region.nodes.len,
                        },
                    );
                    if (branch_plan.join != null and branch_plan.then_edge_override == null and
                        branch_plan.else_edge_override == null and branch_plan.then_shared_reentry == null and
                        branch_plan.else_shared_reentry == null and emission_plan.branchEdgesAreIdentical(block))
                    {
                        if (emission_plan.discardedBranchConditionNeedsLocal(program, block)) {
                            try output.appendSlice(allocator, indent);
                            try output.appendSlice(allocator, "local _ = ");
                            try branch_expression.emitCondition(
                                output,
                                allocator,
                                program,
                                emission_plan,
                                branch.condition,
                                composition,
                                false,
                                place_aliases,
                            );
                            try output.append(allocator, '\n');
                        }
                        try emitBranchArm(
                            output,
                            allocator,
                            program,
                            emission_plan,
                            scopes,
                            then_edge,
                            branch_plan.then_region,
                            branch_plan.join,
                            indent,
                            place_aliases,
                        );
                        break :branch_emission;
                    }
                    if (branch_expression.match(program, emission_plan, scopes, branch, branch_plan)) |expression_plan| {
                        if (composition.isDeferred(expression_plan.target)) break :branch_emission;
                        try branch_expression.emitAssignment(output, allocator, program, emission_plan, scopes, expression_plan, composition, indent, place_aliases);
                        break :branch_emission;
                    }

                    if (branch_plan.join == null and
                        regionAlwaysFunctionTerminates(program, branch_plan.then_region) and
                        regionAlwaysFunctionTerminates(program, branch_plan.else_region))
                    {
                        const terminal_indent = try allocDeeperIndent(allocator, indent);
                        defer allocator.free(terminal_indent);
                        try output.appendSlice(allocator, indent);
                        try output.appendSlice(allocator, "if ");
                        try branch_expression.emitCondition(output, allocator, program, emission_plan, branch.condition, composition, false, place_aliases);
                        try output.appendSlice(allocator, " then\n");
                        try emitBranchArm(output, allocator, program, emission_plan, scopes, then_edge, branch_plan.then_region, null, terminal_indent, place_aliases);
                        try output.appendSlice(allocator, indent);
                        try output.appendSlice(allocator, "end\n");
                        try emitBranchArm(output, allocator, program, emission_plan, scopes, else_edge, branch_plan.else_region, null, indent, place_aliases);
                        break :branch_emission;
                    }

                    const arm_indent = try allocDeeperIndent(allocator, indent);
                    defer allocator.free(arm_indent);

                    const then_is_empty = branchArmIsStructurallyEmpty(program, then_edge, branch_plan.then_region, branch_plan.join);
                    const else_is_empty = branchArmIsStructurallyEmpty(program, else_edge, branch_plan.else_region, branch_plan.join);
                    if (then_is_empty and else_is_empty) {
                        // The condition was already evaluated by the branch block.
                    } else if (then_is_empty) {
                        try output.appendSlice(allocator, indent);
                        try output.appendSlice(allocator, "if not ");
                        try branch_expression.emitCondition(output, allocator, program, emission_plan, branch.condition, composition, true, place_aliases);
                        try output.appendSlice(allocator, " then\n");
                        try emitBranchArm(output, allocator, program, emission_plan, scopes, else_edge, branch_plan.else_region, branch_plan.join, arm_indent, place_aliases);
                    } else {
                        try output.appendSlice(allocator, indent);
                        try output.appendSlice(allocator, "if ");
                        try branch_expression.emitCondition(output, allocator, program, emission_plan, branch.condition, composition, false, place_aliases);
                        try output.appendSlice(allocator, " then\n");
                        if (!then_is_empty) {
                            try emitBranchArm(output, allocator, program, emission_plan, scopes, then_edge, branch_plan.then_region, branch_plan.join, arm_indent, place_aliases);
                        }
                        if (!else_is_empty) {
                            if (branch_statement.matchElseIf(program, emission_plan, scopes, else_edge, branch_plan.else_region, branch_plan.join)) |else_if| {
                                try emitElseIfChain(output, allocator, program, emission_plan, scopes, else_if, branch_plan.join.?, indent, arm_indent, place_aliases);
                            } else {
                                try output.appendSlice(allocator, indent);
                                try output.appendSlice(allocator, "else\n");
                                try emitBranchArm(output, allocator, program, emission_plan, scopes, else_edge, branch_plan.else_region, branch_plan.join, arm_indent, place_aliases);
                            }
                        }
                    }

                    if (!then_is_empty or !else_is_empty) {
                        try output.appendSlice(allocator, indent);
                        try output.appendSlice(allocator, "end\n");
                    }
                }
            },
            .loop => |loop_plan| {
                try emitLoop(output, allocator, program, emission_plan, scopes, region, node_index, loop_plan, indent, place_aliases);
                if (region.stop != null or region.loop_exit != null) {
                    try emitLoopEscapePropagation(output, allocator, program, emission_plan, node.*, indent, false);
                }
                if (loop_plan.exit_is_escape) {
                    try emitEscapeFlagSet(output, allocator, program, emission_plan, loop_plan.exit_edge.target, indent);
                }
            },
            .latch_loop => |loop_plan| {
                try emitLatchLoop(output, allocator, program, emission_plan, scopes, region, node_index, loop_plan, indent, place_aliases);
                if (region.stop != null or region.loop_exit != null) {
                    try emitLoopEscapePropagation(output, allocator, program, emission_plan, node.*, indent, false);
                }
                if (loop_plan.exit_is_escape) {
                    try emitEscapeFlagSet(output, allocator, program, emission_plan, loop_plan.exit, indent);
                }
            },
            .infinite_loop => |loop_plan| {
                try emitInfiniteLoop(output, allocator, program, emission_plan, scopes, region, node_index, loop_plan, indent, place_aliases);
                if (region.stop != null or region.loop_exit != null) {
                    try emitLoopEscapePropagation(output, allocator, program, emission_plan, node.*, indent, false);
                }
                if (loop_plan.exit_is_escape) {
                    try emitEscapeFlagSet(output, allocator, program, emission_plan, loop_plan.exit.?, indent);
                }
            },
            .loop_control => |control| try emitLoopControl(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                region,
                node_index,
                control,
                indent,
                place_aliases,
            ),
            .loop_boundary => |control| {
                try emitLoopBoundaryControl(
                    output,
                    allocator,
                    program,
                    emission_plan,
                    scopes,
                    region,
                    node_index,
                    control,
                    indent,
                    place_aliases,
                );
            },
            .loop_terminal => |control| try emitLoopTerminalControl(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                region,
                node_index,
                control,
                indent,
                place_aliases,
            ),
        }
        if (projected_continue) |projection| {
            if (node_index + 1 == region.nodes.len and node.* == .loop) {
                if (projection.nonlocal) {
                    // Carried by flag: this region's own wrapper follows the inner loop, and the flag carries the
                    // continue past every wrapper to the loop.
                    _ = try loop_continue_projection.validateEntry(program, region.continue_projection.?.target, projection.target_edge);
                    try emitEscapeFlagSet(output, allocator, program, emission_plan, region.continue_projection.?.target, indent);
                } else {
                    try emitProjectedContinueAfterTransferredEdge(
                        output,
                        allocator,
                        program,
                        emission_plan,
                        projection.target_edge,
                        region.continue_projection.?.target,
                        indent,
                    );
                }
            }
        } else if (region.continue_projection) |projection| {
            if (projection.edge == null and projection.forwarding == null and
                node_index + 1 == region.nodes.len and
                (node.* == .branch or node.* == .latch_loop or node.* == .infinite_loop))
            {
                if (region.continue_target != null and projection.target == region.continue_target.? and !projection.via_flag) {
                    try emitNativeIterationCompletionSetForTarget(output, allocator, emission_plan, projection.target, indent);
                    try emitContinueStatement(output, allocator, emission_plan, projection.target, indent);
                } else {
                    try emitEscapeFlagSet(output, allocator, program, emission_plan, projection.target, indent);
                }
            }
        }
    }
    if (forwarded_stop_edge) |edge| {
        const joined_forwarded_stop = if (region.nodes.len == 0)
            false
        else switch (region.nodes[region.nodes.len - 1]) {
            .branch => |branch| branch.join != null and branch.join.? == region.stop_forwarding.?,
            else => false,
        };
        if (region.nodes.len == 0 or joined_forwarded_stop) {
            try emitEdgeParametersUnlessConsumed(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                program.blocks[edge.target.index()],
                edge.arguments,
                region_indent,
                false,
                place_aliases,
            );
        }
    }
    if (region.terminal_projection) |projection| {
        if (projection.edge == null and region.nodes.len != 0) {
            const joined = switch (region.nodes[region.nodes.len - 1]) {
                .branch => |branch| branch.join != null and branch.join.? == projection.terminal,
                else => false,
            };
            if (!joined) return error.UnsupportedControlFlow;
            try emitProjectedTerminalBody(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                projection.terminal,
                allocated_group_indent orelse region_indent,
                place_aliases,
                composedValuePlan(emission_plan, place_aliases, composition),
            );
        }
    }
    if (region.escape_projection) |projection| {
        const needs_trailing_projection = projection.edge == null or region.nodes.len == 0 or
            region.nodes[region.nodes.len - 1] != .block;
        if (needs_trailing_projection) {
            try emitEscapeFlagSet(output, allocator, program, emission_plan, projection.target, allocated_group_indent orelse region_indent);
            try emitBreakStatement(output, allocator, allocated_group_indent orelse region_indent);
        }
    }
    if (active_group != emission_scope.invalid_scope and wraps_groups) {
        try closeContainerGroupWrapper(output, allocator, region_indent, active_group_wrapper.?);
        active_group_wrapper = null;
        allocator.free(allocated_group_indent.?);
        allocated_group_indent = null;
    }
    if (!expression_composition.allRenderedExactlyOnce()) {
        return error.UnsupportedControlFlow;
    }
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

fn emitElseIfChain(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    structured: structure.Branch,
    chain_join: ir.BlockId,
    indent: []const u8,
    arm_indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    const block = program.blocks[structured.block.index()];
    const branch = switch (block.terminator) {
        .branch => |value| value,
        else => return error.UnsupportedControlFlow,
    };
    const then_edge = try branch_statement.validatedStructuredEdgeAlloc(
        allocator,
        program,
        .{ .source = block.id, .kind = .branch_then, .target = branch.then_edge.target },
        branch.then_edge,
        structured.then_edge_override,
        structured.then_shared_reentry,
    );
    const else_edge = try branch_statement.validatedStructuredEdgeAlloc(
        allocator,
        program,
        .{ .source = block.id, .kind = .branch_else, .target = branch.else_edge.target },
        branch.else_edge,
        structured.else_edge_override,
        structured.else_shared_reentry,
    );

    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "elseif ");
    try branch_expression.emitCondition(output, allocator, program, emission_plan, branch.condition, null, false, place_aliases);
    try output.appendSlice(allocator, " then\n");
    try emitBranchArm(output, allocator, program, emission_plan, scopes, then_edge, structured.then_region, structured.join, arm_indent, place_aliases);

    if (branchArmIsStructurallyEmpty(program, else_edge, structured.else_region, structured.join)) return;
    if (branch_statement.matchElseIf(program, emission_plan, scopes, else_edge, structured.else_region, chain_join)) |next| {
        return emitElseIfChain(output, allocator, program, emission_plan, scopes, next, chain_join, indent, arm_indent, place_aliases);
    }
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "else\n");
    try emitBranchArm(output, allocator, program, emission_plan, scopes, else_edge, structured.else_region, structured.join, arm_indent, place_aliases);
}

/// A privately owned return clone: a block with exactly one predecessor, no instructions, and a
/// `return <values>` terminator whose values are exactly its parameters. Node-split normalization
/// produces such clones (one per escape) so a multi-entry ring becomes reducible; because the clone
/// has a single predecessor its parameters are bound only from that edge, so the clone's return can
/// be emitted inline as `return <edge arguments>` wherever the edge is reached.
fn isPrivatelyOwnedReturnClone(
    analysis: *const cfg.Analysis,
    program: *const ir.Program,
    block_id: ir.BlockId,
) bool {
    if (block_id.index() >= program.blocks.len) return false;
    const block = program.blocks[block_id.index()];
    if (block.instructions.len != 0) return false;
    const returns = switch (block.terminator) {
        .return_values => |values| values,
        else => return false,
    };
    if (!std.mem.eql(ir.ValueId, returns, block.parameters)) return false;
    return analysis.predecessorCount(block_id) == 1;
}

fn emitBranchArmImpl(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    edge: ir.Edge,
    region: *const structure.Region,
    join: ?ir.BlockId,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    var trace_stage: []const u8 = "begin";
    errdefer std.debug.print(
        "emit branch arm failure stage={s} target={} join={?d} nodes={d} stop={?d} continue_target={?d} stop_forwarding={?d} terminal={} continue={} escape={} edge_args={d}\n",
        .{
            trace_stage,
            edge.target.index(),
            if (join) |block| block.index() else null,
            region.nodes.len,
            if (region.stop) |block| block.index() else null,
            if (region.continue_target) |block| block.index() else null,
            if (region.stop_forwarding) |block| block.index() else null,
            region.terminal_projection != null,
            region.continue_projection != null,
            region.escape_projection != null,
            edge.arguments.len,
        },
    );
    trace_stage = "stop_forwarding";
    if (region.stop_forwarding) |entry| {
        if (region.nodes.len == 0 and (edge.target != entry or edge.arguments.len != 0)) return error.UnsupportedControlFlow;
    }
    trace_stage = "terminal_projection";
    if (region.terminal_projection) |projection| {
        if (projection.edge == null) {
            if (region.nodes.len == 0) {
                if (edge.target != projection.terminal) return error.UnsupportedControlFlow;
                return emitProjectedTerminal(
                    output,
                    allocator,
                    program,
                    emission_plan,
                    scopes,
                    edge,
                    projection.terminal,
                    indent,
                    place_aliases,
                    valuePlan(emission_plan, place_aliases),
                );
            }
            if (edge.target != region.nodes[0].blockId()) return error.UnsupportedControlFlow;
        }
    }
    trace_stage = "continue_projection";
    if (region.continue_projection) |projection| {
        // An empty arm is written in its holding region's `if`, with no wrapper of its own: a continue it carries by
        // flag sets the flag and leaves the innermost wrapper, whose propagation carries the flag on to the loop.
        const by_flag = region.continue_target == null or region.continue_target.? != projection.target or
            projection.via_flag;
        if (try validateEmptyProjectedContinue(program, region, edge)) |projected_edge| {
            try emitProjectedContinue(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                projected_edge,
                projection.target,
                indent,
                place_aliases,
                by_flag,
            );
            if (by_flag) try emitEmptyArmFlagBreak(output, allocator, emission_plan, indent);
            return;
        }
        if (projection.edge == null and projection.forwarding == null) {
            if (region.nodes.len == 0) {
                try emitProjectedContinue(
                    output,
                    allocator,
                    program,
                    emission_plan,
                    scopes,
                    edge,
                    projection.target,
                    indent,
                    place_aliases,
                    by_flag,
                );
                if (by_flag) try emitEmptyArmFlagBreak(output, allocator, emission_plan, indent);
                return;
            }
            const owns_target = switch (region.nodes[region.nodes.len - 1]) {
                .branch => |branch| branch.join != null and branch.join.? == projection.target,
                .latch_loop => |loop| loop.exit == projection.target,
                .infinite_loop => |loop| loop.exit != null and loop.exit.? == projection.target,
                else => false,
            };
            if (!owns_target or edge.target != region.nodes[0].blockId()) {
                return error.UnsupportedControlFlow;
            }
        }
        if (region.nodes.len == 0 or edge.target != region.nodes[0].blockId()) return error.UnsupportedControlFlow;
    }
    trace_stage = "escape_projection";
    if (region.escape_projection) |projection| {
        if (projection.edge == null and region.nodes.len == 0) {
            if (edge.target != projection.target) return error.UnsupportedControlFlow;
        } else if (region.nodes.len == 0 or edge.target != region.nodes[0].blockId()) {
            if (region.nodes.len == 0 and isPrivatelyOwnedReturnClone(scopes.analysis, program, edge.target)) {
                return emitReturnArguments(output, allocator, program, valuePlan(emission_plan, place_aliases), edge.arguments, indent);
            }
            return error.UnsupportedControlFlow;
        }
    }
    trace_stage = "edge_parameters";
    const enters_join = join != null and edge.target == join.?;
    const enters_region_stop = region.stop != null and edge.target == region.stop.?;
    try emitEdgeParametersUnlessConsumed(output, allocator, program, emission_plan, scopes, program.blocks[edge.target.index()], edge.arguments, indent, !enters_join and !enters_region_stop, place_aliases);
    trace_stage = "region";
    try emitRegion(output, allocator, program, emission_plan, scopes, region, indent, place_aliases);
}

/// The `break` after the escape flag of a continue an empty branch arm carries by flag: the arm is written in its
/// holding region's `if` with no wrapper of its own, so the `break` must leave a transfer wrapper, whose
/// propagation carries the flag on. A loop boundary's body exit continue carried by flag, written in its holding
/// region's text, takes the same `break`. Anywhere else the function is refused, and emitFunctionBody writes it in
/// the flat layout.
fn emitEmptyArmFlagBreak(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    emission_plan: *const EmissionPlan,
    indent: []const u8,
) (EmitError || std.mem.Allocator.Error)!void {
    const innermost = emission_plan.state.continue_binder orelse return error.UnsupportedControlFlow;
    if (innermost.kind != .wrapper) return error.UnsupportedControlFlow;
    try emitBreakStatement(output, allocator, indent);
}

fn emitBranchArm(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    edge: ir.Edge,
    region: *const structure.Region,
    join: ?ir.BlockId,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    emitBranchArmImpl(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        edge,
        region,
        join,
        indent,
        place_aliases,
    ) catch |err| {
        std.debug.print(
            "emit branch arm error={s} target={} join={?d} region_first={?d} region_nodes={d} stop={?d} continue_target={?d} projection_target={?d} projection_edge={} projection_forwarding={}\n",
            .{
                @errorName(err),
                edge.target.index(),
                if (join) |block| block.index() else null,
                if (region.nodes.len == 0) null else region.nodes[0].blockId().index(),
                region.nodes.len,
                if (region.stop) |block| block.index() else null,
                if (region.continue_target) |block| block.index() else null,
                if (region.continue_projection) |projection| projection.target.index() else null,
                if (region.continue_projection) |projection| projection.edge != null else false,
                if (region.continue_projection) |projection| projection.forwarding != null else false,
            },
        );
        return err;
    };
}

fn validatedStopForwardingEdge(program: *const ir.Program, region: *const structure.Region) EmitError!?ir.Edge {
    const entry = region.stop_forwarding orelse return null;
    const stop = region.stop orelse return error.UnsupportedControlFlow;
    return try transparent_stop.validateEdge(program, entry, stop);
}

const ValidatedContinueProjection = struct {
    source_edge: ir.Edge,
    target_edge: ir.Edge,
    /// Written as an escape flag: the target is not the region's continue target, or the projection is carried by
    /// flag (`structure.markFlaggedContinues`).
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
        return .{ .source_edge = source_edge, .target_edge = forwarding.edge, .nonlocal = nonlocal or projection.via_flag };
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
    return .{ .source_edge = edge, .target_edge = edge, .nonlocal = projection.via_flag };
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

fn emitProjectedTerminal(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    edge: ir.Edge,
    terminal_id: ir.BlockId,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
    values: render.ValuePlan,
) (EmitError || std.mem.Allocator.Error)!void {
    if (edge.target != terminal_id or terminal_id.index() >= program.blocks.len) return error.UnsupportedControlFlow;
    const terminal = program.blocks[terminal_id.index()];
    if (edge.arguments.len != terminal.parameters.len) return error.UnsupportedControlFlow;
    switch (terminal.terminator) {
        .return_values, .return_pack, .return_expanded, .throw_error => {},
        else => return error.UnsupportedControlFlow,
    }
    try emitEdgeParametersUnlessConsumed(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        terminal,
        edge.arguments,
        indent,
        false,
        place_aliases,
    );
    return emitProjectedTerminalBody(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        terminal_id,
        indent,
        place_aliases,
        values,
    );
}

fn emitProjectedTerminalBody(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    terminal_id: ir.BlockId,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
    values: render.ValuePlan,
) (EmitError || std.mem.Allocator.Error)!void {
    if (terminal_id.index() >= program.blocks.len) return error.UnsupportedControlFlow;
    const terminal = program.blocks[terminal_id.index()];
    switch (terminal.terminator) {
        .return_values, .return_pack, .return_expanded, .throw_error => {},
        else => return error.UnsupportedControlFlow,
    }
    try emitBlockInstructionsWithDeclaration(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        terminal,
        indent,
        false,
        place_aliases,
        null,
    );
    try call_emission.terminator(output, allocator, program, emission_plan, terminal, indent, values);
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

fn emitLoop(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    enclosing_region: *const structure.Region,
    node_index: usize,
    loop_plan: structure.Loop,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    if (loop_plan.body_region.stop == null or loop_plan.body_region.stop.? != loop_plan.header or
        loop_plan.body_region.continue_target == null or loop_plan.body_region.continue_target.? != loop_plan.header)
    {
        return error.UnsupportedControlFlow;
    }
    if (scopes.nativeIterationConsumesParameters(loop_plan.header)) {
        if (try iteration_protocol.matchLoop(allocator, program, loop_plan)) |protocol| switch (protocol) {
            .numeric => |numeric| return emitNumericForLoop(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                enclosing_region,
                node_index,
                loop_plan.body_region,
                loop_plan.exit_edge,
                numeric,
                false,
                indent,
                place_aliases,
            ),
            .generic => |generic| return emitGenericForLoop(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                enclosing_region,
                node_index,
                loop_plan.body_region,
                loop_plan.exit_edge,
                generic,
                false,
                indent,
                place_aliases,
            ),
        };
    }

    const header = program.blocks[loop_plan.header.index()];
    const branch = switch (header.terminator) {
        .branch => |value| value,
        else => return error.UnsupportedControlFlow,
    };
    const expected_body = if (loop_plan.continue_on_true) branch.then_edge else branch.else_edge;
    const expected_exit = if (loop_plan.continue_on_true) branch.else_edge else branch.then_edge;
    if (expected_body.target != loop_plan.body_edge.target or expected_exit.target != loop_plan.exit_edge.target) {
        return error.UnsupportedControlFlow;
    }

    const exit_is_return_clone = isPrivatelyOwnedReturnClone(scopes.analysis, program, loop_plan.exit_edge.target);
    // Loop exit into a return clone: run prepareLoopExit exactly as before; only when it raises
    // error.UnsupportedControlFlow on a privately owned return clone is the exit inlined as a
    // return instead (prepareLoopExit ignores `output` and mutates nothing, so the catch is safe).
    var inline_return_exit = false;
    prepareLoopExit(output, allocator, program, emission_plan, enclosing_region, node_index, loop_plan.exit_edge.target, indent) catch |err| {
        if (err == error.UnsupportedControlFlow and exit_is_return_clone) {
            inline_return_exit = true;
        } else {
            return err;
        }
    };
    const loop_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(loop_indent);
    const arm_indent = try allocDeeperIndent(allocator, loop_indent);
    defer allocator.free(arm_indent);

    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "while true do\n");
    // A lexical `continue` in the body or in the loop's own propagation binds to this loop.
    const loop_binder: ContinueBinder = .{ .kind = .loop, .header = loop_plan.header, .stop = loop_plan.body_region.stop, .parent = emission_plan.state.continue_binder };
    emission_plan.state.continue_binder = &loop_binder;
    defer emission_plan.state.continue_binder = loop_binder.parent;
    const predeclared_header = if (structured_escape.regionHasNestedEscapeTo(loop_plan.body_region, loop_plan.header))
        loop_plan.header
    else
        null;
    if (predeclared_header) |header_flag| {
        try emitEscapeFlagDeclaration(output, allocator, program, emission_plan, header_flag, loop_indent);
    }
    // The flag of the exit this loop owns starts false on every pass (`loopOwnedExitFlag`).
    if (structured_escape.loopOwnedExitFlag(enclosing_region, .{ .loop = loop_plan })) |exit_flag| {
        try emitEscapeFlagDeclaration(output, allocator, program, emission_plan, exit_flag, loop_indent);
    }
    try emitBlockInstructionsWithDeclaration(output, allocator, program, emission_plan, scopes, header, loop_indent, false, place_aliases, null);
    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "if ");
    try render.valueUseScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), branch.condition);
    try output.appendSlice(allocator, " then\n");
    if (loop_plan.continue_on_true) {
        try emitLoopBody(output, allocator, program, emission_plan, scopes, loop_plan, arm_indent, place_aliases, predeclared_header);
    } else {
        try emitLoopExitTransfer(output, allocator, program, emission_plan, scopes, loop_plan.exit_edge, inline_return_exit, arm_indent, place_aliases);
    }

    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "else\n");
    if (loop_plan.continue_on_true) {
        try emitLoopExitTransfer(output, allocator, program, emission_plan, scopes, loop_plan.exit_edge, inline_return_exit, arm_indent, place_aliases);
    } else {
        try emitLoopBody(output, allocator, program, emission_plan, scopes, loop_plan, arm_indent, place_aliases, predeclared_header);
    }
    try emitLoopEscapePropagation(
        output,
        allocator,
        program,
        emission_plan,
        .{ .loop = loop_plan },
        loop_indent,
        true,
    );
    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "end\n");
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

fn emitAcyclicNativeIteration(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    enclosing_region: *const structure.Region,
    node_index: usize,
    acyclic: iteration_protocol.Acyclic,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    if (acyclic.exit_region) |exit_region| {
        // A header without a join is the last node of its region, as a join-less branch is.
        // Its loop gets no exit edge (no exit placement check, no exit parameters before the loop); the exit arm
        // follows the loop and is written as the else arm of a join-less branch whose arms both terminate.
        if (node_index + 1 != enclosing_region.nodes.len) return error.UnsupportedControlFlow;
        const branch_plan = switch (enclosing_region.nodes[node_index]) {
            .branch => |value| value,
            else => return error.UnsupportedControlFlow,
        };
        const else_edge = try branch_statement.validatedStructuredEdgeAlloc(
            allocator,
            program,
            .{ .source = branch_plan.block, .kind = .branch_else, .target = acyclic.exit_edge.target },
            acyclic.exit_edge,
            branch_plan.else_edge_override,
            branch_plan.else_shared_reentry,
        );
        switch (acyclic.protocol) {
            .numeric => |numeric| try emitNumericForLoop(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                enclosing_region,
                node_index,
                acyclic.body_region,
                null,
                numeric,
                true,
                indent,
                place_aliases,
            ),
            .generic => |generic| try emitGenericForLoop(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                enclosing_region,
                node_index,
                acyclic.body_region,
                null,
                generic,
                true,
                indent,
                place_aliases,
            ),
        }
        return emitBranchArm(output, allocator, program, emission_plan, scopes, else_edge, exit_region, null, indent, place_aliases);
    }
    return switch (acyclic.protocol) {
        .numeric => |numeric| emitNumericForLoop(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            enclosing_region,
            node_index,
            acyclic.body_region,
            acyclic.exit_edge,
            numeric,
            true,
            indent,
            place_aliases,
        ),
        .generic => |generic| emitGenericForLoop(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            enclosing_region,
            node_index,
            acyclic.body_region,
            acyclic.exit_edge,
            generic,
            true,
            indent,
            place_aliases,
        ),
    };
}

fn emitNumericForLoop(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    enclosing_region: *const structure.Region,
    node_index: usize,
    body_region: *const structure.Region,
    exit_edge: ?ir.Edge,
    numeric: iteration_protocol.NumericLoop,
    break_after_body: bool,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    if (numeric.operation.mode == .semantic_normalized) {
        return emitSemanticNormalizedNumericLoop(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            enclosing_region,
            node_index,
            body_region,
            exit_edge,
            numeric,
            break_after_body,
            indent,
            place_aliases,
        );
    }
    if (exit_edge) |edge| try prepareLoopExit(output, allocator, program, emission_plan, enclosing_region, node_index, edge.target, indent);
    const results = numeric.transition.results;
    if (results.len != 4) return error.UnsupportedControlFlow;

    const completion_flag: ?[]const u8 = if (nativeIterationDeclaresCompletion(program, emission_plan, scopes, exit_edge, break_after_body)) blk: {
        const header = body_region.stop orelse return error.UnsupportedControlFlow;
        break :blk try nativeIterationCompletionFlagNameAlloc(allocator, program, emission_plan, header);
    } else null;
    defer if (completion_flag) |flag| allocator.free(flag);

    if (break_after_body and exit_edge != null) {
        try emitEdgeParametersUnlessConsumed(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            program.blocks[exit_edge.?.target.index()],
            exit_edge.?.arguments,
            indent,
            false,
            place_aliases,
        );
    }

    if (completion_flag) |flag| try emitNativeIterationCompletionDeclaration(output, allocator, flag, indent);

    try emitNumericForOpen(output, allocator, program, emission_plan, numeric, indent, place_aliases);

    const loop_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(loop_indent);
    // The flag of the exit this loop owns starts false on every pass (`loopOwnedExitFlag`). A `for` written for a
    // branch or a loop boundary finds no loop node at `node_index`, so it declares nothing.
    if (structured_escape.loopOwnedExitFlag(enclosing_region, enclosing_region.nodes[node_index])) |exit_flag| {
        try emitEscapeFlagDeclaration(output, allocator, program, emission_plan, exit_flag, loop_indent);
    }

    const completion_state = emission_plan.state;
    const previous_completion = completion_state.native_iteration_completion;
    var completion_context: NativeIterationCompletion = undefined;
    defer {
        if (completion_flag != null) completion_state.native_iteration_completion = previous_completion;
    }
    if (completion_flag) |flag| {
        completion_context = .{
            .header = body_region.stop.?,
            .flag_name = flag,
            .parent = previous_completion,
        };
        completion_state.native_iteration_completion = &completion_context;
        try emitNativeIterationCompletionAssignment(output, allocator, flag, false, loop_indent);
    }

    {
        // A lexical `continue` in the body binds to this loop; a `for` that runs its body once binds none.
        const loop_binder: ContinueBinder = if (break_after_body)
            .{ .kind = .one_shot, .parent = emission_plan.state.continue_binder }
        else
            .{ .kind = .loop, .header = body_region.stop, .stop = body_region.stop, .parent = emission_plan.state.continue_binder };
        emission_plan.state.continue_binder = &loop_binder;
        defer emission_plan.state.continue_binder = loop_binder.parent;
        try emitRegion(output, allocator, program, emission_plan, scopes, body_region, loop_indent, place_aliases);
    }
    // No termination test: a body region whose last node returns is written inside a transfer wrapper (when
    // that node is a branch, each returning arm is), so this write never follows a bare return; after a wrapped
    // region it is where a continue the wrapper captures resumes, so it must stay.
    if (completion_flag) |flag| try emitNativeIterationCompletionAssignment(output, allocator, flag, true, loop_indent);
    if (break_after_body and !regionAlwaysFunctionTerminates(program, body_region)) {
        try emitBreakStatement(output, allocator, loop_indent);
    }

    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
    if (completion_flag) |flag| try emitGuardedNativeIterationExitCopy(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        exit_edge.?,
        flag,
        indent,
        place_aliases,
    );
}

/// The `for <index> = <start>, <limit>, <step> do` line of a native numeric loop.
fn emitNumericForOpen(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    numeric: iteration_protocol.NumericLoop,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "for ");
    try render.valueName(output, allocator, &emission_plan.names, numeric.body_parameter);
    try output.appendSlice(allocator, " = ");
    try render.valueUseScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), numeric.initial_arguments[0]);
    try output.appendSlice(allocator, ", ");
    try render.valueUseScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), numeric.initial_arguments[1]);
    try output.appendSlice(allocator, ", ");
    try render.valueUseScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), numeric.initial_arguments[2]);
    try output.appendSlice(allocator, " do\n");
}

fn emitSemanticNormalizedNumericLoop(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    enclosing_region: *const structure.Region,
    node_index: usize,
    body_region: *const structure.Region,
    exit_edge: ?ir.Edge,
    numeric: iteration_protocol.NumericLoop,
    break_after_body: bool,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    const results = numeric.transition.results;
    if (results.len != 4 or numeric.initial_arguments.len != 4) return error.UnsupportedControlFlow;
    if (exit_edge) |edge| try prepareLoopExit(output, allocator, program, emission_plan, enclosing_region, node_index, edge.target, indent);

    if (break_after_body and exit_edge != null) {
        try emitEdgeParametersUnlessConsumed(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            program.blocks[exit_edge.?.target.index()],
            exit_edge.?.arguments,
            indent,
            false,
            place_aliases,
        );
    }

    const state = [_]ir.ValueId{ numeric.operation.control, numeric.operation.limit, numeric.operation.step };
    for (state, numeric.initial_arguments[0..3]) |parameter, initial| {
        try output.appendSlice(allocator, indent);
        if (!emission_plan.names.valueUsesStorage(parameter)) try output.appendSlice(allocator, "local ");
        try render.valueName(output, allocator, &emission_plan.names, parameter);
        try output.appendSlice(allocator, " = ");
        try render.valueUseScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), initial);
        try output.appendSlice(allocator, "\n");
    }

    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "while true do\n");
    const loop_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(loop_indent);
    const branch_indent = try allocDeeperIndent(allocator, loop_indent);
    defer allocator.free(branch_indent);
    // The flag of the exit this loop owns starts false on every pass (`loopOwnedExitFlag`). A `for` written for a
    // branch or a loop boundary finds no loop node at `node_index`, so it declares nothing.
    if (structured_escape.loopOwnedExitFlag(enclosing_region, enclosing_region.nodes[node_index])) |exit_flag| {
        try emitEscapeFlagDeclaration(output, allocator, program, emission_plan, exit_flag, loop_indent);
    }

    try output.appendSlice(allocator, loop_indent);
    try render.valueName(output, allocator, &emission_plan.names, numeric.operation.control);
    try output.appendSlice(allocator, " = ");
    try render.valueName(output, allocator, &emission_plan.names, numeric.operation.control);
    try output.appendSlice(allocator, " + ");
    try render.valueName(output, allocator, &emission_plan.names, numeric.operation.step);
    try output.appendSlice(allocator, "\n");

    try output.appendSlice(allocator, loop_indent);
    if (!emission_plan.names.valueUsesStorage(results[0])) try output.appendSlice(allocator, "local ");
    try render.valueName(output, allocator, &emission_plan.names, results[0]);
    try output.appendSlice(allocator, "\n");
    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "if ");
    try render.valueName(output, allocator, &emission_plan.names, numeric.operation.step);
    try output.appendSlice(allocator, " <= 0 then\n");
    try output.appendSlice(allocator, branch_indent);
    try render.valueName(output, allocator, &emission_plan.names, results[0]);
    try output.appendSlice(allocator, " = ");
    try render.valueName(output, allocator, &emission_plan.names, numeric.operation.control);
    try output.appendSlice(allocator, " >= ");
    try render.valueName(output, allocator, &emission_plan.names, numeric.operation.limit);
    try output.appendSlice(allocator, "\n");
    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "else\n");
    try output.appendSlice(allocator, branch_indent);
    try render.valueName(output, allocator, &emission_plan.names, results[0]);
    try output.appendSlice(allocator, " = ");
    try render.valueName(output, allocator, &emission_plan.names, numeric.operation.control);
    try output.appendSlice(allocator, " <= ");
    try render.valueName(output, allocator, &emission_plan.names, numeric.operation.limit);
    try output.appendSlice(allocator, "\n");
    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "end\n");

    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "if not ");
    try render.valueName(output, allocator, &emission_plan.names, results[0]);
    try output.appendSlice(allocator, " then\n");
    if (!break_after_body and exit_edge != null) {
        try emitEdgeParametersUnlessConsumed(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            program.blocks[exit_edge.?.target.index()],
            exit_edge.?.arguments,
            branch_indent,
            false,
            place_aliases,
        );
    }
    try emitBreakStatement(output, allocator, branch_indent);
    try output.appendSlice(allocator, loop_indent);
    try output.appendSlice(allocator, "end\n");

    try output.appendSlice(allocator, loop_indent);
    if (!emission_plan.names.valueUsesStorage(numeric.body_parameter)) try output.appendSlice(allocator, "local ");
    try render.valueName(output, allocator, &emission_plan.names, numeric.body_parameter);
    try output.appendSlice(allocator, " = ");
    try render.valueName(output, allocator, &emission_plan.names, numeric.operation.control);
    try output.appendSlice(allocator, "\n");
    {
        // A lexical `continue` in the body binds to this loop; a `for` that runs its body once binds none.
        const loop_binder: ContinueBinder = if (break_after_body)
            .{ .kind = .one_shot, .parent = emission_plan.state.continue_binder }
        else
            .{ .kind = .loop, .header = body_region.stop, .stop = body_region.stop, .parent = emission_plan.state.continue_binder };
        emission_plan.state.continue_binder = &loop_binder;
        defer emission_plan.state.continue_binder = loop_binder.parent;
        try emitRegion(output, allocator, program, emission_plan, scopes, body_region, loop_indent, place_aliases);
    }
    if (break_after_body and !regionAlwaysFunctionTerminates(program, body_region)) {
        try emitBreakStatement(output, allocator, loop_indent);
    }

    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

fn emitGenericForLoop(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    enclosing_region: *const structure.Region,
    node_index: usize,
    body_region: *const structure.Region,
    exit_edge: ?ir.Edge,
    generic: iteration_protocol.GenericLoop,
    break_after_body: bool,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    if (exit_edge) |edge| try prepareLoopExit(output, allocator, program, emission_plan, enclosing_region, node_index, edge.target, indent);
    const results = generic.transition.results;
    if (results.len < 4 or results.len != @as(usize, generic.operation.variable_count) + 3) return error.UnsupportedControlFlow;

    const completion_flag: ?[]const u8 = if (nativeIterationDeclaresCompletion(program, emission_plan, scopes, exit_edge, break_after_body)) blk: {
        const header = body_region.stop orelse return error.UnsupportedControlFlow;
        break :blk try nativeIterationCompletionFlagNameAlloc(allocator, program, emission_plan, header);
    } else null;
    defer if (completion_flag) |flag| allocator.free(flag);

    if (break_after_body and exit_edge != null) {
        try emitEdgeParametersUnlessConsumed(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            program.blocks[exit_edge.?.target.index()],
            exit_edge.?.arguments,
            indent,
            false,
            place_aliases,
        );
    }

    if (completion_flag) |flag| try emitNativeIterationCompletionDeclaration(output, allocator, flag, indent);

    try emitGenericForOpen(output, allocator, program, emission_plan, scopes, generic, indent, place_aliases);

    const loop_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(loop_indent);
    // The flag of the exit this loop owns starts false on every pass (`loopOwnedExitFlag`). A `for` written for a
    // branch or a loop boundary finds no loop node at `node_index`, so it declares nothing.
    if (structured_escape.loopOwnedExitFlag(enclosing_region, enclosing_region.nodes[node_index])) |exit_flag| {
        try emitEscapeFlagDeclaration(output, allocator, program, emission_plan, exit_flag, loop_indent);
    }

    const completion_state = emission_plan.state;
    const previous_completion = completion_state.native_iteration_completion;
    var completion_context: NativeIterationCompletion = undefined;
    defer {
        if (completion_flag != null) completion_state.native_iteration_completion = previous_completion;
    }
    if (completion_flag) |flag| {
        completion_context = .{
            .header = body_region.stop.?,
            .flag_name = flag,
            .parent = previous_completion,
        };
        completion_state.native_iteration_completion = &completion_context;
        try emitNativeIterationCompletionAssignment(output, allocator, flag, false, loop_indent);
    }

    {
        // A lexical `continue` in the body binds to this loop; a `for` that runs its body once binds none.
        const loop_binder: ContinueBinder = if (break_after_body)
            .{ .kind = .one_shot, .parent = emission_plan.state.continue_binder }
        else
            .{ .kind = .loop, .header = body_region.stop, .stop = body_region.stop, .parent = emission_plan.state.continue_binder };
        emission_plan.state.continue_binder = &loop_binder;
        defer emission_plan.state.continue_binder = loop_binder.parent;
        try emitRegion(output, allocator, program, emission_plan, scopes, body_region, loop_indent, place_aliases);
    }
    // No termination test: a body region whose last node returns is written inside a transfer wrapper (when
    // that node is a branch, each returning arm is), so this write never follows a bare return; after a wrapped
    // region it is where a continue the wrapper captures resumes, so it must stay.
    if (completion_flag) |flag| try emitNativeIterationCompletionAssignment(output, allocator, flag, true, loop_indent);
    if (break_after_body and !regionAlwaysFunctionTerminates(program, body_region)) {
        try emitBreakStatement(output, allocator, loop_indent);
    }

    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
    if (completion_flag) |flag| try emitGuardedNativeIterationExitCopy(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        exit_edge.?,
        flag,
        indent,
        place_aliases,
    );
}

fn loopExitTransferWritesParameters(
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    edge: ir.Edge,
) bool {
    if (edge.target.index() >= program.blocks.len or scopes.edgeParametersConsumed(edge.target)) return false;
    const target = program.blocks[edge.target.index()];
    for (target.parameters) |parameter| {
        if (!emission_plan.dead.isValueAlias(parameter)) return true;
    }
    return false;
}

/// Whether a native `for` declares `__lifter_native_iteration_complete_<header>` before it: a loop whose exhaustion
/// edge writes a parameter, never a `for` that runs its body once. The two native writers and the register
/// certificate ask this one predicate.
pub fn nativeIterationDeclaresCompletion(
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    exit_edge: ?ir.Edge,
    break_after_body: bool,
) bool {
    if (break_after_body) return false;
    const edge = exit_edge orelse return false;
    return loopExitTransferWritesParameters(program, emission_plan, scopes, edge);
}

/// The native `for` the readable writer emits for a structure node: the registers its frame holds beside its loop
/// variables, whether it declares a completion local, and the region written inside it (`null`: the body is the
/// terminal block of a loop boundary, written in the node's own scope).
pub const NativeFor = struct {
    header: ir.BlockId,
    hidden_registers: usize,
    completion: bool,
    body: ?*const structure.Region,
};

/// The native `for` `region.nodes[node_index]` is written as, if any: a `.loop` node through `emitLoop`, a `.branch`
/// node through `emitAcyclicNativeIteration` and a `.loop_boundary` node through `emitLoopBoundaryNativeIteration`,
/// each under the activation and the match its writer asks for. A semantic-normalized numeric loop is written as
/// `while true do` and holds no `for` frame.
pub fn nativeForAt(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    region: *const structure.Region,
    node_index: usize,
) std.mem.Allocator.Error!?NativeFor {
    switch (region.nodes[node_index]) {
        .loop => |loop_plan| {
            if (!scopes.nativeIterationConsumesParameters(loop_plan.header)) return null;
            const protocol = (try iteration_protocol.matchLoop(allocator, program, loop_plan)) orelse return null;
            if (nativeProtocolIsSemanticNormalized(protocol)) return null;
            return .{
                .header = loop_plan.header,
                .hidden_registers = nativeForHiddenRegisters(protocol),
                .completion = nativeIterationDeclaresCompletion(program, emission_plan, scopes, loop_plan.exit_edge, false),
                .body = loop_plan.body_region,
            };
        },
        .branch => |branch_plan| {
            if (!scopes.nativeIterationConsumesParameters(branch_plan.block)) return null;
            const acyclic = (try iteration_protocol.matchAcyclicBranch(allocator, program, branch_plan)) orelse return null;
            if (nativeProtocolIsSemanticNormalized(acyclic.protocol)) return null;
            return .{
                .header = branch_plan.block,
                .hidden_registers = nativeForHiddenRegisters(acyclic.protocol),
                .completion = false,
                .body = acyclic.body_region,
            };
        },
        .loop_boundary => |control| {
            if (!scopes.nativeIterationConsumesParameters(control.block)) return null;
            const acyclic = (try iteration_protocol.matchAcyclicLoopBoundary(allocator, program, control)) orelse return null;
            const body: ?*const structure.Region = switch (control.boundary) {
                // The writer opens this `for` itself and writes the terminal block inside it.
                .terminal => null,
                .side_exit => |side_exit| blk: {
                    if (nativeProtocolIsSemanticNormalized(acyclic.protocol)) return null;
                    break :blk side_exit.region;
                },
                else => return null,
            };
            return .{
                .header = control.block,
                .hidden_registers = nativeForHiddenRegisters(acyclic.protocol),
                .completion = false,
                .body = body,
            };
        },
        else => return null,
    }
}

/// The registers a native `for` frame holds beside its loop variables in the pinned compiler: a numeric `for` its
/// limit and step (the index is the loop variable), a generic `for` its generator, state and control and at least two
/// variable slots.
fn nativeForHiddenRegisters(protocol: iteration_protocol.Match) usize {
    return switch (protocol) {
        .numeric => 2,
        .generic => |generic| 3 + @max(generic.body_parameters.len, 2) - generic.body_parameters.len,
    };
}

fn nativeProtocolIsSemanticNormalized(protocol: iteration_protocol.Match) bool {
    return switch (protocol) {
        .numeric => |numeric| numeric.operation.mode == .semantic_normalized,
        .generic => false,
    };
}

fn nativeIterationCompletionFlagNameAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    header: ir.BlockId,
) std.mem.Allocator.Error![]const u8 {
    const base = try std.fmt.allocPrint(allocator, "__lifter_native_iteration_complete_{d}", .{header.index()});
    defer allocator.free(base);
    return emission_plan.names.internalNameAlloc(allocator, program, base);
}

fn emitNativeIterationCompletionDeclaration(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    flag_name: []const u8,
    indent: []const u8,
) std.mem.Allocator.Error!void {
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "local ");
    try output.appendSlice(allocator, flag_name);
    try output.appendSlice(allocator, " = true\n");
}

fn emitNativeIterationCompletionAssignment(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    flag_name: []const u8,
    complete: bool,
    indent: []const u8,
) std.mem.Allocator.Error!void {
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, flag_name);
    try output.appendSlice(allocator, if (complete) " = true\n" else " = false\n");
}

fn emitNativeIterationCompletionSetForTarget(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    emission_plan: *const EmissionPlan,
    target: ir.BlockId,
    indent: []const u8,
) std.mem.Allocator.Error!void {
    var active = emission_plan.state.native_iteration_completion;
    while (active) |completion| : (active = completion.parent) {
        if (completion.header != target) continue;
        return emitNativeIterationCompletionAssignment(output, allocator, completion.flag_name, true, indent);
    }
}

fn emitGuardedNativeIterationExitCopy(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    edge: ir.Edge,
    flag_name: []const u8,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    const copy_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(copy_indent);
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "if ");
    try output.appendSlice(allocator, flag_name);
    try output.appendSlice(allocator, " then\n");
    try emitEdgeParametersUnlessConsumed(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        program.blocks[edge.target.index()],
        edge.arguments,
        copy_indent,
        false,
        place_aliases,
    );
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

/// The `for <bindings> in <initializers> do` line of a native generic loop, with its initializer fusion.
fn emitGenericForOpen(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    generic: iteration_protocol.GenericLoop,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "for ");
    for (generic.body_parameters, 0..) |parameter, index| {
        if (index != 0) try output.appendSlice(allocator, ", ");
        try render.valueName(output, allocator, &emission_plan.names, parameter);
    }
    try output.appendSlice(allocator, " in ");
    const initializer_count = genericInitializerCount(program, emission_plan, generic.initial_arguments[0..3]);
    const initializer_fusion = if (initializer_count == 3)
        scopes.genericInitializerFusion(generic.initial_arguments[0..3], generic.transition.block)
    else
        null;
    if (initializer_fusion) |fusion| {
        if (fusion.producer.index() >= program.instructions.len) return error.UnsupportedOperation;
        try render.plannedInvocation(
            output,
            allocator,
            program,
            valuePlan(emission_plan, place_aliases),
            &emission_plan.packs,
            program.instructions[fusion.producer.index()],
        );
    } else {
        for (generic.initial_arguments[0..initializer_count], 0..) |argument, index| {
            if (index != 0) try output.appendSlice(allocator, ", ");
            if (index + 1 == initializer_count) {
                try render.valueUseRoot(output, allocator, program, valuePlan(emission_plan, place_aliases), argument);
            } else {
                try render.valueUseScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), argument);
            }
        }
    }
    try output.appendSlice(allocator, " do\n");
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

fn emitLoopBody(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    loop_plan: structure.Loop,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
    predeclared_header: ?ir.BlockId,
) (EmitError || std.mem.Allocator.Error)!void {
    const enters_header = loop_plan.body_edge.target == loop_plan.header;
    try emitEdgeParametersUnlessConsumed(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        program.blocks[loop_plan.body_edge.target.index()],
        loop_plan.body_edge.arguments,
        indent,
        !enters_header,
        place_aliases,
    );
    try emitRegionWithPredeclaredBlock(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        loop_plan.body_region,
        indent,
        place_aliases,
        predeclared_header,
    );
}

fn emitLatchLoop(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    enclosing_region: *const structure.Region,
    node_index: usize,
    loop_plan: structure.LatchLoop,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    if (loop_plan.body_region.nodes.len == 0 or loop_plan.body_region.nodes[0].blockId() != loop_plan.header or
        loop_plan.body_region.stop == null or loop_plan.body_region.stop.? != loop_plan.header or
        loop_plan.body_region.continue_target == null or loop_plan.body_region.continue_target.? != loop_plan.header or
        loop_plan.body_region.loop_exit == null or loop_plan.body_region.loop_exit.? != loop_plan.exit)
    {
        return error.UnsupportedControlFlow;
    }
    if (loop_plan.shared_reentries) |shared| {
        try branch_statement.validateSharedPathsAlloc(allocator, program, shared);
    }
    if (loop_plan.shared_exits) |shared| {
        try loop_exit_shape.validateAllAlloc(allocator, program, shared);
    }

    const exit_is_region_stop = enclosing_region.stop != null and loop_plan.exit == enclosing_region.stop.?;
    const exit_is_enclosing_loop_exit = enclosing_region.loop_exit != null and loop_plan.exit == enclosing_region.loop_exit.?;
    if (!exit_is_region_stop and !exit_is_enclosing_loop_exit and !loop_plan.exit_is_escape) {
        if (node_index + 1 >= enclosing_region.nodes.len or enclosing_region.nodes[node_index + 1].blockId() != loop_plan.exit) {
            return error.UnsupportedControlFlow;
        }
    }
    const loop_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(loop_indent);
    const predeclared_header = if (structured_escape.regionHasNestedEscapeTo(loop_plan.body_region, loop_plan.header))
        loop_plan.header
    else
        null;
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "while true do\n");
    {
        // A lexical `continue` in the body or in the loop's own propagation binds to this loop.
        const loop_binder: ContinueBinder = .{ .kind = .loop, .header = loop_plan.header, .stop = loop_plan.body_region.stop, .parent = emission_plan.state.continue_binder };
        emission_plan.state.continue_binder = &loop_binder;
        defer emission_plan.state.continue_binder = loop_binder.parent;
        if (predeclared_header) |header| {
            try emitEscapeFlagDeclaration(output, allocator, program, emission_plan, header, loop_indent);
        }
        // The flag of the exit this loop owns starts false on every pass (`loopOwnedExitFlag`).
        if (structured_escape.loopOwnedExitFlag(enclosing_region, .{ .latch_loop = loop_plan })) |exit_flag| {
            try emitEscapeFlagDeclaration(output, allocator, program, emission_plan, exit_flag, loop_indent);
        }
        try emitRegionWithPredeclaredBlock(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            loop_plan.body_region,
            loop_indent,
            place_aliases,
            predeclared_header,
        );
        try emitLoopEscapePropagation(
            output,
            allocator,
            program,
            emission_plan,
            .{ .latch_loop = loop_plan },
            loop_indent,
            true,
        );
    }
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

fn emitInfiniteLoop(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    enclosing_region: *const structure.Region,
    node_index: usize,
    loop_plan: structure.InfiniteLoop,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    const body_projects_continue = loop_plan.body_region.continue_projection != null and
        loop_plan.body_region.continue_projection.?.target == loop_plan.header;
    const body_stop = loop_plan.body_region.stop orelse return error.UnsupportedControlFlow;
    if (body_stop != loop_plan.header and !body_projects_continue) {
        const forwarding = try transparent_stop.validateEdge(program, body_stop, loop_plan.header);
        if (forwarding.arguments.len != 0) return error.UnsupportedControlFlow;
    }
    if (loop_plan.body_region.nodes.len == 0 or loop_plan.body_region.nodes[0].blockId() != loop_plan.header or
        loop_plan.body_region.continue_target == null or loop_plan.body_region.continue_target.? != loop_plan.header)
    {
        return error.UnsupportedControlFlow;
    }
    if (loop_plan.exit) |exit| {
        if (loop_plan.body_region.loop_exit == null or loop_plan.body_region.loop_exit.? != exit) return error.UnsupportedControlFlow;
        try prepareLoopExit(output, allocator, program, emission_plan, enclosing_region, node_index, exit, indent);
    } else {
        if (loop_plan.shared_side_exit != null) return error.UnsupportedControlFlow;
        if (node_index + 1 != enclosing_region.nodes.len or loop_plan.body_region.loop_exit != null) return error.UnsupportedControlFlow;
    }
    if (loop_plan.shared_side_exit) |side_exit| {
        const exit = loop_plan.exit orelse return error.UnsupportedControlFlow;
        if (side_exit.entries.len == 0) return error.UnsupportedControlFlow;
        for (side_exit.entries) |entry| {
            if (entry.entry.index() >= program.blocks.len or
                entry.region.stop == null or entry.region.stop.? != exit or
                entry.region.nodes.len == 0 or entry.region.nodes[0].blockId() != entry.entry)
            {
                return error.UnsupportedControlFlow;
            }
            const side_flag = try escapeFlagNameAlloc(allocator, program, emission_plan, entry.entry);
            defer allocator.free(side_flag);
            try output.appendSlice(allocator, indent);
            try output.appendSlice(allocator, "local ");
            try output.appendSlice(allocator, side_flag);
            try output.appendSlice(allocator, " = false\n");
        }
    }
    const loop_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(loop_indent);
    const predeclared_header = if (structured_escape.regionHasNestedEscapeTo(loop_plan.body_region, loop_plan.header))
        loop_plan.header
    else
        null;
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "while true do\n");
    {
        // A lexical `continue` in the body or in the loop's own propagation binds to this loop.
        const loop_binder: ContinueBinder = .{ .kind = .loop, .header = loop_plan.header, .stop = loop_plan.body_region.stop, .parent = emission_plan.state.continue_binder };
        emission_plan.state.continue_binder = &loop_binder;
        defer emission_plan.state.continue_binder = loop_binder.parent;
        if (predeclared_header) |header| {
            try emitEscapeFlagDeclaration(output, allocator, program, emission_plan, header, loop_indent);
        }
        // The flag of the exit this loop owns starts false on every pass (`loopOwnedExitFlag`).
        if (structured_escape.loopOwnedExitFlag(enclosing_region, .{ .infinite_loop = loop_plan })) |exit_flag| {
            try emitEscapeFlagDeclaration(output, allocator, program, emission_plan, exit_flag, loop_indent);
        }
        try emitRegionWithPredeclaredBlock(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            loop_plan.body_region,
            loop_indent,
            place_aliases,
            predeclared_header,
        );
        try emitLoopEscapePropagation(
            output,
            allocator,
            program,
            emission_plan,
            .{ .infinite_loop = loop_plan },
            loop_indent,
            true,
        );
    }
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
    if (loop_plan.shared_side_exit) |side_exit| {
        for (side_exit.entries) |entry| {
            const side_flag = try escapeFlagNameAlloc(allocator, program, emission_plan, entry.entry);
            defer allocator.free(side_flag);
            const side_indent = try allocDeeperIndent(allocator, indent);
            defer allocator.free(side_indent);
            try output.appendSlice(allocator, indent);
            try output.appendSlice(allocator, "if ");
            try output.appendSlice(allocator, side_flag);
            try output.appendSlice(allocator, " then\n");
            try emitRegion(output, allocator, program, emission_plan, scopes, entry.region, side_indent, place_aliases);
            try output.appendSlice(allocator, indent);
            try output.appendSlice(allocator, "end\n");
        }
    }
}

fn emitLoopExit(output: *std.ArrayList(u8), allocator: std.mem.Allocator, program: *const ir.Program, emission_plan: *const EmissionPlan, scopes: *const emission_scope.Plan, edge: ir.Edge, indent: []const u8, place_aliases: []const PlaceAlias) !void {
    try emitEdgeParametersUnlessConsumed(output, allocator, program, emission_plan, scopes, program.blocks[edge.target.index()], edge.arguments, indent, false, place_aliases);
    try emitBreakStatement(output, allocator, indent);
}

/// Emit `return <values>` for an explicit value list, mirroring the ordinary `return_values`
/// terminator rendering (scalar uses for the leading values, a root use for the last).
fn emitReturnArguments(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    values: render.ValuePlan,
    arguments: []const ir.ValueId,
    indent: []const u8,
) !void {
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "return");
    if (arguments.len != 0) try output.append(allocator, ' ');
    for (arguments, 0..) |value, index| {
        if (index != 0) try output.appendSlice(allocator, ", ");
        if (index + 1 < arguments.len)
            try render.valueUseScalar(output, allocator, program, values, value)
        else
            try render.valueUseRoot(output, allocator, program, values, value);
    }
    try output.append(allocator, '\n');
}

/// Emit a loop's exit transfer. When the exit edge enters a privately owned return clone the loop
/// returns inline (`return <edge arguments>`) in place of the usual edge-parameter copy + `break`.
/// The return is wrapped in `do ... end` so it stays a non-terminal statement, exactly as
/// `emitBreakStatement` wraps `break`, because loop escape propagation is emitted after it in the
/// same block; the edge arguments are the clone's incoming values, already in scope, so the clone's
/// parameters (which are never declared, the clone not being walked) are not referenced.
fn emitLoopExitTransfer(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    edge: ir.Edge,
    exit_is_return_clone: bool,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) (EmitError || std.mem.Allocator.Error)!void {
    if (exit_is_return_clone) {
        const body_indent = try allocDeeperIndent(allocator, indent);
        defer allocator.free(body_indent);
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "do\n");
        try emitReturnArguments(output, allocator, program, valuePlan(emission_plan, place_aliases), edge.arguments, body_indent);
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "end\n");
        return;
    }
    try emitLoopExit(output, allocator, program, emission_plan, scopes, edge, indent, place_aliases);
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
) (EmitError || std.mem.Allocator.Error)!void {
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
        if (escapePropagationIsLoopContinue(target, loop_header)) {
            if (!continueBindsTo(emission_plan.state.continue_binder, target)) return error.UnsupportedControlFlow;
            try emitNativeIterationCompletionSetForTarget(output, allocator, emission_plan, target, break_indent);
            try output.appendSlice(allocator, break_indent);
            try output.appendSlice(allocator, "continue\n");
        } else {
            try output.appendSlice(allocator, break_indent);
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
) (EmitError || std.mem.Allocator.Error)!void {
    const flag = try escapeFlagNameAlloc(allocator, program, emission_plan, target);
    defer allocator.free(flag);
    const body_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(body_indent);
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "if ");
    try output.appendSlice(allocator, flag);
    try output.appendSlice(allocator, " then\n");
    try emitNativeIterationCompletionSetForTarget(output, allocator, emission_plan, target, body_indent);
    try emitContinueStatement(output, allocator, emission_plan, target, body_indent);
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
) (EmitError || std.mem.Allocator.Error)!void {
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
) (EmitError || std.mem.Allocator.Error)!void {
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
        structured_escape.regionHasNestedEscapeTo(region, loop_header.?) and
        writesStopConsumer(emission_plan.state.continue_binder, loop_header.?))
    {
        // The target is the region's owning loop stop, so consume a nested
        // transfer after the temporary wrapper has closed as a loop continue.
        try emitEscapeContinueIfSet(output, allocator, program, emission_plan, loop_header.?, indent);
    }
}

/// Whether the flag consumer of a region whose stop is its continue target is written after the region's wrapper.
/// Leaving the wrapper already reaches the stop, so the consumer is needed only where the stop is where the
/// innermost loop continues. It is not written when the stop is another block (the local stop of a loop-boundary
/// body, or of a region inside one that stops at the same block) and its `continue` would bind elsewhere: inside a
/// wrapper that stops at another block, or to a loop whose next pass starts at another block. It is written, as
/// before, where the innermost Luau loop statement reaches the stop, and where the stop is the innermost loop's
/// continue point or no loop is around it, so that emitContinueStatement still refuses a captured `continue`.
fn writesStopConsumer(binder: ?*const ContinueBinder, stop: ir.BlockId) bool {
    if (continueBindsTo(binder, stop)) return true;
    var outer = binder;
    while (outer) |statement| : (outer = statement.parent) {
        switch (statement.kind) {
            .wrapper => continue,
            .loop => return sameBlock(statement.header, stop) or sameBlock(statement.stop, stop),
            .one_shot => return true,
        }
    }
    return true;
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

fn emitLoopControl(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    region: *const structure.Region,
    node_index: usize,
    control: structure.LoopControl,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) !void {
    if (node_index + 1 != region.nodes.len or region.stop == null or region.loop_exit == null) return error.UnsupportedControlFlow;
    const block = program.blocks[control.block.index()];
    const branch = switch (block.terminator) {
        .branch => |value| value,
        else => return error.UnsupportedControlFlow,
    };
    const expected_continue = if (control.continue_on_true) branch.then_edge else branch.else_edge;
    const expected_exit = if (control.continue_on_true) branch.else_edge else branch.then_edge;
    if (expected_continue.target != region.stop.? or expected_exit.target != region.loop_exit.?) return error.UnsupportedControlFlow;
    try emitBlockInstructions(output, allocator, program, emission_plan, scopes, block, indent, place_aliases);

    const arm_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(arm_indent);
    if (edgeTransferIsStructurallyEmpty(program, scopes, control.continue_edge)) {
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, if (control.continue_on_true) "if not " else "if ");
        if (control.continue_on_true) {
            try render.valueUseGroupedScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), branch.condition);
        } else {
            try render.valueUseScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), branch.condition);
        }
        try output.appendSlice(allocator, " then\n");
        try emitLoopExit(output, allocator, program, emission_plan, scopes, control.exit_edge, arm_indent, place_aliases);
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "end\n");
        return;
    }
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "if ");
    try render.valueUseScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), branch.condition);
    try output.appendSlice(allocator, " then\n");
    if (control.continue_on_true) {
        try emitLoopContinue(output, allocator, program, emission_plan, scopes, control.continue_edge, arm_indent, place_aliases);
    } else {
        try emitLoopExit(output, allocator, program, emission_plan, scopes, control.exit_edge, arm_indent, place_aliases);
    }
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "else\n");
    if (control.continue_on_true) {
        try emitLoopExit(output, allocator, program, emission_plan, scopes, control.exit_edge, arm_indent, place_aliases);
    } else {
        try emitLoopContinue(output, allocator, program, emission_plan, scopes, control.continue_edge, arm_indent, place_aliases);
    }
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
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
    try emitNativeIterationCompletionSetForTarget(output, allocator, emission_plan, target, indent);
    try emitContinueStatement(output, allocator, emission_plan, target, indent);
}

fn emitProjectedContinueAfterTransferredEdge(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    edge: ir.Edge,
    target: ir.BlockId,
    indent: []const u8,
) (EmitError || std.mem.Allocator.Error)!void {
    _ = try loop_continue_projection.validateEntry(program, target, edge);
    try emitNativeIterationCompletionSetForTarget(output, allocator, emission_plan, target, indent);
    try emitContinueStatement(output, allocator, emission_plan, target, indent);
}

/// Whether a lexical `continue` written under `binder`, the innermost Luau loop statement, reaches `target`: the
/// binder is a loop whose header or body stop is `target`, or a transfer wrapper whose stop is `target` (leaving a
/// wrapper reaches its stop) or is the body stop of the innermost loop around it, whose header is `target`. A `for`
/// that runs its body once binds no `continue`, and neither does the absence of a loop statement.
fn continueBindsTo(binder: ?*const ContinueBinder, target: ir.BlockId) bool {
    const innermost = binder orelse return false;
    switch (innermost.kind) {
        .loop => return sameBlock(innermost.header, target) or sameBlock(innermost.stop, target),
        .one_shot => return false,
        .wrapper => {
            if (sameBlock(innermost.stop, target)) return true;
            var outer = innermost.parent;
            while (outer) |enclosing| : (outer = enclosing.parent) {
                if (enclosing.kind == .wrapper) continue;
                return enclosing.kind == .loop and sameBlock(enclosing.header, target) and
                    enclosing.stop != null and sameBlock(innermost.stop, enclosing.stop.?);
            }
            return false;
        },
    }
}

fn sameBlock(block: ?ir.BlockId, target: ir.BlockId) bool {
    return block != null and block.? == target;
}

/// A lexical `continue` to `target`, written only where it binds to a loop statement that reaches `target`;
/// anywhere else the function is refused, and emitFunctionBody writes it in the flat layout.
fn emitContinueStatement(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    emission_plan: *const EmissionPlan,
    target: ir.BlockId,
    indent: []const u8,
) (EmitError || std.mem.Allocator.Error)!void {
    if (!continueBindsTo(emission_plan.state.continue_binder, target)) return error.UnsupportedControlFlow;
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

fn emitLoopBoundaryControl(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    region: *const structure.Region,
    node_index: usize,
    control: structure.LoopBoundaryControl,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) !void {
    if (node_index + 1 != region.nodes.len or region.stop == null) {
        return error.UnsupportedControlFlow;
    }
    const body_exit = try transparent_stop.validateLoopBoundaryBody(
        program,
        region.stop,
        region.loop_exit,
        region.continue_target,
        control.body_region.stop,
        control.body_region.loop_exit,
        control.body_region.continue_target,
    );
    const block = program.blocks[control.block.index()];
    const branch = switch (block.terminator) {
        .branch => |value| value,
        else => return error.UnsupportedControlFlow,
    };
    const expected_body = if (control.body_on_true) branch.then_edge else branch.else_edge;
    const expected_boundary = if (control.body_on_true) branch.else_edge else branch.then_edge;
    if (expected_body.target != control.body_edge.target) return error.UnsupportedControlFlow;
    switch (control.boundary) {
        .exit => |edge| if (region.loop_exit == null or edge.target != expected_boundary.target or edge.target != region.loop_exit.?) return error.UnsupportedControlFlow,
        .escape => |edge| if (edge.target != expected_boundary.target) return error.UnsupportedControlFlow,
        .terminal => |terminal| if (terminal.edge.target != expected_boundary.target or terminal.edge.target != terminal.block) return error.UnsupportedControlFlow,
        .side_exit => |side_exit| if (region.loop_exit == null or side_exit.entry_edge.target != expected_boundary.target or
            side_exit.region.stop == null or side_exit.region.stop.? != region.loop_exit.?) return error.UnsupportedControlFlow,
        .side_escape => |side_escape| if (side_escape.entry_edge.target != expected_boundary.target or
            side_escape.region.stop == null or side_escape.region.stop.? != side_escape.target) return error.UnsupportedControlFlow,
        .shared_exit => |shared_exit| {
            if (region.loop_exit == null) return error.UnsupportedControlFlow;
            const entry = shared_exit.value() orelse return error.UnsupportedControlFlow;
            const expected_reference: ir.CfgEdgeRef = .{
                .source = control.block,
                .kind = if (control.body_on_true) .branch_else else .branch_then,
                .target = expected_boundary.target,
            };
            if (shared_exit.owner.exit != region.loop_exit.? or
                !std.meta.eql(entry.reference, expected_reference)) return error.UnsupportedControlFlow;
            try loop_exit_shape.validateEntryAlloc(allocator, program, shared_exit);
        },
    }
    if (scopes.nativeIterationConsumesParameters(control.block)) {
        if (try iteration_protocol.matchAcyclicLoopBoundary(allocator, program, control)) |acyclic| {
            return emitLoopBoundaryNativeIteration(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                region,
                node_index,
                control,
                acyclic,
                body_exit,
                indent,
                place_aliases,
            );
        }
    }
    try emitBlockInstructions(output, allocator, program, emission_plan, scopes, block, indent, place_aliases);

    const arm_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(arm_indent);
    // A side escape that falls through to this region's end is written with no flag and no `break`.
    const side_falls_through = structured_escape.regionSideEscapeFallsThrough(region);
    if (body_exit == .parent_stop and branchArmIsStructurallyEmpty(program, control.body_edge, control.body_region, null)) {
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, if (control.body_on_true) "if not " else "if ");
        if (control.body_on_true) {
            try render.valueUseGroupedScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), branch.condition);
        } else {
            try render.valueUseScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), branch.condition);
        }
        try output.appendSlice(allocator, " then\n");
        try emitLoopBoundaryArm(output, allocator, program, emission_plan, scopes, control.boundary, side_falls_through, arm_indent, place_aliases);
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "end\n");
        return;
    }
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "if ");
    try render.valueUseScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), branch.condition);
    try output.appendSlice(allocator, " then\n");
    if (control.body_on_true) {
        try emitLoopBoundaryBody(output, allocator, program, emission_plan, scopes, control, body_exit, region.continue_target, arm_indent, place_aliases);
    } else {
        try emitLoopBoundaryArm(output, allocator, program, emission_plan, scopes, control.boundary, side_falls_through, arm_indent, place_aliases);
    }
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "else\n");
    if (control.body_on_true) {
        try emitLoopBoundaryArm(output, allocator, program, emission_plan, scopes, control.boundary, side_falls_through, arm_indent, place_aliases);
    } else {
        try emitLoopBoundaryBody(output, allocator, program, emission_plan, scopes, control, body_exit, region.continue_target, arm_indent, place_aliases);
    }
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

/// A native iteration header planned as a loop boundary whose boundary arm is the
/// iteration body. The header's own block is not written (its only instruction is the transition, which the native
/// activation suppresses). The body is written inside `for <bindings> ... do ... end`, which binds the body
/// parameters, and the exit arm follows the loop, so a `continue` or `break` it writes binds to the enclosing loop.
fn emitLoopBoundaryNativeIteration(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    region: *const structure.Region,
    node_index: usize,
    control: structure.LoopBoundaryControl,
    acyclic: iteration_protocol.AcyclicBoundary,
    body_exit: transparent_stop.LoopBoundaryBodyExit,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) !void {
    switch (control.boundary) {
        .terminal => |terminal| {
            switch (acyclic.protocol) {
                .numeric => |numeric| try emitNumericForOpen(output, allocator, program, emission_plan, numeric, indent, place_aliases),
                .generic => |generic| try emitGenericForOpen(output, allocator, program, emission_plan, scopes, generic, indent, place_aliases),
            }
            const loop_indent = try allocDeeperIndent(allocator, indent);
            defer allocator.free(loop_indent);
            // What `emitOwnedTerminalArm` writes, without its edge parameters: the `for` binds the body parameter.
            const body = program.blocks[terminal.block.index()];
            try emitBlockInstructions(output, allocator, program, emission_plan, scopes, body, loop_indent, place_aliases);
            try call_emission.terminator(output, allocator, program, emission_plan, body, loop_indent, valuePlan(emission_plan, place_aliases));
            try output.appendSlice(allocator, indent);
            try output.appendSlice(allocator, "end\n");
        },
        .side_exit => |side_exit| switch (acyclic.protocol) {
            .numeric => |numeric| try emitNumericForLoop(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                region,
                node_index,
                side_exit.region,
                null,
                numeric,
                true,
                indent,
                place_aliases,
            ),
            .generic => |generic| try emitGenericForLoop(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                region,
                node_index,
                side_exit.region,
                null,
                generic,
                true,
                indent,
                place_aliases,
            ),
        },
        else => return error.UnsupportedControlFlow,
    }
    if (body_exit == .parent_stop and branchArmIsStructurallyEmpty(program, control.body_edge, control.body_region, null)) return;
    try emitLoopBoundaryBody(output, allocator, program, emission_plan, scopes, control, body_exit, region.continue_target, indent, place_aliases);
}

fn emitLoopBoundaryBodyImpl(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    control: structure.LoopBoundaryControl,
    body_exit: transparent_stop.LoopBoundaryBodyExit,
    continue_target: ?ir.BlockId,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) !void {
    const entry = program.blocks[control.body_edge.target.index()];
    const enters_loop_header = control.body_region.stop != null and control.body_edge.target == control.body_region.stop.?;
    try emitEdgeParametersUnlessConsumed(output, allocator, program, emission_plan, scopes, entry, control.body_edge.arguments, indent, !enters_loop_header, place_aliases);
    if (try validateEmptyBoundaryContinue(program, control.body_region, control.body_edge)) |transfer| {
        if (transfer.nonlocal) {
            try emitEscapeFlagSet(output, allocator, program, emission_plan, transfer.target, indent);
        } else {
            try emitNativeIterationCompletionSetForTarget(output, allocator, emission_plan, transfer.target, indent);
            try emitContinueStatement(output, allocator, emission_plan, transfer.target, indent);
        }
        return;
    }
    try emitRegion(output, allocator, program, emission_plan, scopes, control.body_region, indent, place_aliases);
    // No termination test: a body region whose last node returns is written inside a transfer wrapper (when
    // that node is a branch, each returning arm is), so this continue never follows a bare return; after a
    // wrapped region it is where a continue the wrapper captures resumes, so it must stay.
    if (body_exit == .continue_target and control.body_region.continue_projection == null) {
        if (control.continue_via_flag) {
            // Carried by flag (`structure.markFlaggedContinues`): the innermost Luau loop statement here is a transfer
            // wrapper that stops at another block, so set the loop header's flag and leave the wrapper; each wrapper on
            // the way forwards the flag, and the loop body's wrapper consumes it as a `continue`.
            try emitEscapeFlagSet(output, allocator, program, emission_plan, continue_target orelse return error.UnsupportedControlFlow, indent);
            try emitEmptyArmFlagBreak(output, allocator, emission_plan, indent);
            return;
        }
        try emitNativeIterationCompletionSetForTarget(
            output,
            allocator,
            emission_plan,
            continue_target orelse return error.UnsupportedControlFlow,
            indent,
        );
        try emitContinueStatement(output, allocator, emission_plan, continue_target.?, indent);
    }
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

fn emitLoopBoundaryBody(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    control: structure.LoopBoundaryControl,
    body_exit: transparent_stop.LoopBoundaryBodyExit,
    continue_target: ?ir.BlockId,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) !void {
    try emitLoopBoundaryBodyImpl(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        control,
        body_exit,
        continue_target,
        indent,
        place_aliases,
    );
}

fn emitLoopBoundaryArmImpl(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    boundary: structure.LoopBoundary,
    side_falls_through: bool,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) !void {
    switch (boundary) {
        .exit => |edge| {
            try emitEdgeParametersUnlessConsumed(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                program.blocks[edge.target.index()],
                edge.arguments,
                indent,
                false,
                place_aliases,
            );
            try emitEscapeFlagSet(output, allocator, program, emission_plan, edge.target, indent);
            try emitBreakStatement(output, allocator, indent);
        },
        .escape => |edge| {
            try emitEdgeParametersUnlessConsumed(output, allocator, program, emission_plan, scopes, program.blocks[edge.target.index()], edge.arguments, indent, false, place_aliases);
            try emitEscapeFlagSet(output, allocator, program, emission_plan, edge.target, indent);
            try emitBreakStatement(output, allocator, indent);
        },
        .terminal => |terminal| try emitOwnedTerminalArm(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            terminal.edge,
            terminal.block,
            indent,
            place_aliases,
        ),
        .side_exit => |side_exit| {
            const entry = program.blocks[side_exit.entry_edge.target.index()];
            try emitEdgeParametersUnlessConsumed(output, allocator, program, emission_plan, scopes, entry, side_exit.entry_edge.arguments, indent, true, place_aliases);
            try emitRegion(output, allocator, program, emission_plan, scopes, side_exit.region, indent, place_aliases);
            if (!regionAlwaysFunctionTerminates(program, side_exit.region)) {
                try emitBreakStatement(output, allocator, indent);
            }
        },
        .side_escape => |side_escape| {
            const entry = program.blocks[side_escape.entry_edge.target.index()];
            try emitEdgeParametersUnlessConsumed(output, allocator, program, emission_plan, scopes, entry, side_escape.entry_edge.arguments, indent, true, place_aliases);
            // A side escape that falls through to the holding region's end reaches it by leaving this arm
            // (`structure.regionSideEscapeFallsThrough`): no flag and no `break`.
            const writes_side_flag = !side_falls_through and !regionAlwaysFunctionTerminates(program, side_escape.region);
            // Where this arm sets the side target's flag after the side region, the side region declares no flag
            // of that name: the set must reach the flag of the region or loop that owns the side target.
            try emitRegionPredeclared(
                output,
                allocator,
                program,
                emission_plan,
                scopes,
                side_escape.region,
                indent,
                place_aliases,
                if (writes_side_flag) side_escape.target else null,
            );
            if (writes_side_flag) {
                const free_targets = try structured_escape.regionFreeTargetsAlloc(allocator, side_escape.region);
                defer allocator.free(free_targets);
                if (free_targets.len == 0) {
                    try emitEscapeFlagSet(output, allocator, program, emission_plan, side_escape.target, indent);
                    try emitBreakStatement(output, allocator, indent);
                } else {
                    const fallback_indent = try allocDeeperIndent(allocator, indent);
                    defer allocator.free(fallback_indent);
                    try output.appendSlice(allocator, indent);
                    try output.appendSlice(allocator, "if ");
                    for (free_targets, 0..) |target, index| {
                        if (index != 0) try output.appendSlice(allocator, " and ");
                        try output.appendSlice(allocator, "not ");
                        const flag = try escapeFlagNameAlloc(allocator, program, emission_plan, target);
                        defer allocator.free(flag);
                        try output.appendSlice(allocator, flag);
                    }
                    try output.appendSlice(allocator, " then\n");
                    try emitEscapeFlagSet(output, allocator, program, emission_plan, side_escape.target, fallback_indent);
                    try emitBreakStatement(output, allocator, fallback_indent);
                    try output.appendSlice(allocator, indent);
                    try output.appendSlice(allocator, "end\n");
                }
            }
        },
        .shared_exit => |shared_exit| {
            try loop_exit_shape.validateEntryAlloc(allocator, program, shared_exit);
            try emitBreakStatement(output, allocator, indent);
        },
    }
}

fn emitLoopBoundaryArm(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    boundary: structure.LoopBoundary,
    side_falls_through: bool,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) !void {
    try emitLoopBoundaryArmImpl(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        boundary,
        side_falls_through,
        indent,
        place_aliases,
    );
}

fn emitLoopTerminalControl(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    region: *const structure.Region,
    node_index: usize,
    control: structure.LoopTerminalControl,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) !void {
    if (node_index + 1 != region.nodes.len or region.stop == null) return error.UnsupportedControlFlow;
    const block = program.blocks[control.block.index()];
    const branch = switch (block.terminator) {
        .branch => |value| value,
        else => return error.UnsupportedControlFlow,
    };
    const expected_continue = if (control.continue_on_true) branch.then_edge else branch.else_edge;
    const expected_terminal = if (control.continue_on_true) branch.else_edge else branch.then_edge;
    if (expected_continue.target != region.stop.? or expected_terminal.target != control.terminal_block) return error.UnsupportedControlFlow;
    try emitBlockInstructions(output, allocator, program, emission_plan, scopes, block, indent, place_aliases);

    const arm_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(arm_indent);
    if (edgeTransferIsStructurallyEmpty(program, scopes, control.continue_edge)) {
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, if (control.continue_on_true) "if not " else "if ");
        if (control.continue_on_true) {
            try render.valueUseGroupedScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), branch.condition);
        } else {
            try render.valueUseScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), branch.condition);
        }
        try output.appendSlice(allocator, " then\n");
        try emitOwnedTerminalArm(output, allocator, program, emission_plan, scopes, control.terminal_edge, control.terminal_block, arm_indent, place_aliases);
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "end\n");
        return;
    }
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "if ");
    try render.valueUseScalar(output, allocator, program, valuePlan(emission_plan, place_aliases), branch.condition);
    try output.appendSlice(allocator, " then\n");
    if (control.continue_on_true) {
        try emitLoopContinue(output, allocator, program, emission_plan, scopes, control.continue_edge, arm_indent, place_aliases);
    } else {
        try emitOwnedTerminalArm(output, allocator, program, emission_plan, scopes, control.terminal_edge, control.terminal_block, arm_indent, place_aliases);
    }
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "else\n");
    if (control.continue_on_true) {
        try emitOwnedTerminalArm(output, allocator, program, emission_plan, scopes, control.terminal_edge, control.terminal_block, arm_indent, place_aliases);
    } else {
        try emitLoopContinue(output, allocator, program, emission_plan, scopes, control.continue_edge, arm_indent, place_aliases);
    }
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

fn emitOwnedTerminalArm(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    terminal_edge: ir.Edge,
    terminal_block: ir.BlockId,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
) !void {
    const terminal = program.blocks[terminal_block.index()];
    try emitEdgeParameters(output, allocator, program, emission_plan, terminal, terminal_edge.arguments, indent, true, place_aliases);
    try emitBlockInstructions(output, allocator, program, emission_plan, scopes, terminal, indent, place_aliases);
    try call_emission.terminator(output, allocator, program, emission_plan, terminal, indent, valuePlan(emission_plan, place_aliases));
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
    if (scopes.edgeParametersConsumed(target.id)) return;
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

test "a propagated continue to a guarded native header writes its completion flag at the arm's indent" {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const function_blocks = [_]ir.BlockId{ ir.BlockId.fromIndex(0), header };
    const blocks = [_]ir.Block{
        .{ .id = ir.BlockId.fromIndex(0), .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = header, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &function_blocks, .entry_block = ir.BlockId.fromIndex(0) }};
    const program: ir.Program = .{
        .program_id = "native-completion-propagated-continue",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var plan = try EmissionPlan.init(allocator, &program, .standard_luau);
    defer plan.deinit();
    var completion: NativeIterationCompletion = .{ .header = header, .flag_name = "__lifter_native_iteration_complete_1" };
    plan.state.native_iteration_completion = &completion;
    defer plan.state.native_iteration_completion = null;
    const header_loop: ContinueBinder = .{ .kind = .loop, .header = header, .stop = header };
    plan.state.continue_binder = &header_loop;
    defer plan.state.continue_binder = null;

    var propagated: std.ArrayList(u8) = .empty;
    defer propagated.deinit(allocator);
    try emitEscapePropagation(&propagated, allocator, &program, &plan, &.{header}, "    ", header);
    try std.testing.expectEqualStrings(
        "    if __lifter_escape_1 then\n" ++
            "      __lifter_native_iteration_complete_1 = true\n" ++
            "      continue\n" ++
            "    end\n",
        propagated.items,
    );

    var continued: std.ArrayList(u8) = .empty;
    defer continued.deinit(allocator);
    try emitEscapeContinueIfSet(&continued, allocator, &program, &plan, header, "    ");
    try std.testing.expectEqualStrings(
        "    if __lifter_escape_1 then\n" ++
            "      __lifter_native_iteration_complete_1 = true\n" ++
            "      do\n" ++
            "        continue\n" ++
            "      end\n" ++
            "    end\n",
        continued.items,
    );

    // Without a context for the header neither writer writes a completion flag.
    plan.state.native_iteration_completion = null;
    var unguarded: std.ArrayList(u8) = .empty;
    defer unguarded.deinit(allocator);
    try emitEscapePropagation(&unguarded, allocator, &program, &plan, &.{header}, "    ", header);
    try emitEscapeContinueIfSet(&unguarded, allocator, &program, &plan, header, "    ");
    try std.testing.expectEqualStrings(
        "    if __lifter_escape_1 then\n" ++
            "      continue\n" ++
            "    end\n" ++
            "    if __lifter_escape_1 then\n" ++
            "      do\n" ++
            "        continue\n" ++
            "      end\n" ++
            "    end\n",
        unguarded.items,
    );
}

test "explicit continues to a guarded native header write its completion flag before do continue end" {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const function_blocks = [_]ir.BlockId{ entry, header };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &function_blocks, .entry_block = entry }};
    const program: ir.Program = .{
        .program_id = "native-completion-explicit-continues",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var plan = try EmissionPlan.init(allocator, &program, .standard_luau);
    defer plan.deinit();
    // The scope plan of the program's one function: the writers below read it only to ask whether a native loop
    // consumes the header's parameters (it does not here, and the header has none).
    var analysis = try cfg.Analysis.init(allocator, &program, functions[0]);
    defer analysis.deinit();
    var structured = try structure.Plan.initWithArbitraryFallback(allocator, &analysis);
    defer structured.deinit();
    var scopes = try emission_scope.Plan.init(
        allocator,
        &program,
        functions[0],
        &analysis,
        &structured,
        &plan.packs,
        &plan.dead,
        &plan.place_writes,
        &plan.place_reads,
        &plan.fused_values,
        &plan.closure_stores,
    );
    defer scopes.deinit();
    var completion: NativeIterationCompletion = .{ .header = header, .flag_name = "__lifter_native_iteration_complete_1" };
    plan.state.native_iteration_completion = &completion;
    defer plan.state.native_iteration_completion = null;
    const header_loop: ContinueBinder = .{ .kind = .loop, .header = header, .stop = header };
    plan.state.continue_binder = &header_loop;
    defer plan.state.continue_binder = null;
    const to_header: ir.Edge = .{ .target = header };
    const guarded_continue =
        "    __lifter_native_iteration_complete_1 = true\n" ++
        "    do\n" ++
        "      continue\n" ++
        "    end\n";

    var escaped: std.ArrayList(u8) = .empty;
    defer escaped.deinit(allocator);
    try emitEscapeContinueIfSet(&escaped, allocator, &program, &plan, header, "    ");
    try std.testing.expectEqualStrings(
        "    if __lifter_escape_1 then\n" ++
            "      __lifter_native_iteration_complete_1 = true\n" ++
            "      do\n" ++
            "        continue\n" ++
            "      end\n" ++
            "    end\n",
        escaped.items,
    );

    var projected: std.ArrayList(u8) = .empty;
    defer projected.deinit(allocator);
    try emitProjectedContinue(&projected, allocator, &program, &plan, &scopes, to_header, header, "    ", &.{}, false);
    try std.testing.expectEqualStrings(guarded_continue, projected.items);

    var transferred: std.ArrayList(u8) = .empty;
    defer transferred.deinit(allocator);
    try emitProjectedContinueAfterTransferredEdge(&transferred, allocator, &program, &plan, to_header, header, "    ");
    try std.testing.expectEqualStrings(guarded_continue, transferred.items);

    // An empty loop-boundary body whose local continue projection enters the header.
    var empty_nodes = [_]structure.Node{};
    var projected_region = structure.Region{
        .nodes = &empty_nodes,
        .stop = entry,
        .loop_exit = null,
        .continue_target = header,
        .continue_projection = .{ .target = header, .edge = null },
    };
    const projected_control: structure.LoopBoundaryControl = .{
        .block = entry,
        .body_edge = to_header,
        .body_region = &projected_region,
        .boundary = .{ .exit = .{ .target = entry } },
        .body_on_true = true,
    };
    var empty_body: std.ArrayList(u8) = .empty;
    defer empty_body.deinit(allocator);
    try emitLoopBoundaryBodyImpl(&empty_body, allocator, &program, &plan, &scopes, projected_control, .parent_stop, header, "    ", &.{});
    try std.testing.expectEqualStrings(guarded_continue, empty_body.items);

    // A loop-boundary body region that stops at the holding region's continue target.
    var stopping_region = structure.Region{
        .nodes = &empty_nodes,
        .stop = header,
        .loop_exit = null,
        .continue_target = header,
    };
    const stopping_control: structure.LoopBoundaryControl = .{
        .block = entry,
        .body_edge = to_header,
        .body_region = &stopping_region,
        .boundary = .{ .exit = .{ .target = entry } },
        .body_on_true = true,
    };
    var stopping_body: std.ArrayList(u8) = .empty;
    defer stopping_body.deinit(allocator);
    try emitLoopBoundaryBodyImpl(&stopping_body, allocator, &program, &plan, &scopes, stopping_control, .continue_target, header, "    ", &.{});
    try std.testing.expectEqualStrings(guarded_continue, stopping_body.items);

    // A context for another header writes no completion flag.
    var other: NativeIterationCompletion = .{ .header = entry, .flag_name = "__lifter_native_iteration_complete_0" };
    plan.state.native_iteration_completion = &other;
    var unmatched: std.ArrayList(u8) = .empty;
    defer unmatched.deinit(allocator);
    try emitProjectedContinueAfterTransferredEdge(&unmatched, allocator, &program, &plan, to_header, header, "    ");
    try std.testing.expectEqualStrings("    do\n      continue\n    end\n", unmatched.items);
}

test "a lexical continue is written only where its loop statement reaches the target" {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const forwarder = ir.BlockId.fromIndex(2);
    const join = ir.BlockId.fromIndex(3);

    // A loop continues at its header, and at its body stop when that block forwards to the header.
    const header_loop: ContinueBinder = .{ .kind = .loop, .header = header, .stop = header };
    const forwarded_loop: ContinueBinder = .{ .kind = .loop, .header = header, .stop = forwarder };
    try std.testing.expect(continueBindsTo(&header_loop, header));
    try std.testing.expect(continueBindsTo(&forwarded_loop, header));
    try std.testing.expect(continueBindsTo(&forwarded_loop, forwarder));
    try std.testing.expect(!continueBindsTo(&header_loop, join));
    // Leaving a transfer wrapper reaches its stop: a continue to that stop is right, and so is a continue to the
    // header of the innermost loop whose body stop the wrapper stops at; a continue to the header inside a wrapper
    // that stops at a join is not.
    const stops_at_join: ContinueBinder = .{ .kind = .wrapper, .stop = join, .parent = &header_loop };
    try std.testing.expect(continueBindsTo(&stops_at_join, join));
    try std.testing.expect(!continueBindsTo(&stops_at_join, header));
    const stops_at_forwarder: ContinueBinder = .{ .kind = .wrapper, .stop = forwarder, .parent = &forwarded_loop };
    const nested_at_forwarder: ContinueBinder = .{ .kind = .wrapper, .stop = forwarder, .parent = &stops_at_forwarder };
    const nested_at_join: ContinueBinder = .{ .kind = .wrapper, .stop = join, .parent = &stops_at_forwarder };
    try std.testing.expect(continueBindsTo(&stops_at_forwarder, header));
    try std.testing.expect(continueBindsTo(&nested_at_forwarder, header));
    try std.testing.expect(!continueBindsTo(&nested_at_join, header));
    // A `for` that runs its body once binds no continue, and a wrapper inside it reaches only its own stop.
    const once: ContinueBinder = .{ .kind = .one_shot, .parent = &header_loop };
    const inside_once: ContinueBinder = .{ .kind = .wrapper, .stop = join, .parent = &once };
    try std.testing.expect(!continueBindsTo(&once, header));
    try std.testing.expect(!continueBindsTo(&inside_once, header));
    try std.testing.expect(continueBindsTo(&inside_once, join));
    // Outside every loop statement nothing binds.
    try std.testing.expect(!continueBindsTo(null, header));

    // The writers refuse a continue whose binder does not reach the target, and write it where it does.
    const function_blocks = [_]ir.BlockId{ ir.BlockId.fromIndex(0), header, forwarder, join };
    const blocks = [_]ir.Block{
        .{ .id = ir.BlockId.fromIndex(0), .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = header, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = forwarder, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = join, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &function_blocks, .entry_block = ir.BlockId.fromIndex(0) }};
    const program: ir.Program = .{
        .program_id = "continue-binder",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var plan = try EmissionPlan.init(allocator, &program, .standard_luau);
    defer plan.deinit();
    defer plan.state.continue_binder = null;
    var refused: std.ArrayList(u8) = .empty;
    defer refused.deinit(allocator);
    for ([_]?*const ContinueBinder{ null, &stops_at_join, &once, &inside_once }) |binder| {
        plan.state.continue_binder = binder;
        try std.testing.expectError(error.UnsupportedControlFlow, emitContinueStatement(&refused, allocator, &plan, header, "    "));
        try std.testing.expectError(error.UnsupportedControlFlow, emitEscapeContinueIfSet(&refused, allocator, &program, &plan, header, "    "));
        try std.testing.expectError(error.UnsupportedControlFlow, emitEscapePropagation(&refused, allocator, &program, &plan, &.{header}, "    ", header));
    }
    plan.state.continue_binder = &stops_at_join;
    var written: std.ArrayList(u8) = .empty;
    defer written.deinit(allocator);
    try emitContinueStatement(&written, allocator, &plan, join, "    ");
    plan.state.continue_binder = &nested_at_forwarder;
    try emitEscapeContinueIfSet(&written, allocator, &program, &plan, header, "    ");
    try std.testing.expectEqualStrings(
        "    do\n" ++
            "      continue\n" ++
            "    end\n" ++
            "    if __lifter_escape_1 then\n" ++
            "      do\n" ++
            "        continue\n" ++
            "      end\n" ++
            "    end\n",
        written.items,
    );
}

test "a continue carried by flag owns its region's wrapper in the register budget" {
    const header = ir.BlockId.fromIndex(1);
    const join = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    var arm_nodes = [_]structure.Node{.{ .block = ir.BlockId.fromIndex(4) }};
    var arm = structure.Region{
        .nodes = &arm_nodes,
        .stop = join,
        .loop_exit = exit,
        .continue_target = header,
        .continue_projection = .{ .target = header, .edge = null },
    };
    var empty_arm = structure.Region{ .nodes = &.{}, .stop = join, .loop_exit = exit, .continue_target = header };
    var body_nodes = [_]structure.Node{
        .{ .branch = .{ .block = ir.BlockId.fromIndex(5), .then_region = &arm, .else_region = &empty_arm, .join = join } },
        .{ .block = join },
    };
    var body = structure.Region{ .nodes = &body_nodes, .stop = header, .loop_exit = exit, .continue_target = header };
    var root_nodes = [_]structure.Node{.{ .latch_loop = .{ .header = header, .body_region = &body, .exit = exit, .latch_count = 1 } }};
    const root = structure.Region{ .nodes = &root_nodes, .stop = null, .loop_exit = null };
    // Written as a lexical continue, the arm's continue adds no wrapper.
    try std.testing.expectEqual(@as(usize, 0), structured_escape.maxOwnedDepth(&root));
    // Carried by flag, it owns a wrapper around its arm, and the loop body owns the wrapper that consumes the flag:
    // the register budget counts both flags.
    arm.continue_projection.?.via_flag = true;
    try std.testing.expect(structured_escape.regionOwnsEscape(&arm));
    try std.testing.expect(structured_escape.regionOwnsEscape(&body));
    try std.testing.expectEqual(@as(usize, 2), structured_escape.maxOwnedDepth(&root));
}

test "a flag consumer after a wrapper is written only where it reaches the stop or the loop continues there" {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const join = ir.BlockId.fromIndex(2);
    const other = ir.BlockId.fromIndex(3);

    const loop: ContinueBinder = .{ .kind = .loop, .header = header, .stop = header };
    const at_other: ContinueBinder = .{ .kind = .wrapper, .stop = other, .parent = &loop };
    const at_join: ContinueBinder = .{ .kind = .wrapper, .stop = join, .parent = &loop };
    const once: ContinueBinder = .{ .kind = .one_shot, .parent = &loop };
    // A stop where the loop continues: written, bound there or captured (emitContinueStatement then refuses).
    try std.testing.expect(writesStopConsumer(&loop, header));
    try std.testing.expect(writesStopConsumer(&at_other, header));
    // Another stop: written where a wrapper stops at it, not where its continue would bind to the loop or to a
    // wrapper that stops elsewhere.
    try std.testing.expect(writesStopConsumer(&at_join, join));
    try std.testing.expect(!writesStopConsumer(&loop, join));
    try std.testing.expect(!writesStopConsumer(&at_other, join));
    // Inside a `for` that runs its body once: written, so emitContinueStatement refuses the function.
    try std.testing.expect(writesStopConsumer(&once, join));

    // The writer: a region whose stop is its continue target, `join`, and whose nested arm escapes to it.
    const function_blocks = [_]ir.BlockId{ ir.BlockId.fromIndex(0), header, join, other };
    const blocks = [_]ir.Block{
        .{ .id = ir.BlockId.fromIndex(0), .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = header, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = join, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = other, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &function_blocks, .entry_block = ir.BlockId.fromIndex(0) }};
    const program: ir.Program = .{
        .program_id = "stop-consumer",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var plan = try EmissionPlan.init(allocator, &program, .standard_luau);
    defer plan.deinit();
    defer plan.state.continue_binder = null;
    var escape_arm = structure.Region{ .nodes = &.{}, .stop = other, .loop_exit = null, .escape_projection = .{ .target = join, .edge = null } };
    var empty_arm = structure.Region{ .nodes = &.{}, .stop = join, .loop_exit = null, .continue_target = join };
    var nodes = [_]structure.Node{.{ .branch = .{ .block = other, .then_region = &escape_arm, .else_region = &empty_arm, .join = null } }};
    const region = structure.Region{ .nodes = &nodes, .stop = join, .loop_exit = null, .continue_target = join };
    var dropped: std.ArrayList(u8) = .empty;
    defer dropped.deinit(allocator);
    plan.state.continue_binder = &loop;
    try emitRegionEscapePropagation(&dropped, allocator, &program, &plan, &region, "    ");
    plan.state.continue_binder = &at_other;
    try emitRegionEscapePropagation(&dropped, allocator, &program, &plan, &region, "    ");
    try std.testing.expectEqualStrings("", dropped.items);
    var written: std.ArrayList(u8) = .empty;
    defer written.deinit(allocator);
    plan.state.continue_binder = &at_join;
    try emitRegionEscapePropagation(&written, allocator, &program, &plan, &region, "    ");
    try std.testing.expectEqualStrings(
        "    if __lifter_escape_2 then\n" ++
            "      do\n" ++
            "        continue\n" ++
            "      end\n" ++
            "    end\n",
        written.items,
    );
}

test "a side region declares no flag of the side target its arm sets after it" {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const side_entry = ir.BlockId.fromIndex(1);
    const side_target = ir.BlockId.fromIndex(2);
    const free_target = ir.BlockId.fromIndex(3);
    const function_blocks = [_]ir.BlockId{ entry, side_entry, side_target, free_target };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = side_entry } } },
        .{ .id = side_entry, .function = function_id, .terminator = .{ .jump = .{ .target = side_target } } },
        .{ .id = side_target, .function = function_id, .terminator = .{ .jump = .{ .target = free_target } } },
        .{ .id = free_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &function_blocks, .entry_block = entry }};
    const program: ir.Program = .{
        .program_id = "side-escape-declaration",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var plan = try EmissionPlan.init(allocator, &program, .standard_luau);
    defer plan.deinit();
    // The scope plan of the program's one function: the arm reads it only to ask whether a native loop consumes the
    // side region's entry parameters (it does not, and the entry has none).
    var analysis = try cfg.Analysis.init(allocator, &program, functions[0]);
    defer analysis.deinit();
    var structured = try structure.Plan.initWithArbitraryFallback(allocator, &analysis);
    defer structured.deinit();
    var scopes = try emission_scope.Plan.init(
        allocator,
        &program,
        functions[0],
        &analysis,
        &structured,
        &plan.packs,
        &plan.dead,
        &plan.place_writes,
        &plan.place_reads,
        &plan.fused_values,
        &plan.closure_stores,
    );
    defer scopes.deinit();
    // The side region leaves for another block on one path (its escape projection to `free_target`, a free target), so
    // it is written inside a transfer wrapper that stops at the side target.
    var side_region = structure.Region{
        .nodes = &.{},
        .stop = side_target,
        .loop_exit = null,
        .escape_projection = .{ .target = free_target, .edge = null },
    };
    const boundary: structure.LoopBoundary = .{ .side_escape = .{
        .entry_edge = .{ .target = side_entry },
        .region = &side_region,
        .target = side_target,
    } };
    const wrapped_side_region =
        "    repeat\n" ++
        "      __lifter_escape_3 = true\n" ++
        "      do\n" ++
        "        break\n" ++
        "      end\n" ++
        "    until true\n" ++
        "    if __lifter_escape_3 then\n" ++
        "      break\n" ++
        "    end\n";

    // The arm sets the side target's flag after the side region: the region's wrapper declares no flag of that name,
    // so the set reaches the flag of the region or loop that owns the side target.
    var sets_after: std.ArrayList(u8) = .empty;
    defer sets_after.deinit(allocator);
    try emitLoopBoundaryArmImpl(&sets_after, allocator, &program, &plan, &scopes, boundary, false, "    ", &.{});
    try std.testing.expectEqualStrings(
        wrapped_side_region ++
            "    if not __lifter_escape_3 then\n" ++
            "      __lifter_escape_2 = true\n" ++
            "      do\n" ++
            "        break\n" ++
            "      end\n" ++
            "    end\n",
        sets_after.items,
    );

    // A side escape that falls through to the holding region's end sets nothing after the region, whose wrapper keeps
    // its own declaration.
    var falls_through: std.ArrayList(u8) = .empty;
    defer falls_through.deinit(allocator);
    try emitLoopBoundaryArmImpl(&falls_through, allocator, &program, &plan, &scopes, boundary, true, "    ", &.{});
    try std.testing.expectEqualStrings("    local __lifter_escape_2 = false\n" ++ wrapped_side_region, falls_through.items);
}

test "a loop that owns its exit declares that exit's flag and counts it in the register budget" {
    const header = ir.BlockId.fromIndex(1);
    const inner_header = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    const inner_block = ir.BlockId.fromIndex(4);
    // An infinite loop whose body holds an inner loop that leaves through the outer loop's exit: the inner loop's exit
    // is an escape, carried by the flag of the exit the outer loop owns.
    var inner_nodes = [_]structure.Node{.{ .block = inner_block }};
    var inner_body = structure.Region{ .nodes = &inner_nodes, .stop = inner_header, .loop_exit = exit, .continue_target = inner_header };
    var body_nodes = [_]structure.Node{
        .{ .block = header },
        .{ .loop = .{
            .header = inner_header,
            .body_region = &inner_body,
            .body_edge = .{ .target = inner_block },
            .exit_edge = .{ .target = exit },
            .exit_is_escape = true,
            .continue_on_true = true,
        } },
    };
    var body = structure.Region{ .nodes = &body_nodes, .stop = header, .loop_exit = exit, .continue_target = header };
    var root_nodes = [_]structure.Node{
        .{ .infinite_loop = .{ .header = header, .body_region = &body, .exit = exit } },
        .{ .block = exit },
    };
    var root = structure.Region{ .nodes = &root_nodes, .stop = null, .loop_exit = null };
    try std.testing.expectEqual(@as(?ir.BlockId, exit), structured_escape.loopOwnedExitFlag(&root, root_nodes[0]));
    // The inner loop leaves through an escape, so it owns no exit.
    try std.testing.expectEqual(@as(?ir.BlockId, null), structured_escape.loopOwnedExitFlag(&body, body_nodes[1]));
    // The owned exit's flag lives through the outer loop's body: one flag in the register budget.
    try std.testing.expectEqual(@as(usize, 1), structured_escape.maxOwnedDepth(&root));
    // A holding region whose stop is the exit declares the flag before its wrapper, so the loop does not.
    root.stop = exit;
    try std.testing.expectEqual(@as(?ir.BlockId, null), structured_escape.loopOwnedExitFlag(&root, root_nodes[0]));
    root.stop = null;
    // A loop whose exit is itself an escape owns no exit.
    root_nodes[0].infinite_loop.exit_is_escape = true;
    try std.testing.expectEqual(@as(?ir.BlockId, null), structured_escape.loopOwnedExitFlag(&root, root_nodes[0]));
    root_nodes[0].infinite_loop.exit_is_escape = false;
    // With no escape to the exit in the body there is no flag to declare and none to count.
    body_nodes[1].loop.exit_is_escape = false;
    try std.testing.expectEqual(@as(?ir.BlockId, null), structured_escape.loopOwnedExitFlag(&root, root_nodes[0]));
    try std.testing.expectEqual(@as(usize, 0), structured_escape.maxOwnedDepth(&root));
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

test "unstructured semantic numeric transition emits its explicit dynamic sequence" {
    const proof = ir.EvidenceId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = ir.ValueId.fromIndex(0), .function = function_id, .name_hint = "control", .origin = .{ .parameter = 0 } },
        .{ .id = ir.ValueId.fromIndex(1), .function = function_id, .name_hint = "limit", .origin = .{ .parameter = 1 } },
        .{ .id = ir.ValueId.fromIndex(2), .function = function_id, .name_hint = "step", .origin = .{ .parameter = 2 } },
        .{ .id = ir.ValueId.fromIndex(3), .function = function_id, .type = .boolean, .name_hint = "initial", .origin = .{ .parameter = 3 } },
        .{ .id = ir.ValueId.fromIndex(4), .function = function_id, .type = .boolean, .name_hint = "has_value", .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } } },
        .{ .id = ir.ValueId.fromIndex(5), .function = function_id, .name_hint = "next_limit", .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 1 } } },
        .{ .id = ir.ValueId.fromIndex(6), .function = function_id, .name_hint = "next_step", .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 2 } } },
        .{ .id = ir.ValueId.fromIndex(7), .function = function_id, .name_hint = "next_control", .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 3 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = block_id,
        .operation = .{ .numeric_for_next = .{
            .control = ir.ValueId.fromIndex(0),
            .limit = ir.ValueId.fromIndex(1),
            .step = ir.ValueId.fromIndex(2),
            .initial = ir.ValueId.fromIndex(3),
            .mode = .semantic_normalized,
        } },
        .results = &.{ ir.ValueId.fromIndex(4), ir.ValueId.fromIndex(5), ir.ValueId.fromIndex(6), ir.ValueId.fromIndex(7) },
        .effects = .dynamic_call,
        .evidence = &.{proof},
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{instruction_id},
        .terminator = .{ .return_values = &.{ ir.ValueId.fromIndex(4), ir.ValueId.fromIndex(5), ir.ValueId.fromIndex(6), ir.ValueId.fromIndex(7) } },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ ir.ValueId.fromIndex(0), ir.ValueId.fromIndex(1), ir.ValueId.fromIndex(2), ir.ValueId.fromIndex(3) },
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:semantic-numeric-transition",
    }};
    const program: ir.Program = .{
        .program_id = "semantic-numeric-transition",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const source = try emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "next_control = control + next_step") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "if next_step <= 0 then") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "has_value = next_control >= next_limit") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "has_value = next_control <= next_limit") != null);
}

fn emitInstruction(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    instruction: ir.Instruction,
    indent: []const u8,
    declare_results: bool,
    declare_place: bool,
    place_aliases: []const PlaceAlias,
    composition: ?*const branch_expression.Composition,
) (EmitError || std.mem.Allocator.Error)!void {
    if (composition) |value| {
        if (value.instructionIsAbsorbed(instruction.id)) return;
    }
    if (emission_plan.dead.contains(instruction.id)) return;
    if (scopes.instructionIsMovedLiteralInitializer(instruction.id)) return;
    if (emission_plan.place_reads.contains(instruction.id)) return;
    if (emission_plan.fused_values.contains(instruction.id)) return;
    if (emission_plan.closure_stores.consumerForProducer(instruction.id) != null) return;
    if (emission_plan.place_writes.consumerForProducer(instruction.id) != null) return;
    const values = composedValuePlan(emission_plan, place_aliases, composition);
    if (emission_plan.closure_stores.producerForConsumer(instruction.id)) |producer_id| {
        return emitClosureStore(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            instruction,
            producer_id,
            indent,
            place_aliases,
            values,
        );
    }
    switch (emission_plan.packs.role(instruction.id)) {
        .ordinary => {},
        .fused_invocation_producer => return,
        .fused_return_producer => return,
        .fused_pack_values_producer => return,
        .materialized_pack_values_producer => return,
        .fused_pack_values_return_producer => return,
        .materialized_invocation_producer => |adjustment_id| {
            if (adjustment_id.index() >= program.instructions.len) return error.UnsupportedOperation;
            return call_emission.materializedAdjustment(
                output,
                allocator,
                program,
                emission_plan,
                program.instructions[adjustment_id.index()],
                instruction,
                indent,
                scopes.instructionDeclaresResults(adjustment_id),
                values,
            );
        },
        .materialized_adjustment => return,
        .materialized_adjustment_copy => |primary_id| {
            if (primary_id.index() >= program.instructions.len) return error.UnsupportedOperation;
            return call_emission.materializedAdjustmentCopy(
                output,
                allocator,
                emission_plan,
                instruction,
                program.instructions[primary_id.index()],
                indent,
                declare_results,
            );
        },
        .stored_invocation_producer => return call_emission.storedPack(
            output,
            allocator,
            program,
            emission_plan,
            instruction,
            indent,
            values,
        ),
        .stored_adjustment => |producer_id| {
            if (producer_id.index() >= program.instructions.len) return error.UnsupportedOperation;
            return call_emission.storedAdjustment(
                output,
                allocator,
                program,
                emission_plan,
                instruction,
                program.instructions[producer_id.index()],
                indent,
                declare_results,
                values,
            );
        },
        .fused_adjustment => |producer_id| return call_emission.fusedAdjustment(
            output,
            allocator,
            program,
            emission_plan,
            instruction,
            program.instructions[producer_id.index()],
            indent,
            declare_results,
            values,
        ),
        .direct_vararg_adjustment => return call_emission.directVarargAdjustment(
            output,
            allocator,
            program,
            emission_plan,
            instruction,
            indent,
            declare_results,
            values,
        ),
        .fused_pack_values_adjustment => |producer_id| return call_emission.packValuesAdjustment(
            output,
            allocator,
            program,
            emission_plan,
            instruction,
            program.instructions[producer_id.index()],
            indent,
            declare_results,
            values,
        ),
    }

    switch (instruction.operation) {
        .generic_for_next => |operation| return emitGenericForNextTransition(
            output,
            allocator,
            program,
            emission_plan,
            instruction,
            operation,
            indent,
            values,
        ),
        .numeric_for_next => |operation| switch (operation.mode) {
            .semantic_normalized => return emitSemanticNormalizedTransition(
                output,
                allocator,
                program,
                emission_plan,
                instruction,
                operation,
                indent,
                declare_results,
                values,
            ),
            .luau_numeric => return emitLuauNumericTransition(
                output,
                allocator,
                program,
                emission_plan,
                instruction,
                operation,
                indent,
                declare_results,
                values,
            ),
        },
        .call_repeated_table_get => |operation| return emitCallRepeatedTableGetInstruction(
            output,
            allocator,
            program,
            emission_plan,
            instruction,
            operation,
            indent,
            declare_results,
            place_aliases,
            values,
        ),
        .call,
        .namecall,
        .protected_call,
        .coroutine_create,
        .coroutine_resume,
        .coroutine_yield,
        => return call_emission.instruction(
            output,
            allocator,
            program,
            emission_plan,
            instruction,
            indent,
            declare_results,
            values,
        ),
        .make_closure => |closure| return emitClosureInstruction(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            instruction,
            closure,
            indent,
            declare_results,
            place_aliases,
            values,
        ),
        .place_read => |place_id| return lexical.emitRead(
            output,
            allocator,
            program,
            values,
            instruction,
            place_id,
            indent,
            declare_results,
            place_aliases,
        ),
        .place_write => |operation| return emitPlaceWriteInstruction(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            instruction,
            operation,
            indent,
            declare_place,
            place_aliases,
            values,
        ),
        .make_table_literal => |constructor| return emitTableConstructorInstruction(
            output,
            allocator,
            program,
            emission_plan,
            instruction,
            constructor,
            indent,
            declare_results,
            values,
        ),
        .table_set_pack => |operation| return emitTableSetPackInstruction(
            output,
            allocator,
            program,
            emission_plan,
            instruction,
            operation,
            indent,
            values,
        ),
        .table_set => if (compound_update.matchTable(program, &emission_plan.dead, &emission_plan.fused_values, instruction)) |update| {
            return emitCompoundMemoryUpdate(
                output,
                allocator,
                program,
                emission_plan,
                instruction,
                update,
                indent,
                values,
            );
        },
        .environment_set => if (compound_update.matchEnvironment(program, &emission_plan.dead, &emission_plan.fused_values, instruction)) |update| {
            return emitCompoundMemoryUpdate(
                output,
                allocator,
                program,
                emission_plan,
                instruction,
                update,
                indent,
                values,
            );
        },
        else => {},
    }

    if (instruction.results.len == 0 and render.statementNeedsSeparator(program, values, instruction.operation)) {
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "do\n");
        const statement_indent = try allocDeeperIndent(allocator, indent);
        defer allocator.free(statement_indent);
        try output.appendSlice(allocator, statement_indent);
        try render.statement(output, allocator, program, values, instruction.operation);
        try output.append(allocator, '\n');
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "end\n");
        return;
    }

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
        try render.expressionRoot(output, allocator, program, values, instruction.operation);
    } else try render.statement(output, allocator, program, values, instruction.operation);
    try output.append(allocator, '\n');
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
    try render.valueUseGroupedScalar(output, allocator, program, values, operation.control);
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

fn emitLuauNumericTransition(
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
    if (instruction.results.len != 4) return error.UnsupportedOperation;
    const has_value = instruction.results[0];
    const next_limit = instruction.results[1];
    const next_step = instruction.results[2];
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

    const guard_name = try emission_plan.names.internalNameAlloc(allocator, program, "__lifter_numeric_guard");
    defer allocator.free(guard_name);
    const arm_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(arm_indent);

    // The initial entry runs a one-shot native `for`, so the VM performs FORNPREP's coercion of the initial value,
    // the limit and the step, in that order and with its own error messages; `* 1` then takes the coerced numbers
    // and keeps -0, NaN and inf. A later entry advances by the coerced step. The test reads the step's sign without
    // advancing first.
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "if ");
    try render.valueUseScalar(output, allocator, program, values, operation.initial);
    try output.appendSlice(allocator, " then\n");
    try output.appendSlice(allocator, arm_indent);
    try output.appendSlice(allocator, "for ");
    try output.appendSlice(allocator, guard_name);
    try output.appendSlice(allocator, " = ");
    try render.valueUseScalar(output, allocator, program, values, operation.control);
    try output.appendSlice(allocator, ", ");
    try render.valueUseScalar(output, allocator, program, values, operation.limit);
    try output.appendSlice(allocator, ", ");
    try render.valueUseScalar(output, allocator, program, values, operation.step);
    try output.appendSlice(allocator, " do break end\n");
    try output.appendSlice(allocator, arm_indent);
    try render.valueName(output, allocator, &emission_plan.names, next_limit);
    try output.appendSlice(allocator, " = ");
    try render.valueUseGroupedScalar(output, allocator, program, values, operation.limit);
    try output.appendSlice(allocator, " * 1\n");
    try output.appendSlice(allocator, arm_indent);
    try render.valueName(output, allocator, &emission_plan.names, next_step);
    try output.appendSlice(allocator, " = ");
    try render.valueUseGroupedScalar(output, allocator, program, values, operation.step);
    try output.appendSlice(allocator, " * 1\n");
    try output.appendSlice(allocator, arm_indent);
    try render.valueName(output, allocator, &emission_plan.names, next_control);
    try output.appendSlice(allocator, " = ");
    try render.valueUseGroupedScalar(output, allocator, program, values, operation.control);
    try output.appendSlice(allocator, " * 1\n");
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "else\n");
    try output.appendSlice(allocator, arm_indent);
    try render.valueName(output, allocator, &emission_plan.names, next_limit);
    try output.appendSlice(allocator, " = ");
    try render.valueUseScalar(output, allocator, program, values, operation.limit);
    try output.append(allocator, '\n');
    try output.appendSlice(allocator, arm_indent);
    try render.valueName(output, allocator, &emission_plan.names, next_step);
    try output.appendSlice(allocator, " = ");
    try render.valueUseScalar(output, allocator, program, values, operation.step);
    try output.append(allocator, '\n');
    try output.appendSlice(allocator, arm_indent);
    try render.valueName(output, allocator, &emission_plan.names, next_control);
    try output.appendSlice(allocator, " = ");
    try render.valueUseGroupedScalar(output, allocator, program, values, operation.control);
    try output.appendSlice(allocator, " + ");
    try render.valueName(output, allocator, &emission_plan.names, next_step);
    try output.append(allocator, '\n');
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");

    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "if ");
    try render.valueName(output, allocator, &emission_plan.names, next_step);
    try output.appendSlice(allocator, " > 0 then\n");
    try output.appendSlice(allocator, arm_indent);
    try render.valueName(output, allocator, &emission_plan.names, has_value);
    try output.appendSlice(allocator, " = ");
    try render.valueName(output, allocator, &emission_plan.names, next_control);
    try output.appendSlice(allocator, " <= ");
    try render.valueName(output, allocator, &emission_plan.names, next_limit);
    try output.append(allocator, '\n');
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "else\n");
    try output.appendSlice(allocator, arm_indent);
    try render.valueName(output, allocator, &emission_plan.names, has_value);
    try output.appendSlice(allocator, " = ");
    try render.valueName(output, allocator, &emission_plan.names, next_limit);
    try output.appendSlice(allocator, " <= ");
    try render.valueName(output, allocator, &emission_plan.names, next_control);
    try output.append(allocator, '\n');
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "end\n");
}

fn emitGenericForNextTransition(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    instruction: ir.Instruction,
    operation: ir.GenericForNext,
    indent: []const u8,
    values: render.ValuePlan,
) !void {
    const variable_count = @as(usize, operation.variable_count);
    if (variable_count == 0 or instruction.results.len != variable_count + 3) return error.UnsupportedOperation;

    const iterator_name = try emission_plan.names.internalNameAlloc(allocator, program, "__lifter_generic_iterator");
    defer allocator.free(iterator_name);
    const state_name = try emission_plan.names.internalNameAlloc(allocator, program, "__lifter_generic_state");
    defer allocator.free(state_name);
    const control_name = try emission_plan.names.internalNameAlloc(allocator, program, "__lifter_generic_control");
    defer allocator.free(control_name);
    const metatable_name = try emission_plan.names.internalNameAlloc(allocator, program, "__lifter_generic_metatable");
    defer allocator.free(metatable_name);
    const iterator_method_name = try emission_plan.names.internalNameAlloc(allocator, program, "__lifter_generic_method");
    defer allocator.free(iterator_method_name);
    const inner_indent = try allocDeeperIndent(allocator, indent);
    defer allocator.free(inner_indent);

    // A generic-for transition is an SSA operation, so prepare private
    // temporaries instead of overwriting its iterator/state/control operands.
    try output.appendSlice(allocator, indent);
    try output.appendSlice(allocator, "do\n");
    try output.appendSlice(allocator, inner_indent);
    try output.appendSlice(allocator, "local ");
    try output.appendSlice(allocator, iterator_name);
    try output.appendSlice(allocator, " = ");
    try render.valueUseScalar(output, allocator, program, values, operation.iterator);
    try output.append(allocator, '\n');
    try output.appendSlice(allocator, inner_indent);
    try output.appendSlice(allocator, "local ");
    try output.appendSlice(allocator, state_name);
    try output.appendSlice(allocator, " = ");
    try render.valueUseScalar(output, allocator, program, values, operation.state);
    try output.append(allocator, '\n');
    try output.appendSlice(allocator, inner_indent);
    try output.appendSlice(allocator, "local ");
    try output.appendSlice(allocator, control_name);
    try output.appendSlice(allocator, " = ");
    try render.valueUseScalar(output, allocator, program, values, operation.control);
    try output.append(allocator, '\n');

    try output.appendSlice(allocator, inner_indent);
    try output.appendSlice(allocator, "if ");
    try render.valueUseScalar(output, allocator, program, values, operation.initial);
    try output.appendSlice(allocator, " then\n");
    const preparation_indent = try allocDeeperIndent(allocator, inner_indent);
    defer allocator.free(preparation_indent);

    try output.appendSlice(allocator, preparation_indent);
    try output.appendSlice(allocator, "local ");
    try output.appendSlice(allocator, metatable_name);
    try output.appendSlice(allocator, " = ");
    try render.runtimeCallStart(output, allocator, values, .getmetatable);
    try output.appendSlice(allocator, iterator_name);
    try output.appendSlice(allocator, ")\n");
    try output.appendSlice(allocator, preparation_indent);
    try output.appendSlice(allocator, "local ");
    try output.appendSlice(allocator, iterator_method_name);
    try output.appendSlice(allocator, " = ");
    try output.appendSlice(allocator, metatable_name);
    try output.appendSlice(allocator, " and ");
    try output.appendSlice(allocator, metatable_name);
    try output.appendSlice(allocator, ".__iter\n");

    try output.appendSlice(allocator, preparation_indent);
    try output.appendSlice(allocator, "if ");
    try output.appendSlice(allocator, iterator_method_name);
    try output.appendSlice(allocator, " ~= nil then\n");
    const method_indent = try allocDeeperIndent(allocator, preparation_indent);
    defer allocator.free(method_indent);
    try output.appendSlice(allocator, method_indent);
    try output.appendSlice(allocator, iterator_name);
    try output.appendSlice(allocator, ", ");
    try output.appendSlice(allocator, state_name);
    try output.appendSlice(allocator, ", ");
    try output.appendSlice(allocator, control_name);
    try output.appendSlice(allocator, " = ");
    try output.appendSlice(allocator, iterator_method_name);
    try output.append(allocator, '(');
    try output.appendSlice(allocator, iterator_name);
    try output.appendSlice(allocator, ")\n");
    try output.appendSlice(allocator, preparation_indent);
    try output.appendSlice(allocator, "elseif (");
    try output.appendSlice(allocator, metatable_name);
    try output.appendSlice(allocator, " == nil or ");
    try output.appendSlice(allocator, metatable_name);
    try output.appendSlice(allocator, ".__call == nil) and ");
    try render.runtimeCallStart(output, allocator, values, .type);
    try output.appendSlice(allocator, iterator_name);
    try output.appendSlice(allocator, ") == \"table\" then\n");
    try output.appendSlice(allocator, method_indent);
    try output.appendSlice(allocator, state_name);
    try output.appendSlice(allocator, " = ");
    try output.appendSlice(allocator, iterator_name);
    try output.append(allocator, '\n');
    try output.appendSlice(allocator, method_indent);
    try output.appendSlice(allocator, iterator_name);
    try output.appendSlice(allocator, " = ");
    const next_name = emission_plan.names.runtimeCapability(.next) orelse return error.UnsupportedOperation;
    try render.globalIdentifier(output, allocator, next_name);
    try output.append(allocator, '\n');
    try output.appendSlice(allocator, method_indent);
    try output.appendSlice(allocator, control_name);
    try output.appendSlice(allocator, " = nil\n");
    try output.appendSlice(allocator, preparation_indent);
    try output.appendSlice(allocator, "end\n");
    try output.appendSlice(allocator, inner_indent);
    try output.appendSlice(allocator, "end\n");

    const prepared_iterator = instruction.results[1];
    const prepared_state = instruction.results[2];
    try output.appendSlice(allocator, inner_indent);
    try render.valueName(output, allocator, &emission_plan.names, prepared_iterator);
    try output.appendSlice(allocator, " = ");
    try output.appendSlice(allocator, iterator_name);
    try output.append(allocator, '\n');
    try output.appendSlice(allocator, inner_indent);
    try render.valueName(output, allocator, &emission_plan.names, prepared_state);
    try output.appendSlice(allocator, " = ");
    try output.appendSlice(allocator, state_name);
    try output.append(allocator, '\n');

    try output.appendSlice(allocator, inner_indent);
    for (instruction.results[3..], 0..) |result, index| {
        if (index != 0) try output.appendSlice(allocator, ", ");
        try render.valueName(output, allocator, &emission_plan.names, result);
    }
    try output.appendSlice(allocator, " = ");
    try output.appendSlice(allocator, iterator_name);
    try output.append(allocator, '(');
    try output.appendSlice(allocator, state_name);
    try output.appendSlice(allocator, ", ");
    try output.appendSlice(allocator, control_name);
    try output.appendSlice(allocator, ")\n");
    try output.appendSlice(allocator, inner_indent);
    try render.valueName(output, allocator, &emission_plan.names, instruction.results[0]);
    try output.appendSlice(allocator, " = ");
    try render.valueName(output, allocator, &emission_plan.names, instruction.results[3]);
    try output.appendSlice(allocator, " ~= nil\n");
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

fn emitPlaceWriteInstruction(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    instruction: ir.Instruction,
    operation: ir.PlaceWrite,
    indent: []const u8,
    declare_place: bool,
    place_aliases: []const PlaceAlias,
    values: render.ValuePlan,
) !void {
    const producer_id = emission_plan.place_writes.producerForWrite(instruction.id) orelse {
        return lexical.emitWrite(
            output,
            allocator,
            program,
            values,
            instruction,
            operation,
            indent,
            declare_place,
            place_aliases,
        ) catch |err| {
            std.debug.print(
                "emit place_write={} stage=lexical_write place={} value={} declare={} aliases={} error={s}\n",
                .{ instruction.id.index(), operation.place.index(), operation.value.index(), declare_place, place_aliases.len, @errorName(err) },
            );
            return err;
        };
    };
    if (producer_id.index() >= program.instructions.len) {
        std.debug.print(
            "emit place_write={} stage=producer_index producer={} error=UnsupportedOperation\n",
            .{ instruction.id.index(), producer_id.index() },
        );
        return error.UnsupportedOperation;
    }
    const producer = program.instructions[producer_id.index()];
    if (producer.operation == .make_closure) {
        const role = emission_plan.packs.role(producer.id);
        if (role != .ordinary) {
            std.debug.print(
                "emit place_write={} stage=closure_role producer={} role={s} error=UnsupportedOperation\n",
                .{ instruction.id.index(), producer.id.index(), @tagName(role) },
            );
            return error.UnsupportedOperation;
        }
        return emitClosure(
            output,
            allocator,
            program,
            emission_plan,
            scopes,
            producer.operation.make_closure,
            .{ .place = .{ .id = operation.place, .declare = declare_place } },
            indent,
            place_aliases,
            values,
        ) catch |err| {
            std.debug.print(
                "emit place_write={} stage=closure_emit producer={} error={s}\n",
                .{ instruction.id.index(), producer.id.index(), @errorName(err) },
            );
            return err;
        };
    }

    const resolved_target = place_render.resolve(operation.place, place_aliases) orelse {
        std.debug.print(
            "emit place_write={} stage=destination_alias place={} aliases={} error=UnsupportedOperation\n",
            .{ instruction.id.index(), operation.place.index(), place_aliases.len },
        );
        return error.UnsupportedOperation;
    };

    if (!declare_place and (resolved_target == .place or resolved_target == .boxed_cell)) {
        if (compound_update.matchPlace(program, &emission_plan.dead, &emission_plan.place_writes, &emission_plan.place_reads, producer, instruction)) |update| {
            try output.appendSlice(allocator, indent);
            try lexical.emitPlaceName(output, allocator, &emission_plan.names, program, operation.place, place_aliases);
            try output.append(allocator, ' ');
            try output.appendSlice(allocator, render.compoundOperator(update.operator) orelse return error.UnsupportedOperation);
            try output.append(allocator, ' ');
            try render.valueUseScalar(output, allocator, program, values, update.right);
            try output.append(allocator, '\n');
            return;
        }
    }

    try output.appendSlice(allocator, indent);
    var box_close = false;
    const closes_external = switch (resolved_target) {
        .place => blk: {
            if (declare_place and !emission_plan.names.placeUsesStorage(resolved_target.place)) {
                try output.appendSlice(allocator, "local ");
            }
            try lexical.emitPlaceName(output, allocator, &emission_plan.names, program, operation.place, place_aliases);
            try output.appendSlice(allocator, " = ");
            break :blk false;
        },
        .external_binding => |binding_id| blk: {
            if (declare_place) return error.UnsupportedOperation;
            try render.runtimeCallStart(output, allocator, values, .rawset);
            try place_render.emitExternalBindingName(output, allocator, &emission_plan.names, binding_id);
            try output.appendSlice(allocator, ", 1, ");
            break :blk true;
        },
        .boxed_cell => blk: {
            // A boxed per-execution cell: the allocating origin write makes a fresh box
            // `<holder> = { value }`; any other write stores the produced value through `<holder>[1]`.
            if (declare_place) return error.UnsupportedOperation;
            if (lexical.placeWriteIsBoxAllocation(program, operation.place, instruction)) {
                try place_render.emitBoxHolderName(output, allocator, &emission_plan.names, program, operation.place, place_aliases);
                try output.appendSlice(allocator, " = { ");
                box_close = true;
            } else {
                try lexical.emitPlaceName(output, allocator, &emission_plan.names, program, operation.place, place_aliases);
                try output.appendSlice(allocator, " = ");
            }
            break :blk false;
        },
    };
    switch (emission_plan.packs.role(producer.id)) {
        .fused_adjustment => |invocation_id| {
            if (invocation_id.index() >= program.instructions.len) return error.UnsupportedOperation;
            try render.plannedInvocation(
                output,
                allocator,
                program,
                values,
                &emission_plan.packs,
                program.instructions[invocation_id.index()],
            );
        },
        .ordinary => switch (producer.operation) {
            .call,
            .namecall,
            .protected_call,
            .coroutine_create,
            .coroutine_resume,
            .coroutine_yield,
            => try render.plannedInvocation(output, allocator, program, values, &emission_plan.packs, producer),
            .make_table_literal => |constructor| try render.plannedTableConstructor(
                output,
                allocator,
                program,
                values,
                producer.id,
                constructor,
            ),
            else => try render.expressionRoot(output, allocator, program, values, producer.operation),
        },
        else => return error.UnsupportedOperation,
    }
    if (box_close) try output.appendSlice(allocator, " }");
    if (closes_external) try output.append(allocator, ')');
    try output.append(allocator, '\n');
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
        .place, .boxed_cell => {
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

fn emitClosureInstruction(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    instruction: ir.Instruction,
    closure: ir.Closure,
    indent: []const u8,
    declare_result: bool,
    parent_place_aliases: []const PlaceAlias,
    parent_values: render.ValuePlan,
) !void {
    if (instruction.results.len != 1) return error.UnsupportedOperation;
    return emitClosure(
        output,
        allocator,
        program,
        emission_plan,
        scopes,
        closure,
        .{ .value = .{ .id = instruction.results[0], .declare = declare_result } },
        indent,
        parent_place_aliases,
        parent_values,
    );
}

fn emitClosureStore(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    consumer: ir.Instruction,
    producer_id: ir.InstructionId,
    indent: []const u8,
    place_aliases: []const PlaceAlias,
    values: render.ValuePlan,
) !void {
    if (producer_id.index() >= program.instructions.len) return error.UnsupportedOperation;
    const producer = program.instructions[producer_id.index()];
    const closure = switch (producer.operation) {
        .make_closure => |value| value,
        else => return error.UnsupportedOperation,
    };
    const destination: ClosureDestination = switch (consumer.operation) {
        .table_set => |store| .{ .table = store },
        .environment_set => |store| .{ .environment = store },
        else => return error.UnsupportedOperation,
    };
    return emitClosure(output, allocator, program, emission_plan, scopes, closure, destination, indent, place_aliases, values);
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
            switch (resolved) {
                // A boxed closure-store destination writes `<holder>[1] = function…`; the box slot needs no
                // `local` and the holder is already declared in the root list.
                .boxed_cell => return,
                .external_binding => return error.UnsupportedOperation,
                .place => |direct| {
                    if (emission_plan.names.placeUsesStorage(direct)) return;
                    try output.appendSlice(allocator, indent);
                    try output.appendSlice(allocator, "local ");
                    try lexical.emitPlaceName(output, allocator, &emission_plan.names, program, place.id, parent_place_aliases);
                    try output.append(allocator, '\n');
                },
            }
        },
        .table, .environment => {},
    }
}

fn emitClosure(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission_plan: *const EmissionPlan,
    scopes: *const emission_scope.Plan,
    closure: ir.Closure,
    destination: ClosureDestination,
    indent: []const u8,
    parent_place_aliases: []const PlaceAlias,
    parent_values: render.ValuePlan,
) !void {
    const target = program.functions[closure.function.index()];
    var closure_plan = lexical.ClosurePlan.initWithStableValues(
        allocator,
        program,
        target,
        closure,
        parent_place_aliases,
        StableCaptureValues{ .scopes = scopes },
    ) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.InvalidClosureBinding => {
            std.debug.print(
                "emit closure={} target={} stage=closure_plan error=InvalidClosureBinding\n",
                .{ closure.function.index(), target.id.index() },
            );
            return error.UnsupportedOperation;
        },
    };
    defer closure_plan.deinit();

    const scopes_snapshots = closure_plan.value_bindings.len != 0 or closure_plan.snapshot_bindings.len != 0;
    var closure_indent = indent;
    var scoped_indent: ?[]u8 = null;
    defer if (scoped_indent) |value| allocator.free(value);
    if (scopes_snapshots) {
        emitScopedClosureDestinationDeclaration(
            output,
            allocator,
            program,
            emission_plan,
            destination,
            indent,
            parent_place_aliases,
        ) catch |err| {
            std.debug.print(
                "emit closure={} target={} stage=destination_declaration error={s}\n",
                .{ closure.function.index(), target.id.index(), @errorName(err) },
            );
            return err;
        };
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "do\n");
        scoped_indent = try allocDeeperIndent(allocator, indent);
        closure_indent = scoped_indent.?;
    }
    for (closure_plan.value_bindings) |binding| {
        try output.appendSlice(allocator, closure_indent);
        try output.appendSlice(allocator, "local ");
        try render.valueName(output, allocator, &emission_plan.names, binding.captured);
        try output.appendSlice(allocator, " = ");
        render.valueUseScalar(output, allocator, program, parent_values, binding.source) catch |err| {
            std.debug.print(
                "emit closure={} target={} stage=capture_value source={} captured={} error={s}\n",
                .{ closure.function.index(), target.id.index(), binding.source.index(), binding.captured.index(), @errorName(err) },
            );
            return err;
        };
        try output.append(allocator, '\n');
    }
    // Per-creation snapshot of each captured boxed per-execution cell: `local <cell> = <holder>` so the child
    // captures this execution's box reference, read through `<cell>[1]` in its body.
    for (closure_plan.snapshot_bindings) |snapshot| {
        try output.appendSlice(allocator, closure_indent);
        try output.appendSlice(allocator, "local ");
        try place_render.emitDirectName(output, allocator, &emission_plan.names, snapshot.captured);
        try output.appendSlice(allocator, " = ");
        place_render.emitBoxHolderName(output, allocator, &emission_plan.names, program, snapshot.source, parent_place_aliases) catch |err| {
            std.debug.print(
                "emit closure={} target={} stage=box_snapshot source={} captured={} error={s}\n",
                .{ closure.function.index(), target.id.index(), snapshot.source.index(), snapshot.captured.index(), @errorName(err) },
            );
            return err;
        };
        try output.append(allocator, '\n');
    }

    try output.appendSlice(allocator, closure_indent);
    var closes_external = false;
    switch (destination) {
        .value => |value| {
            if (value.declare and !scopes_snapshots and !emission_plan.names.valueUsesStorage(value.id)) try output.appendSlice(allocator, "local ");
            if (value.id.index() >= program.values.len) return error.UnsupportedOperation;
            try render.valueName(output, allocator, &emission_plan.names, value.id);
        },
        .place => |place| {
            const resolved = place_render.resolve(place.id, parent_place_aliases) orelse {
                std.debug.print(
                    "emit closure={} target={} stage=destination_alias place={} aliases={} error=UnsupportedOperation\n",
                    .{ closure.function.index(), target.id.index(), place.id.index(), parent_place_aliases.len },
                );
                return error.UnsupportedOperation;
            };
            switch (resolved) {
                .place => {
                    if (place.declare and !scopes_snapshots and !emission_plan.names.placeUsesStorage(resolved.place)) {
                        try output.appendSlice(allocator, "local ");
                    }
                    lexical.emitPlaceName(output, allocator, &emission_plan.names, program, place.id, parent_place_aliases) catch |err| {
                        std.debug.print(
                            "emit closure={} target={} stage=destination_name place={} resolved={} aliases={} error={s}\n",
                            .{ closure.function.index(), target.id.index(), place.id.index(), resolved.place.index(), parent_place_aliases.len, @errorName(err) },
                        );
                        return err;
                    };
                },
                .boxed_cell => {
                    // A closure stored into a boxed per-execution cell: `<holder>[1] = function…` (a box
                    // slot write). The holder is a declared root place, so the slot needs no `local`.
                    lexical.emitPlaceName(output, allocator, &emission_plan.names, program, place.id, parent_place_aliases) catch |err| {
                        std.debug.print(
                            "emit closure={} target={} stage=destination_name place={} aliases={} error={s}\n",
                            .{ closure.function.index(), target.id.index(), place.id.index(), parent_place_aliases.len, @errorName(err) },
                        );
                        return err;
                    };
                },
                .external_binding => |binding_id| {
                    if (place.declare) return error.UnsupportedOperation;
                    try render.runtimeCallStart(output, allocator, parent_values, .rawset);
                    try place_render.emitExternalBindingName(output, allocator, &emission_plan.names, binding_id);
                    try output.appendSlice(allocator, ", 1, ");
                    closes_external = true;
                },
            }
        },
        .table => |store| {
            if (store.mode != .semantic) return error.UnsupportedOperation;
            try render.valueUsePostfix(output, allocator, program, parent_values, store.table);
            try render.semanticValueIndexSuffix(output, allocator, program, parent_values, store.key);
        },
        .environment => |store| {
            if (store.mode != .semantic) return error.UnsupportedOperation;
            switch (store.target) {
                .ambient => try render.globalIdentifier(output, allocator, store.name),
                .value => |environment| {
                    try render.valueUsePostfix(output, allocator, program, parent_values, environment);
                    try render.semanticStringIndexSuffix(output, allocator, store.name);
                },
            }
        },
    }
    if (!closes_external) try output.appendSlice(allocator, " = ");
    try output.appendSlice(allocator, "function(");
    try emitFunctionParameters(output, allocator, emission_plan, target);
    try output.appendSlice(allocator, ")\n");

    const body_indent = try allocDeeperIndent(allocator, closure_indent);
    defer allocator.free(body_indent);
    emitFunctionBody(output, allocator, program, emission_plan, target, body_indent, closure_plan.place_aliases) catch |err| {
        std.debug.print(
            "emit closure={} target={} stage=function_body error={s}\n",
            .{ closure.function.index(), target.id.index(), @errorName(err) },
        );
        return err;
    };

    try output.appendSlice(allocator, closure_indent);
    try output.appendSlice(allocator, "end");
    if (closes_external) try output.append(allocator, ')');
    try output.append(allocator, '\n');
    if (scopes_snapshots) {
        try output.appendSlice(allocator, indent);
        try output.appendSlice(allocator, "end\n");
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
