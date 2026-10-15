const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const dead_code = @import("dead_code.zig");
const diagnostics = @import("diagnostics.zig");
const branch_expression = @import("emit_luau_branch_expr.zig");
const emit_luau = @import("emit_luau.zig");
const emission_planning = @import("emit_luau_plan.zig");
const emission_scope = @import("emit_luau_scope.zig");
const lexical = @import("emit_luau_lexical.zig");
const lexical_transfer = @import("lexical_transfer.zig");
const luau_runtime = @import("luau_runtime.zig");
const readable_scope = @import("readable_scope.zig");
const structure = @import("structure.zig");
const structured_escape = @import("structured_escape.zig");
const prototype_validation = @import("validate_luau_prototypes.zig");
const syntax_depth_validation = @import("validate_luau_syntax_depth.zig");
const upvalue_validation = @import("validate_luau_upvalues.zig");
const jump_budget_validation = @import("validate_luau_jump_budget.zig");
const stage_trace = @import("stage_trace.zig");

const StableCaptureValues = struct {
    scopes: *const emission_scope.Plan,

    pub fn contains(self: StableCaptureValues, value_id: ir.ValueId) bool {
        return self.scopes.valueHasStableLexicalBinding(value_id);
    }
};

const Pressure = struct {
    locals: usize,
    total: usize,
};

/// Which emission layout the register budget must model. `automatic` lets the
/// structured plan fall back to the arbitrary CFG only when the shape demands
/// it; `dispatcher` mirrors the emitter's forced-dispatcher layout.
pub const EmissionStrategy = enum { automatic, dispatcher };

pub fn validate(
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    target: luau_runtime.Target,
) !void {
    return validateWithStrategy(allocator, report, program, scope, target, .automatic);
}

pub fn validateWithStrategy(
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    _: *const readable_scope.Scope,
    target: luau_runtime.Target,
    strategy: EmissionStrategy,
) !void {
    if (stage_trace.enabled) std.debug.print("register_validation stage=begin\n", .{});
    var transfer_arena = std.heap.ArenaAllocator.init(allocator);
    defer transfer_arena.deinit();
    const prepared = lexical_transfer.prepareInArena(transfer_arena.allocator(), program) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.UnsupportedControlFlow, error.UnsupportedTransfer => unreachable,
    };
    if (stage_trace.enabled) std.debug.print("register_validation stage=prepared functions={} blocks={} instructions={}\n", .{ prepared.functions.len, prepared.blocks.len, prepared.instructions.len });
    var readable = try readable_scope.Scope.init(allocator, &prepared);
    defer readable.deinit();
    if (stage_trace.enabled) std.debug.print("register_validation stage=scope\n", .{});
    try validatePrepared(allocator, report, &prepared, &readable, target, strategy);
    if (stage_trace.enabled) std.debug.print("register_validation stage=done\n", .{});
}

fn validatePrepared(
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    target: luau_runtime.Target,
    strategy: EmissionStrategy,
) !void {
    if (stage_trace.enabled) std.debug.print("register_validation stage=emission_plan_begin\n", .{});
    var emission = try emission_planning.Plan.init(allocator, program, target);
    defer emission.deinit();
    if (stage_trace.enabled) std.debug.print("register_validation stage=emission_plan_done\n", .{});

    const emitted_functions = try findEmittedFunctions(allocator, program, readable, &emission);
    defer allocator.free(emitted_functions);
    const stable_values = try allocator.alloc(bool, program.values.len);
    defer allocator.free(stable_values);
    @memset(stable_values, false);
    var syntax_depths = try syntax_depth_validation.Plan.init(allocator, program, readable, &emission);
    defer syntax_depths.deinit();
    if (stage_trace.enabled) std.debug.print("register_validation stage=syntax_plan_done\n", .{});

    var entry_bindings = lexical.EntryPlan.init(allocator, program) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.InvalidEntryBinding => unreachable,
    };
    defer entry_bindings.deinit();
    const entry_base = saturatingAdd(
        saturatingAdd(runtimeCaptureCount(emission.runtime), topLevelFunctionCount(program)),
        saturatingAdd(
            saturatingAdd(program.external_bindings.len, program.functions[program.entry_function.index()].parameters.len),
            entry_bindings.value_bindings.len,
        ),
    );

    for (program.functions) |function| {
        if (!emitted_functions[function.id.index()]) continue;
        if (stage_trace.enabled) std.debug.print("register_validation function={} stage=begin\n", .{function.id.index()});
        var analysis = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.InvalidCfg => unreachable,
        };
        defer analysis.deinit();
        const direct_spine_depth = try syntax_depth_validation.maxDirectSpineDepth(allocator, program, &analysis);
        if (direct_spine_depth >= luau_runtime.max_emitted_syntax_nesting) {
            if (direct_spine_depth > luau_runtime.max_emitted_syntax_nesting and
                !hasDiagnosticForFunction(report, .unsupported_readable_syntax_depth, function.id.index()))
            {
                try report.add(.unsupported_readable_syntax_depth, function.id.index());
            }
            syntax_depths.recordDirectSpineFunction(function, direct_spine_depth);
            continue;
        }
        var structured = (if (strategy == .dispatcher)
            structure.Plan.initArbitrary(allocator, &analysis)
        else
            structure.Plan.initWithArbitraryFallback(allocator, &analysis)) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.UnsupportedShape => unreachable,
        };
        defer structured.deinit();
        var scopes = try emission_scope.Plan.init(
            allocator,
            program,
            function,
            &analysis,
            &structured,
            &emission.packs,
            &emission.dead,
            &emission.place_writes,
            &emission.place_reads,
            &emission.fused_values,
            &emission.closure_stores,
        );
        defer scopes.deinit();
        if (!structured.root.arbitrary_cfg) {
            branch_expression.markDeclarations(program, &emission, &scopes, structured.root, true);
        }
        try syntax_depths.recordFunction(function, &structured, &scopes);
        try jump_budget_validation.validate(report, program, readable, &emission, function, &structured);
        for (program.values) |value| {
            if (value.function == function.id and scopes.valueHasStableLexicalBinding(value.id)) {
                stable_values[value.id.index()] = true;
            }
        }

        const function_base = if (function.id == program.entry_function) entry_base else function.parameters.len;
        const storage_locals = saturatingAdd(
            @intFromBool(emission.names.functionUsesStorage(function)),
            @intFromBool(emission.names.functionUsesValueStorage(program, function)),
        );
        const base = try functionRegisterBase(allocator, function_base, storage_locals, structured.root);
        const pressure = try maximumPressure(allocator, program, readable, &emission, &scopes, function, base);
        // The dispatcher (arbitrary-CFG) layout declares a flat set of locals at
        // the function root that `maximumPressure` undercounts: it scores only
        // materialized (scoped) bindings and omits both the never-materialized
        // declarations and the `__lifter_pc` slot. Budget the emitter's own
        // declaration count plus the pc slot so a forced or natural dispatcher
        // layout past the compiler's limit is refused at admission.
        var effective_locals = pressure.locals;
        var effective_total = pressure.total;
        if (structured.root.arbitrary_cfg) {
            const flat_locals = saturatingAdd(
                saturatingAdd(function_base, storage_locals),
                saturatingAdd(emit_luau.arbitraryDeclarationCount(program, &emission, function), 1),
            );
            effective_locals = @max(effective_locals, flat_locals);
            effective_total = @max(effective_total, saturatingAdd(flat_locals, pressure.total -| pressure.locals));
            // A `luau_numeric` transition renders a one-shot native `for` as its coercion guard. The guard's loop
            // variable is one more local and is FORNPREP's index register, so the limit, step and index frame of 3
            // includes that local rather than adding to it.
            const holds_luau_numeric = holds: for (function.blocks) |block_id| {
                if (block_id.index() >= program.blocks.len) continue;
                for (program.blocks[block_id.index()].instructions) |instruction_id| {
                    if (instruction_id.index() >= program.instructions.len or emission.dead.contains(instruction_id)) continue;
                    switch (program.instructions[instruction_id.index()].operation) {
                        .numeric_for_next => |operation| if (operation.mode == .luau_numeric) break :holds true,
                        else => {},
                    }
                }
            } else false;
            if (holds_luau_numeric) {
                effective_locals = @max(effective_locals, saturatingAdd(flat_locals, 1));
                effective_total = @max(effective_total, saturatingAdd(flat_locals, 3));
            }
        }
        if (stage_trace.enabled) std.debug.print("register_pressure function={} base={} locals={} total={} scopes={}\n", .{
            function.id.index(),
            base,
            effective_locals,
            effective_total,
            scopes.pressureSlotCount(),
        });
        if (effective_locals > luau_runtime.max_local_registers) {
            try report.add(.unsupported_readable_register_pressure, function.id.index());
        } else if (effective_total > luau_runtime.max_registers) {
            try report.add(.unsupported_readable_temporary_register_pressure, function.id.index());
        }
        if (stage_trace.enabled) std.debug.print("register_validation function={} stage=done\n", .{function.id.index()});
    }

    try syntax_depths.addDiagnostics(report, emitted_functions);
    try validateFixedReturnCounts(report, program, readable, &emission, emitted_functions);
    try prototype_validation.validate(report, program, readable, &emission, emitted_functions);
    try upvalue_validation.validate(allocator, report, program, readable, &emission, stable_values);
}

/// The function-scope registers a certified layout holds before any scoped
/// binding: the parameters (the entry chunk's bindings for the entry
/// function), the owned-escape depth, the storage tables and, on a structured
/// root, the escape flags `emitFunctionBody` declares at function scope: one
/// per root free target and one per loop-boundary exit target not among them.
fn functionRegisterBase(
    allocator: std.mem.Allocator,
    function_base: usize,
    storage_locals: usize,
    root: *const structure.Region,
) std.mem.Allocator.Error!usize {
    const base = saturatingAdd(
        saturatingAdd(function_base, structured_escape.maxOwnedDepth(root)),
        storage_locals,
    );
    if (root.arbitrary_cfg) return base;
    const root_escape_targets = try structured_escape.regionFreeTargetsAlloc(allocator, root);
    defer allocator.free(root_escape_targets);
    const loop_boundary_exit_targets = try structured_escape.loopBoundaryExitTargetsAlloc(allocator, root);
    defer allocator.free(loop_boundary_exit_targets);
    var escape_flags = root_escape_targets.len;
    for (loop_boundary_exit_targets) |target| {
        for (root_escape_targets) |declared| {
            if (declared == target) break;
        } else escape_flags += 1;
    }
    return saturatingAdd(base, escape_flags);
}

fn hasDiagnosticForFunction(
    report: *const diagnostics.Report,
    code: diagnostics.Code,
    function_index: usize,
) bool {
    for (report.diagnostics.items) |diagnostic| {
        if (diagnostic.code == code and diagnostic.entity_index != null and
            diagnostic.entity_index.? == function_index) return true;
    }
    return false;
}

fn validateFixedReturnCounts(
    report: *diagnostics.Report,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
    emitted_functions: []const bool,
) std.mem.Allocator.Error!void {
    for (program.functions) |function| {
        if (function.id.index() >= emitted_functions.len or !emitted_functions[function.id.index()]) continue;
        for (function.blocks) |block_id| {
            if (block_id.index() >= program.blocks.len or !readable.block(block_id)) continue;
            const count = fixedReturnValueCount(program, emission, program.blocks[block_id.index()]) orelse continue;
            if (count > luau_runtime.max_fixed_return_values) {
                try report.add(.unsupported_readable_return_count, block_id.index());
            }
        }
    }
}

fn fixedReturnValueCount(
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    block: ir.Block,
) ?usize {
    return switch (emission.packs.terminatorRole(block.id)) {
        .ordinary => switch (block.terminator) {
            .return_values => |values| values.len,
            else => null,
        },
        .fused_invocation_return => null,
        .stored_pack_return => null,
        .fused_pack_values_return => |producer_id| blk: {
            if (producer_id.index() >= program.instructions.len) break :blk null;
            const packed_count = switch (program.instructions[producer_id.index()].operation) {
                .pack_values => |values| values.len,
                else => break :blk null,
            };
            const prefix_count = switch (block.terminator) {
                .return_pack => 0,
                .return_expanded => |expanded| expanded.values.len,
                else => break :blk null,
            };
            break :blk saturatingAdd(prefix_count, packed_count);
        },
    };
}

fn findEmittedFunctions(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
) ![]bool {
    const emitted = try allocator.alloc(bool, program.functions.len);
    @memset(emitted, false);
    for (program.functions) |function| {
        if (function.id == program.entry_function or function.lexical_parent == null) emitted[function.id.index()] = true;
    }

    var changed = true;
    while (changed) {
        changed = false;
        for (program.instructions) |instruction| {
            if (!readable.instruction(instruction.id) or emission.dead.contains(instruction.id)) continue;
            const target = switch (instruction.operation) {
                .make_closure => |closure| closure.function,
                else => continue,
            };
            if (instruction.block.index() >= program.blocks.len or target.index() >= emitted.len) continue;
            const owner = program.blocks[instruction.block.index()].function;
            if (owner.index() >= emitted.len or !emitted[owner.index()] or emitted[target.index()]) continue;
            emitted[target.index()] = true;
            changed = true;
        }
    }
    return emitted;
}

fn maximumPressure(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    function: ir.Function,
    base: usize,
) std.mem.Allocator.Error!Pressure {
    const locals = try allocator.alloc(usize, scopes.pressureSlotCount());
    defer allocator.free(locals);
    @memset(locals, 0);
    const value_locals = try allocator.alloc(usize, scopes.pressureSlotCount());
    defer allocator.free(value_locals);
    @memset(value_locals, 0);
    const pack_locals = try allocator.alloc(usize, scopes.pressureSlotCount());
    defer allocator.free(pack_locals);
    @memset(pack_locals, 0);
    const place_locals = try allocator.alloc(usize, scopes.pressureSlotCount());
    defer allocator.free(place_locals);
    @memset(place_locals, 0);
    const branch_locals = try allocator.alloc(usize, scopes.pressureSlotCount());
    defer allocator.free(branch_locals);
    @memset(branch_locals, 0);
    const closure_locals = try allocator.alloc(usize, scopes.pressureSlotCount());
    defer allocator.free(closure_locals);
    @memset(closure_locals, 0);
    const temporaries = try allocator.alloc(usize, scopes.pressureSlotCount());
    defer allocator.free(temporaries);
    @memset(temporaries, 0);

    for (program.values) |value| {
        if (value.function != function.id) continue;
        if (emission.names.valueUsesStorage(value.id)) continue;
        if (scopes.valueScope(value.id)) |scope| {
            addAtScope(locals, scopes, scope, 1);
            addAtScope(value_locals, scopes, scope, 1);
        }
    }
    for (program.value_packs) |pack| {
        if (pack.function != function.id) continue;
        if (scopes.packScope(pack.id)) |scope| {
            addAtScope(locals, scopes, scope, 1);
            addAtScope(pack_locals, scopes, scope, 1);
        }
    }
    for (function.local_places) |place_id| {
        if (emission.names.placeUsesStorage(place_id)) continue;
        if (scopes.placeScope(place_id)) |scope| {
            addAtScope(locals, scopes, scope, 1);
            addAtScope(place_locals, scopes, scope, 1);
        }
    }
    for (function.blocks) |block_id| {
        if (!readable.block(block_id) or block_id.index() >= program.blocks.len) continue;
        const block = program.blocks[block_id.index()];
        if (emission.discardedBranchConditionNeedsLocal(program, block)) {
            if (scopes.blockScope(block_id)) |scope| {
                addAtScope(locals, scopes, scope, 1);
                addAtScope(branch_locals, scopes, scope, 1);
            }
        }
        if (returnTemporaryFrameSize(program, emission, scopes, block)) |frame_size| {
            if (scopes.blockScope(block_id)) |scope| addTemporaryAtScope(temporaries, scopes, scope, frame_size);
        }
        addTerminatorEdgeFrames(program, emission, scopes, block, temporaries);
        for (block.instructions) |instruction_id| {
            if (!readable.instruction(instruction_id) or instruction_id.index() >= program.instructions.len) continue;
            if (emission.dead.contains(instruction_id) and !emission.dead.isInlined(instruction_id)) continue;
            const instruction = program.instructions[instruction_id.index()];
            if (emittedOperationTemporaryFrameSize(program, emission, scopes, instruction)) |frame_size| {
                if (scopes.renderedPressureScope(instruction.id)) |scope| {
                    addTemporaryAtScope(temporaries, scopes, scope, frame_size);
                }
            }
            const closure = switch (instruction.operation) {
                .make_closure => |value| value,
                else => continue,
            };
            if (closure.function.index() >= program.functions.len) continue;
            var closure_plan = lexical.ClosurePlan.initWithStableValues(
                allocator,
                program,
                program.functions[closure.function.index()],
                closure,
                &.{},
                StableCaptureValues{ .scopes = scopes },
            ) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.InvalidClosureBinding => unreachable,
            };
            defer closure_plan.deinit();
            const rendered_scope = closureRenderedScope(emission, scopes, instruction.id) orelse continue;
            if (scopes.physicalHost(rendered_scope)) |host| {
                if (host < closure_locals.len) closure_locals[host] = @max(closure_locals[host], closure_plan.value_bindings.len);
            }
        }
    }

    var maximum_locals = base;
    var maximum_total = base;
    var peak_host: emission_scope.ScopeId = emission_scope.invalid_scope;
    var peak_values: usize = 0;
    var peak_packs: usize = 0;
    var peak_places: usize = 0;
    var peak_branches: usize = 0;
    var peak_closures: usize = 0;
    var peak_temporaries: usize = 0;
    for (0..scopes.pressureSlotCount()) |index| {
        const host: emission_scope.ScopeId = @intCast(index);
        if (scopes.physicalHost(host) != host) continue;
        var local_total = base;
        var value_total: usize = 0;
        var pack_total: usize = 0;
        var place_total: usize = 0;
        var branch_total: usize = 0;
        var current: ?emission_scope.ScopeId = host;
        while (current) |physical| {
            local_total = saturatingAdd(local_total, locals[physical]);
            value_total = saturatingAdd(value_total, value_locals[physical]);
            pack_total = saturatingAdd(pack_total, pack_locals[physical]);
            place_total = saturatingAdd(place_total, place_locals[physical]);
            branch_total = saturatingAdd(branch_total, branch_locals[physical]);
            current = scopes.parentPhysicalHost(physical);
        }
        const local_peak = saturatingAdd(local_total, closure_locals[host]);
        if (local_peak > maximum_locals) {
            maximum_locals = local_peak;
            peak_host = host;
            peak_values = value_total;
            peak_packs = pack_total;
            peak_places = place_total;
            peak_branches = branch_total;
            peak_closures = closure_locals[host];
            peak_temporaries = temporaries[host];
        }
        maximum_total = @max(maximum_total, saturatingAdd(local_total, @max(closure_locals[host], temporaries[host])));
    }
    if (maximum_locals > luau_runtime.max_local_registers or maximum_total > luau_runtime.max_registers) {
        if (stage_trace.enabled) std.debug.print("register_pressure_detail function={} host={} base={} values={} packs={} places={} branches={} closures={} temporaries={} locals={} total={}\n", .{
            function.id.index(),
            peak_host,
            base,
            peak_values,
            peak_packs,
            peak_places,
            peak_branches,
            peak_closures,
            peak_temporaries,
            maximum_locals,
            maximum_total,
        });
    }
    return .{ .locals = maximum_locals, .total = maximum_total };
}

fn closureRenderedScope(
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    producer: ir.InstructionId,
) ?emission_scope.ScopeId {
    if (emission.closure_stores.consumerForProducer(producer)) |consumer| return scopes.instructionScope(consumer);
    if (emission.place_writes.consumerForProducer(producer)) |consumer| return scopes.instructionScope(consumer);
    return scopes.instructionScope(producer);
}

fn addAtScope(locals: []usize, scopes: *const emission_scope.Plan, scope: emission_scope.ScopeId, count: usize) void {
    const host = scopes.physicalHost(scope) orelse return;
    if (host >= locals.len) return;
    locals[host] = saturatingAdd(locals[host], count);
}

fn addTemporaryAtScope(temporaries: []usize, scopes: *const emission_scope.Plan, scope: emission_scope.ScopeId, count: usize) void {
    const host = scopes.physicalHost(scope) orelse return;
    if (host >= temporaries.len) return;
    temporaries[host] = @max(temporaries[host], count);
}

pub fn operationTemporaryFrameSize(operation: ir.Operation) ?usize {
    return switch (operation) {
        .call => |call| 1 + call.arguments.len + @intFromBool(call.argument_pack != null),
        .namecall => |call| 2 + call.arguments.len + @intFromBool(call.argument_pack != null),
        .protected_call => |call| 2 + @as(usize, @intFromBool(call.error_handler != null)) + call.arguments.len + @intFromBool(call.argument_pack != null),
        .coroutine_create => 2,
        .coroutine_resume => |call| 2 + call.arguments.len + @intFromBool(call.argument_pack != null),
        .coroutine_yield => |call| 1 + call.arguments.len + @intFromBool(call.argument_pack != null),
        .call_repeated_table_get => |call| 6 + call.prefix_arguments.len,
        .make_table_literal => |constructor| 1 + constructor.fields.len + @intFromBool(constructor.tail_pack != null),
        .table_set_pack => 4,
        .string_interpolate => |interpolation| 2 + interpolation.values.len,
        else => null,
    };
}

fn emittedOperationTemporaryFrameSize(
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    instruction: ir.Instruction,
) ?usize {
    switch (emission.packs.role(instruction.id)) {
        .stored_invocation_producer => {
            const invocation = operationTemporaryFrameSize(instruction.operation) orelse return null;
            return saturatingAdd(invocation, 1);
        },
        .stored_adjustment => return 3,
        else => {},
    }
    const raw = switch (instruction.operation) {
        .make_table_literal => |constructor| registerAtomicTableConstructorFrame(
            program,
            emission,
            scopes,
            constructor,
        ) orelse operationTemporaryFrameSize(instruction.operation).?,
        else => operationTemporaryFrameSize(instruction.operation) orelse return null,
    };
    const pack_id = switch (instruction.operation) {
        .call => |call| call.argument_pack,
        .namecall => |call| call.argument_pack,
        .protected_call => |call| call.argument_pack,
        .coroutine_resume => |call| call.argument_pack,
        .coroutine_yield => |call| call.argument_pack,
        .make_table_literal => |constructor| constructor.tail_pack,
        .table_set_pack => |operation| operation.pack,
        else => null,
    } orelse return raw;
    const width = emittedPackWidth(program, emission, instruction.id, pack_id);
    return raw - 1 + width;
}

fn registerAtomicTableConstructorFrame(
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    constructor: ir.TableConstructor,
) ?usize {
    if (constructor.tail_pack != null) return null;
    var list_count: usize = 0;
    var has_keyed = false;
    for (constructor.fields) |field| switch (field) {
        .list => |value| {
            if (!emittedScalarIsRegisterAtomic(program, emission, scopes, value)) return null;
            list_count = saturatingAdd(list_count, 1);
        },
        .keyed => |keyed| {
            if (!emittedScalarIsRegisterAtomic(program, emission, scopes, keyed.key) or
                !emittedScalarIsRegisterAtomic(program, emission, scopes, keyed.value)) return null;
            has_keyed = true;
        },
    };
    const keyed_frame: usize = if (has_keyed) 2 else 0;
    return saturatingAdd(1, @max(list_count, keyed_frame));
}

fn emittedScalarIsRegisterAtomic(
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    value_id: ir.ValueId,
) bool {
    const resolved = emission.dead.resolveValue(value_id);
    if (resolved.index() >= program.values.len) return false;
    if (scopes.valueHasStableLexicalBinding(resolved)) return true;
    const origin = switch (program.values[resolved.index()].origin) {
        .instruction_result => |origin| origin,
        else => return false,
    };
    if (origin.index != 0 or origin.instruction.index() >= program.instructions.len or
        (!emission.dead.isInlined(origin.instruction) and !emission.fused_values.contains(origin.instruction))) return false;
    return switch (program.instructions[origin.instruction.index()].operation) {
        .constant, .function_ref => true,
        else => false,
    };
}

fn emittedPackWidth(
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    consumer: ir.InstructionId,
    pack_id: ir.ValuePackId,
) usize {
    if (pack_id.index() >= program.value_packs.len) return 1;
    return switch (program.value_packs[pack_id.index()].origin) {
        .varargs => 1,
        .instruction_result => |producer_id| blk: {
            if (producer_id.index() >= program.instructions.len) break :blk 1;
            if (emission.packs.storedPackServesInstruction(producer_id, consumer)) break :blk 6;
            if (!emission.packs.packValuesServesInstruction(producer_id, consumer)) break :blk 1;
            break :blk switch (program.instructions[producer_id.index()].operation) {
                .pack_values => |items| items.len,
                else => 1,
            };
        },
    };
}

fn returnTemporaryFrameSize(
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    block: ir.Block,
) ?usize {
    return switch (block.terminator) {
        .return_values => |values| if (emission.packs.terminatorRole(block.id) == .ordinary)
            (if (valuesAreContiguousLexicalRun(program, scopes, values)) 0 else values.len)
        else
            null,
        .return_expanded => |expanded| switch (emission.packs.terminatorRole(block.id)) {
            .stored_pack_return => saturatingAdd(expanded.values.len, 6),
            .fused_pack_values_return => |producer_id| if (producer_id.index() < program.instructions.len)
                switch (program.instructions[producer_id.index()].operation) {
                    .pack_values => |items| expanded.values.len + items.len,
                    else => null,
                }
            else
                null,
            else => expanded.values.len + 1,
        },
        .return_pack => switch (emission.packs.terminatorRole(block.id)) {
            .stored_pack_return => 6,
            .fused_pack_values_return => |producer_id| if (producer_id.index() < program.instructions.len)
                switch (program.instructions[producer_id.index()].operation) {
                    .pack_values => |items| if (valuesAreContiguousLexicalRun(program, scopes, items)) 0 else items.len,
                    else => null,
                }
            else
                null,
            else => null,
        },
        else => null,
    };
}

fn addTerminatorEdgeFrames(
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    block: ir.Block,
    temporaries: []usize,
) void {
    switch (block.terminator) {
        .jump => |edge| addEdgeTemporaryFrame(program, emission, scopes, block.id, edge, temporaries),
        .branch => |branch| {
            addEdgeTemporaryFrame(program, emission, scopes, block.id, branch.then_edge, temporaries);
            addEdgeTemporaryFrame(program, emission, scopes, block.id, branch.else_edge, temporaries);
        },
        else => {},
    }
}

fn addEdgeTemporaryFrame(
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    source: ir.BlockId,
    edge: ir.Edge,
    temporaries: []usize,
) void {
    if (edge.target.index() >= program.blocks.len or scopes.nativeIterationConsumesParameters(edge.target)) return;
    const frame_size = edgeAssignmentCycleCount(program, emission, edge);
    if (frame_size == 0) return;
    if (scopes.blockScope(source)) |scope| addTemporaryAtScope(temporaries, scopes, scope, frame_size);
    if (scopes.blockScope(edge.target)) |scope| addTemporaryAtScope(temporaries, scopes, scope, frame_size);
}

pub fn edgeAssignmentCycleCount(program: *const ir.Program, emission: *const emission_planning.Plan, edge: ir.Edge) usize {
    if (edge.target.index() >= program.blocks.len) return 0;
    const parameters = program.blocks[edge.target.index()].parameters;
    if (parameters.len != edge.arguments.len) return 0;
    var cycles: usize = 0;
    for (parameters, 0..) |parameter, start| {
        if (emission.dead.isValueAlias(parameter)) continue;
        var current = start;
        var minimum = start;
        var length: usize = 0;
        var remaining = parameters.len + 1;
        while (remaining != 0) : (remaining -= 1) {
            const source = emission.dead.resolveValue(edge.arguments[current]);
            const next = resolvedParameterPosition(parameters, &emission.dead, source) orelse break;
            length += 1;
            minimum = @min(minimum, next);
            if (next == start) {
                if (length > 1 and minimum == start) cycles = saturatingAdd(cycles, 1);
                break;
            }
            current = next;
        }
    }
    return cycles;
}

fn resolvedParameterPosition(parameters: []const ir.ValueId, dead: *const dead_code.Plan, source: ir.ValueId) ?usize {
    for (parameters, 0..) |parameter, index| {
        if (!dead.isValueAlias(parameter) and dead.resolveValue(parameter) == source) return index;
    }
    return null;
}

fn valuesAreContiguousLexicalRun(program: *const ir.Program, scopes: *const emission_scope.Plan, values: []const ir.ValueId) bool {
    if (values.len == 0) return true;
    const first_id = values[0];
    if (first_id.index() >= program.values.len or !scopes.valueHasStableLexicalBinding(first_id)) return false;
    const first = program.values[first_id.index()];
    return switch (first.origin) {
        .parameter => |first_index| blk: {
            for (values[1..], 1..) |value_id, offset| {
                if (value_id.index() >= program.values.len) break :blk false;
                const value = program.values[value_id.index()];
                if (value.function != first.function or value.origin != .parameter or
                    value.origin.parameter != first_index + @as(u32, @intCast(offset))) break :blk false;
            }
            break :blk true;
        },
        .block_parameter => |first_origin| blk: {
            for (values[1..], 1..) |value_id, offset| {
                if (value_id.index() >= program.values.len or !scopes.valueHasStableLexicalBinding(value_id)) break :blk false;
                const value = program.values[value_id.index()];
                if (value.function != first.function or value.origin != .block_parameter or
                    value.origin.block_parameter.block != first_origin.block or
                    value.origin.block_parameter.index != first_origin.index + @as(u32, @intCast(offset)) or
                    value_id.index() != first_id.index() + offset) break :blk false;
            }
            break :blk true;
        },
        .instruction_result => |first_origin| blk: {
            for (values[1..], 1..) |value_id, offset| {
                if (value_id.index() >= program.values.len or !scopes.valueHasStableLexicalBinding(value_id)) break :blk false;
                const value = program.values[value_id.index()];
                if (value.function != first.function or value.origin != .instruction_result or
                    value.origin.instruction_result.instruction != first_origin.instruction or
                    value.origin.instruction_result.index != first_origin.index + @as(u32, @intCast(offset)) or
                    value_id.index() != first_id.index() + offset) break :blk false;
            }
            break :blk true;
        },
        .capture => false,
    };
}

fn runtimeCaptureCount(runtime: luau_runtime.Plan) usize {
    var count: usize = 0;
    for (luau_runtime.capabilities) |capability| count += @intFromBool(runtime.requires(capability));
    return count;
}

fn topLevelFunctionCount(program: *const ir.Program) usize {
    var count: usize = 0;
    for (program.functions) |function| {
        if (function.id != program.entry_function and function.lexical_parent == null) count += 1;
    }
    return count;
}

fn saturatingAdd(left: usize, right: usize) usize {
    return std.math.add(usize, left, right) catch std.math.maxInt(usize);
}

test "automatic register certificate covers the function-scope escape flags of nested_repeat" {
    // The native held-out case nested_repeat: its disassembly-path IR
    // (the normalized handoff of that case, as lifted in the native evaluation,
    // embedded in the test below), re-serialized with
    // one entity per line. Its worker (function 1, two parameters) runs two nested loops whose exits
    // the automatic layout routes through function-scope escape flags; the automatic output declares
    // two such flags and needs 10 locals, maxstacksize 11 (luau-compile -O0).
    const nested_repeat_ir =
        \\{"schema_version":"lifter_ir_v1","program_id":"native-nested_repeat","source_semantics":"luau","entry_function":0,"entry_bindings":[],"external_bindings":[],"functions":[
        \\{"id":0,"name_hint":"module","lexical_parent":null,"parameters":[],"captures":[],"local_places":[],"blocks":[0],"entry_block":0,"is_variadic":false,"vararg_pack":null,"evidence":[0]},
        \\{"id":1,"name_hint":"worker","lexical_parent":0,"parameters":[0,1],"captures":[],"local_places":[0,1,2,3,4,5],"blocks":[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],"entry_block":1,"is_variadic":false,"vararg_pack":null,"evidence":[0]}]
        \\,"blocks":[
        \\{"id":0,"function":0,"name_hint":null,"parameters":[],"instructions":[37],"terminator":{"return_values":[27]},"evidence":[0]},
        \\{"id":1,"function":1,"name_hint":"register_entry","parameters":[],"instructions":[0,1],"terminator":{"jump":{"target":2,"arguments":[]}},"evidence":[0]},
        \\{"id":2,"function":1,"name_hint":"instruction_1","parameters":[],"instructions":[2,3],"terminator":{"jump":{"target":3,"arguments":[]}},"evidence":[1]},
        \\{"id":3,"function":1,"name_hint":"instruction_2","parameters":[],"instructions":[4,5],"terminator":{"jump":{"target":4,"arguments":[]}},"evidence":[2]},
        \\{"id":4,"function":1,"name_hint":"instruction_3","parameters":[],"instructions":[6,7],"terminator":{"jump":{"target":5,"arguments":[]}},"evidence":[3]},
        \\{"id":5,"function":1,"name_hint":"instruction_4","parameters":[],"instructions":[8,9],"terminator":{"jump":{"target":6,"arguments":[]}},"evidence":[4]},
        \\{"id":6,"function":1,"name_hint":"instruction_5","parameters":[],"instructions":[10,11,12,13],"terminator":{"jump":{"target":7,"arguments":[]}},"evidence":[5]},
        \\{"id":7,"function":1,"name_hint":"instruction_6","parameters":[],"instructions":[14,15,16,17],"terminator":{"jump":{"target":8,"arguments":[]}},"evidence":[6]},
        \\{"id":8,"function":1,"name_hint":"instruction_7","parameters":[],"instructions":[18,19,20,21],"terminator":{"jump":{"target":9,"arguments":[]}},"evidence":[7]},
        \\{"id":9,"function":1,"name_hint":"instruction_8","parameters":[],"instructions":[22,23],"terminator":{"jump":{"target":10,"arguments":[]}},"evidence":[8]},
        \\{"id":10,"function":1,"name_hint":"instruction_9","parameters":[],"instructions":[24,25,26],"terminator":{"branch":{"condition":18,"then_edge":{"target":12,"arguments":[]},"else_edge":{"target":11,"arguments":[]}}},"evidence":[9]},
        \\{"id":11,"function":1,"name_hint":"instruction_10","parameters":[],"instructions":[],"terminator":{"jump":{"target":5,"arguments":[]}},"evidence":[10]},
        \\{"id":12,"function":1,"name_hint":"instruction_11","parameters":[],"instructions":[27,28],"terminator":{"jump":{"target":13,"arguments":[]}},"evidence":[11]},
        \\{"id":13,"function":1,"name_hint":"instruction_12","parameters":[],"instructions":[29,30,31,32],"terminator":{"jump":{"target":14,"arguments":[]}},"evidence":[12]},
        \\{"id":14,"function":1,"name_hint":"instruction_13","parameters":[],"instructions":[33,34,35],"terminator":{"branch":{"condition":25,"then_edge":{"target":16,"arguments":[]},"else_edge":{"target":15,"arguments":[]}}},"evidence":[13]},
        \\{"id":15,"function":1,"name_hint":"instruction_14","parameters":[],"instructions":[],"terminator":{"jump":{"target":4,"arguments":[]}},"evidence":[14]},
        \\{"id":16,"function":1,"name_hint":"instruction_15","parameters":[],"instructions":[36],"terminator":{"return_values":[26]},"evidence":[15]}]
        \\,"instructions":[
        \\{"id":0,"block":1,"operation":{"place_write":{"place":0,"value":0}},"results":[],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[0],"claims":[]},
        \\{"id":1,"block":1,"operation":{"place_write":{"place":1,"value":1}},"results":[],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[0],"claims":[]},
        \\{"id":2,"block":2,"operation":{"constant":{"number":0}},"results":[2],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[1],"claims":[]},
        \\{"id":3,"block":2,"operation":{"place_write":{"place":2,"value":2}},"results":[],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[1],"claims":[]},
        \\{"id":4,"block":3,"operation":{"constant":{"number":0}},"results":[3],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[2],"claims":[]},
        \\{"id":5,"block":3,"operation":{"place_write":{"place":3,"value":3}},"results":[],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[2],"claims":[]},
        \\{"id":6,"block":4,"operation":{"constant":{"number":0}},"results":[4],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[3],"claims":[]},
        \\{"id":7,"block":4,"operation":{"place_write":{"place":4,"value":4}},"results":[],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[3],"claims":[]},
        \\{"id":8,"block":5,"operation":{"constant":{"number":1}},"results":[5],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[4],"claims":[]},
        \\{"id":9,"block":5,"operation":{"place_write":{"place":5,"value":5}},"results":[],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[4],"claims":[]},
        \\{"id":10,"block":6,"operation":{"place_read":4},"results":[6],"pack_result":null,"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[5],"claims":[]},
        \\{"id":11,"block":6,"operation":{"place_read":5},"results":[7],"pack_result":null,"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[5],"claims":[]},
        \\{"id":12,"block":6,"operation":{"binary":{"operator":"add","left":6,"right":7,"mode":"semantic","shift_behavior":null}},"results":[8],"pack_result":null,"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true},"evidence":[5],"claims":[]},
        \\{"id":13,"block":6,"operation":{"place_write":{"place":4,"value":8}},"results":[],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[5],"claims":[]},
        \\{"id":14,"block":7,"operation":{"place_read":2},"results":[9],"pack_result":null,"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[6],"claims":[]},
        \\{"id":15,"block":7,"operation":{"place_read":0},"results":[10],"pack_result":null,"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[6],"claims":[]},
        \\{"id":16,"block":7,"operation":{"binary":{"operator":"add","left":9,"right":10,"mode":"semantic","shift_behavior":null}},"results":[11],"pack_result":null,"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true},"evidence":[6],"claims":[]},
        \\{"id":17,"block":7,"operation":{"place_write":{"place":5,"value":11}},"results":[],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[6],"claims":[]},
        \\{"id":18,"block":8,"operation":{"place_read":5},"results":[12],"pack_result":null,"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[7],"claims":[]},
        \\{"id":19,"block":8,"operation":{"place_read":4},"results":[13],"pack_result":null,"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[7],"claims":[]},
        \\{"id":20,"block":8,"operation":{"binary":{"operator":"add","left":12,"right":13,"mode":"semantic","shift_behavior":null}},"results":[14],"pack_result":null,"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true},"evidence":[7],"claims":[]},
        \\{"id":21,"block":8,"operation":{"place_write":{"place":2,"value":14}},"results":[],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[7],"claims":[]},
        \\{"id":22,"block":9,"operation":{"constant":{"number":2}},"results":[15],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[8],"claims":[]},
        \\{"id":23,"block":9,"operation":{"place_write":{"place":5,"value":15}},"results":[],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[8],"claims":[]},
        \\{"id":24,"block":10,"operation":{"place_read":5},"results":[16],"pack_result":null,"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[9],"claims":[]},
        \\{"id":25,"block":10,"operation":{"place_read":4},"results":[17],"pack_result":null,"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[9],"claims":[]},
        \\{"id":26,"block":10,"operation":{"binary":{"operator":"less_equal","left":16,"right":17,"mode":"semantic","shift_behavior":null}},"results":[18],"pack_result":null,"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true},"evidence":[9],"claims":[]},
        \\{"id":27,"block":12,"operation":{"constant":{"number":1}},"results":[19],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[11],"claims":[]},
        \\{"id":28,"block":12,"operation":{"place_write":{"place":5,"value":19}},"results":[],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[11],"claims":[]},
        \\{"id":29,"block":13,"operation":{"place_read":3},"results":[20],"pack_result":null,"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[12],"claims":[]},
        \\{"id":30,"block":13,"operation":{"place_read":5},"results":[21],"pack_result":null,"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[12],"claims":[]},
        \\{"id":31,"block":13,"operation":{"binary":{"operator":"add","left":20,"right":21,"mode":"semantic","shift_behavior":null}},"results":[22],"pack_result":null,"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true},"evidence":[12],"claims":[]},
        \\{"id":32,"block":13,"operation":{"place_write":{"place":3,"value":22}},"results":[],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[12],"claims":[]},
        \\{"id":33,"block":14,"operation":{"place_read":1},"results":[23],"pack_result":null,"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[13],"claims":[]},
        \\{"id":34,"block":14,"operation":{"place_read":3},"results":[24],"pack_result":null,"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[13],"claims":[]},
        \\{"id":35,"block":14,"operation":{"binary":{"operator":"less_equal","left":23,"right":24,"mode":"semantic","shift_behavior":null}},"results":[25],"pack_result":null,"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true},"evidence":[13],"claims":[]},
        \\{"id":36,"block":16,"operation":{"place_read":2},"results":[26],"pack_result":null,"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[15],"claims":[]},
        \\{"id":37,"block":0,"operation":{"make_closure":{"function":1,"bindings":[]}},"results":[27],"pack_result":null,"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false},"evidence":[0],"claims":[]}]
        \\,"values":[
        \\{"id":0,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":"argument_0","origin":{"parameter":0}},
        \\{"id":1,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":"argument_1","origin":{"parameter":1}},
        \\{"id":2,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":2,"index":0}}},
        \\{"id":3,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":4,"index":0}}},
        \\{"id":4,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":6,"index":0}}},
        \\{"id":5,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":8,"index":0}}},
        \\{"id":6,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":10,"index":0}}},
        \\{"id":7,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":11,"index":0}}},
        \\{"id":8,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":12,"index":0}}},
        \\{"id":9,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":14,"index":0}}},
        \\{"id":10,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":15,"index":0}}},
        \\{"id":11,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":16,"index":0}}},
        \\{"id":12,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":18,"index":0}}},
        \\{"id":13,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":19,"index":0}}},
        \\{"id":14,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":20,"index":0}}},
        \\{"id":15,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":22,"index":0}}},
        \\{"id":16,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":24,"index":0}}},
        \\{"id":17,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":25,"index":0}}},
        \\{"id":18,"function":1,"type":{"kind":"boolean","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":26,"index":0}}},
        \\{"id":19,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":27,"index":0}}},
        \\{"id":20,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":29,"index":0}}},
        \\{"id":21,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":30,"index":0}}},
        \\{"id":22,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":31,"index":0}}},
        \\{"id":23,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":33,"index":0}}},
        \\{"id":24,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":34,"index":0}}},
        \\{"id":25,"function":1,"type":{"kind":"boolean","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":35,"index":0}}},
        \\{"id":26,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":36,"index":0}}},
        \\{"id":27,"function":0,"type":{"kind":"function","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":37,"index":0}}}]
        \\,"value_packs":[],"places":[
        \\{"id":0,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":"r0","origin":{"local":0},"evidence":[0]},
        \\{"id":1,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":"r1","origin":{"local":1},"evidence":[0]},
        \\{"id":2,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":"r2","origin":{"local":2},"evidence":[0]},
        \\{"id":3,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":"r3","origin":{"local":3},"evidence":[0]},
        \\{"id":4,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":"r4","origin":{"local":4},"evidence":[0]},
        \\{"id":5,"function":1,"type":{"kind":"dynamic","bit_width":0,"signed":false},"name_hint":"r5","origin":{"local":5},"evidence":[0]}]
        \\,"captures":[],"evidence":[
        \\{"id":0,"kind":"decoded_record","locator":"compiler-listing:0","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":1,"kind":"decoded_record","locator":"compiler-listing:0:line:5","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":2,"kind":"decoded_record","locator":"compiler-listing:0:line:6","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":3,"kind":"decoded_record","locator":"compiler-listing:0:line:7","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":4,"kind":"decoded_record","locator":"compiler-listing:0:line:8","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":5,"kind":"decoded_record","locator":"compiler-listing:0:line:9","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":6,"kind":"decoded_record","locator":"compiler-listing:0:line:10","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":7,"kind":"decoded_record","locator":"compiler-listing:0:line:11","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":8,"kind":"decoded_record","locator":"compiler-listing:0:line:12","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":9,"kind":"decoded_record","locator":"compiler-listing:0:line:13","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":10,"kind":"decoded_record","locator":"compiler-listing:0:line:14","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":11,"kind":"decoded_record","locator":"compiler-listing:0:line:15","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":12,"kind":"decoded_record","locator":"compiler-listing:0:line:16","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":13,"kind":"decoded_record","locator":"compiler-listing:0:line:17","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":14,"kind":"decoded_record","locator":"compiler-listing:0:line:18","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"},
        \\{"id":15,"kind":"decoded_record","locator":"compiler-listing:0:line:19","digest":"18e064a6cac4d4ffbe21d366607a2eefa9601016c42b69cec5285c6f35f3ac45"}]
        \\,"solver_terms":[],"constraints":[],"queries":[],"solver_models":[],"unsat_cores":[],"certificates":[],"edge_rewrites":[],"claims":[],"obligations":[]}
    ;
    const allocator = std.testing.allocator;
    const parsed = try std.json.parseFromSlice(ir.Program, allocator, nested_repeat_ir, .{
        .allocate = .alloc_always,
        .ignore_unknown_fields = true,
    });
    defer parsed.deinit();

    // The per-function certification path of validateWithStrategy and
    // validatePrepared (standard target, automatic strategy) for the worker.
    var transfer_arena = std.heap.ArenaAllocator.init(allocator);
    defer transfer_arena.deinit();
    const program = try lexical_transfer.prepareInArena(transfer_arena.allocator(), &parsed.value);
    var readable = try readable_scope.Scope.init(allocator, &program);
    defer readable.deinit();
    var emission = try emission_planning.Plan.init(allocator, &program, .standard_luau);
    defer emission.deinit();
    const function = program.functions[1];
    var analysis = try cfg.Analysis.init(allocator, &program, function);
    defer analysis.deinit();
    var structured = try structure.Plan.initWithArbitraryFallback(allocator, &analysis);
    defer structured.deinit();
    var scopes = try emission_scope.Plan.init(
        allocator,
        &program,
        function,
        &analysis,
        &structured,
        &emission.packs,
        &emission.dead,
        &emission.place_writes,
        &emission.place_reads,
        &emission.fused_values,
        &emission.closure_stores,
    );
    defer scopes.deinit();
    if (!structured.root.arbitrary_cfg) {
        branch_expression.markDeclarations(&program, &emission, &scopes, structured.root, true);
    }
    const storage_locals = saturatingAdd(
        @intFromBool(emission.names.functionUsesStorage(function)),
        @intFromBool(emission.names.functionUsesValueStorage(&program, function)),
    );
    const base = try functionRegisterBase(allocator, function.parameters.len, storage_locals, structured.root);
    const pressure = try maximumPressure(allocator, &program, &readable, &emission, &scopes, function, base);
    // The certified total must cover the emitted peak.
    try std.testing.expectEqual(@as(usize, 11), pressure.total);
}
