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
/// it; `dispatcher` mirrors the emitter's forced-dispatcher layout (K16).
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
        const base = saturatingAdd(
            saturatingAdd(function_base, structured_escape.maxOwnedDepth(structured.root)),
            storage_locals,
        );
        const pressure = try maximumPressure(allocator, program, readable, &emission, &scopes, function, base);
        // The dispatcher (arbitrary-CFG) layout declares a flat set of locals at
        // the function root that `maximumPressure` undercounts: it scores only
        // materialized (scoped) bindings and omits both the never-materialized
        // declarations and the `__lifter_pc` slot. Budget the emitter's own
        // declaration count plus the pc slot so a forced or natural dispatcher
        // layout past the compiler's limit is refused at admission (K16).
        var effective_locals = pressure.locals;
        var effective_total = pressure.total;
        if (structured.root.arbitrary_cfg) {
            const flat_locals = saturatingAdd(
                saturatingAdd(function_base, storage_locals),
                saturatingAdd(emit_luau.arbitraryDeclarationCount(program, &emission, function), 1),
            );
            effective_locals = @max(effective_locals, flat_locals);
            effective_total = @max(effective_total, saturatingAdd(flat_locals, pressure.total -| pressure.locals));
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
