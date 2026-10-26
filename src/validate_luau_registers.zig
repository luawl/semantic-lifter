const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const compound_update = @import("compound_update.zig");
const dead_code = @import("dead_code.zig");
const diagnostics = @import("diagnostics.zig");
const branch_expression = @import("emit_luau_branch_expr.zig");
const emit_luau = @import("emit_luau.zig");
const emission_planning = @import("emit_luau_plan.zig");
const emission_scope = @import("emit_luau_scope.zig");
const iteration_protocol = @import("iteration_protocol.zig");
const lexical = @import("emit_luau_lexical.zig");
const lexical_transfer = @import("lexical_transfer.zig");
const luau_runtime = @import("luau_runtime.zig");
const luau_syntax = @import("luau_syntax.zig");
const readable_scope = @import("readable_scope.zig");
const runtime_uses = @import("runtime_uses.zig");
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

    pub fn isBoxedPlace(self: StableCaptureValues, place_id: ir.PlaceId) bool {
        return self.scopes.arbitraryPlaceNeedsPerExecutionCell(place_id);
    }
};

const Pressure = struct {
    locals: usize,
    total: usize,
    /// The registers a host holds above its locals at most, over the hosts: the native `for` frames on its chain and
    /// the larger of its closure snapshots and its statement frames.
    scratch: usize,
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
    scope: *const readable_scope.Scope,
    target: luau_runtime.Target,
    strategy: EmissionStrategy,
) !void {
    return validateWithLayout(allocator, report, program, scope, target, strategy, null);
}

/// `validateWithStrategy` with every function marked in `flat_functions` (indexed by function id; null marks none)
/// certified in the dispatcher layout, the layout `emitFunctionBody` writes for a function whose structured plan the
/// region writer refused: the register terms, the syntax depth, the jump budget and the stable values handed to the
/// upvalue certificate of a marked function are computed on that layout.
pub fn validateWithLayout(
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    _: *const readable_scope.Scope,
    target: luau_runtime.Target,
    strategy: EmissionStrategy,
    flat_functions: ?[]const bool,
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
    try validatePrepared(allocator, report, &prepared, &readable, target, strategy, flat_functions);
    if (stage_trace.enabled) std.debug.print("register_validation stage=done\n", .{});
}

fn validatePrepared(
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    target: luau_runtime.Target,
    strategy: EmissionStrategy,
    flat_functions: ?[]const bool,
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

    // The emitter sized the marks on its own preparation of this program, one mark per function this walk visits;
    // a different count means the two preparations disagree and a function written flat could go uncertified.
    if (flat_functions) |marks| std.debug.assert(marks.len == program.functions.len);
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
        const written_flat = if (flat_functions) |marks| function.id.index() < marks.len and marks[function.id.index()] else false;
        var structured = (if (strategy == .dispatcher or written_flat)
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
        const pressure = try maximumPressure(allocator, program, readable, &emission, &scopes, function, base, structured.root);
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
            // A closure creation declares its snapshot locals in a `do` block above every flat declaration, and a
            // statement's own registers sit above them all.
            effective_locals = @max(effective_locals, saturatingAdd(flat_locals, try peakClosureSnapshotLocals(allocator, program, &emission, &scopes, function)));
            effective_total = @max(effective_total, saturatingAdd(flat_locals, pressure.scratch));
            // A boxed per-execution cell snapshots its holder with one transient `do`-block local
            // per boxed capture at each closure creation; sequential creations reuse the registers, so the peak is
            // the most boxed cells a single `make_closure` captures. The comprehensive flat `@max` above masks the
            // scoped pressure, so add the peak to the flat frame in lockstep with the emission (like the
            // `luau_numeric`/`generic_for_next` additions). The root holder count is unchanged.
            const peak_boxed_snapshots = peakBoxedSnapshots(program, &emission, &scopes, function);
            if (peak_boxed_snapshots != 0) {
                effective_locals = @max(effective_locals, saturatingAdd(flat_locals, peak_boxed_snapshots));
                effective_total = @max(effective_total, saturatingAdd(flat_locals, saturatingAdd(peak_boxed_snapshots, pressure.total -| pressure.locals)));
            }
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
            // A `generic_for_next` transition is emitted flat by `emitGenericForNextTransition`
            // (`src/emit_luau.zig`) as a `do` block with three private locals (`__lifter_generic_iterator`,
            // `__lifter_generic_state`, `__lifter_generic_control`), two more under its `if <initial>` guard
            // (`__lifter_generic_metatable`, `__lifter_generic_method`) around a three-result `__iter` call,
            // and the loop values stored above the three privates. Budget the five private locals and the
            // iterator call frame (three results above five locals, or the loop values' slots, whichever is
            // larger) so a flat function holding the transition past the compiler's limit is refused at
            // admission, in lockstep with `emitGenericForNextTransition`.
            for (function.blocks) |block_id| {
                if (block_id.index() >= program.blocks.len) continue;
                for (program.blocks[block_id.index()].instructions) |instruction_id| {
                    if (instruction_id.index() >= program.instructions.len or emission.dead.contains(instruction_id)) continue;
                    const instruction = program.instructions[instruction_id.index()];
                    switch (instruction.operation) {
                        .generic_for_next => {
                            if (instruction.results.len < 3) continue;
                            var targets: usize = 0;
                            for (instruction.results[3..]) |result| {
                                targets = saturatingAdd(targets, if (emission.names.valueUsesStorage(result)) 2 else 1);
                            }
                            effective_locals = @max(effective_locals, saturatingAdd(flat_locals, 5));
                            effective_total = @max(effective_total, saturatingAdd(flat_locals, saturatingAdd(3, @max(5, targets))));
                        },
                        else => {},
                    }
                }
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

/// The most snapshot locals a single closure creation of this function declares in its `do` block: one per value
/// binding the closure snapshots and one per boxed per-execution cell it captures, live together.
fn peakClosureSnapshotLocals(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    function: ir.Function,
) std.mem.Allocator.Error!usize {
    var peak: usize = 0;
    for (function.blocks) |block_id| {
        if (block_id.index() >= program.blocks.len) continue;
        for (program.blocks[block_id.index()].instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len or emission.dead.contains(instruction_id)) continue;
            const closure = switch (program.instructions[instruction_id.index()].operation) {
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
                error.InvalidClosureBinding => continue,
            };
            defer closure_plan.deinit();
            peak = @max(peak, saturatingAdd(closure_plan.value_bindings.len, closure_plan.snapshot_bindings.len));
        }
    }
    return peak;
}

/// The function-scope registers a certified layout holds before any scoped
/// The most boxed per-execution cells a single `make_closure` in this function captures.
/// Each such capture snapshots its holder with one transient `do`-block local at the creation site; the
/// snapshots of one creation are live together, while sequential creations reuse the registers. The holder
/// itself stays a root-list place (counted by `arbitraryDeclarationCount`), so only the snapshots are added.
fn peakBoxedSnapshots(
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    function: ir.Function,
) usize {
    var peak: usize = 0;
    for (function.blocks) |block_id| {
        if (block_id.index() >= program.blocks.len) continue;
        for (program.blocks[block_id.index()].instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len or emission.dead.contains(instruction_id)) continue;
            const closure = switch (program.instructions[instruction_id.index()].operation) {
                .make_closure => |value| value,
                else => continue,
            };
            var count: usize = 0;
            for (closure.bindings) |binding| switch (binding) {
                .place => |place_id| {
                    if (scopes.arbitraryPlaceNeedsPerExecutionCell(place_id)) count += 1;
                },
                .value => {},
            };
            peak = @max(peak, count);
        }
    }
    return peak;
}

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

/// The register certificate of one function: the larger of two counts. The first is the held frame with the charges
/// every statement takes in any layout (calls, constructors, returns, edge cycles, closure snapshots, native `for`
/// frames). The second also charges every statement root its own registers (`addStatementRootFrames`) and counts
/// the locals the text declares: a value a branch composition writes inline in its consumer is not one of them.
fn maximumPressure(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    function: ir.Function,
    base: usize,
    root: *const structure.Region,
) std.mem.Allocator.Error!Pressure {
    const held = try hostPressure(allocator, program, readable, emission, scopes, function, base, root, false);
    const rooted = try hostPressure(allocator, program, readable, emission, scopes, function, base, root, true);
    return .{
        .locals = @max(held.locals, rooted.locals),
        .total = @max(held.total, rooted.total),
        .scratch = @max(held.scratch, rooted.scratch),
    };
}

fn hostPressure(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    function: ir.Function,
    base: usize,
    root: *const structure.Region,
    statement_roots: bool,
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
    // The registers a native `for` holds that no value scope counts (`addNativeForFootprints`): summed along the host
    // chain as the locals are, and added to the total only.
    const frames = try allocator.alloc(usize, scopes.pressureSlotCount());
    defer allocator.free(frames);
    @memset(frames, 0);

    var compositions: Compositions = .{};
    defer compositions.deinit(allocator);
    if (statement_roots and !root.arbitrary_cfg) try compositions.addRegion(allocator, program, emission, scopes, root);

    for (program.values) |value| {
        if (value.function != function.id) continue;
        if (emission.names.valueUsesStorage(value.id)) continue;
        // A value a composition defers into its consumer (`return ..., c and x`) or absorbs as its condition is
        // written inline there and declares no local; the consumer's statement frame holds its registers.
        if (compositions.writesInline(value.id)) continue;
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

    if (!root.arbitrary_cfg) try addNativeForFootprints(allocator, program, emission, scopes, root, locals, frames, temporaries);
    if (statement_roots) try addStatementRootFrames(allocator, program, readable, emission, scopes, function, root, &compositions, temporaries);

    var maximum_locals = base;
    var maximum_total = base;
    var maximum_scratch: usize = 0;
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
        var frame_total: usize = 0;
        var current: ?emission_scope.ScopeId = host;
        while (current) |physical| {
            local_total = saturatingAdd(local_total, locals[physical]);
            frame_total = saturatingAdd(frame_total, frames[physical]);
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
        const scratch = saturatingAdd(frame_total, @max(closure_locals[host], temporaries[host]));
        maximum_scratch = @max(maximum_scratch, scratch);
        maximum_total = @max(maximum_total, saturatingAdd(local_total, scratch));
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
    return .{ .locals = maximum_locals, .total = maximum_total, .scratch = maximum_scratch };
}

/// Registers a native `for` holds that no value scope counts (`emit_luau.nativeForAt`): its frame registers beside its
/// loop variables, from the `for` statement to its `end`, and its completion local, from its declaration before the
/// `for` to the end of the enclosing block, where the completion locals of sibling loops are live together. The loop
/// variables are counted as values. No line declares the header's parameters, but each one that has a value scope and
/// no value storage is counted as a local of the block the `for` is written in or of a block around it, so it covers
/// one of these registers: under value storage none does, nor does an aliased parameter of a one-shot header.
fn addNativeForFootprints(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    region: *const structure.Region,
    locals: []usize,
    frames: []usize,
    temporaries: []usize,
) std.mem.Allocator.Error!void {
    for (region.nodes, 0..) |*node, index| {
        if (try emit_luau.nativeForAt(allocator, program, emission, scopes, region, index)) |native| {
            var covered: usize = 0;
            for (program.blocks[native.header.index()].parameters) |parameter| {
                if (!emission.names.valueUsesStorage(parameter) and scopes.valueScope(parameter) != null) covered += 1;
            }
            const completion: usize = @intFromBool(native.completion);
            const completion_uncovered = completion -| covered;
            const frame_uncovered = (native.hidden_registers + completion) -| (covered + completion_uncovered);
            if (scopes.nodeScope(node)) |scope| {
                // The completion local is declared in the block the `for` is written in, and the `for` statement holds
                // its frame there.
                addAtScope(locals, scopes, scope, completion_uncovered);
                addTemporaryAtScope(temporaries, scopes, scope, frame_uncovered);
                // A terminal loop boundary's body is written in the node's own scope.
                if (native.body == null) addAtScope(frames, scopes, scope, frame_uncovered);
            }
            if (native.body) |body| {
                // Every physical block the body's nodes are written in (its container groups) holds the frame.
                var previous: emission_scope.ScopeId = emission_scope.invalid_scope;
                for (body.nodes) |*body_node| {
                    const container = scopes.nodeContainerScope(body_node) orelse continue;
                    const host = scopes.physicalHost(container) orelse continue;
                    if (host == previous or host >= frames.len) continue;
                    previous = host;
                    frames[host] = saturatingAdd(frames[host], frame_uncovered);
                }
            }
        }
        switch (node.*) {
            .block, .loop_control, .loop_terminal => {},
            .branch => |branch| {
                try addNativeForFootprints(allocator, program, emission, scopes, branch.then_region, locals, frames, temporaries);
                try addNativeForFootprints(allocator, program, emission, scopes, branch.else_region, locals, frames, temporaries);
            },
            .loop => |loop| try addNativeForFootprints(allocator, program, emission, scopes, loop.body_region, locals, frames, temporaries),
            .latch_loop => |loop| try addNativeForFootprints(allocator, program, emission, scopes, loop.body_region, locals, frames, temporaries),
            .infinite_loop => |loop| {
                try addNativeForFootprints(allocator, program, emission, scopes, loop.body_region, locals, frames, temporaries);
                if (loop.shared_side_exit) |side_exit| {
                    for (side_exit.entries) |entry| {
                        try addNativeForFootprints(allocator, program, emission, scopes, entry.region, locals, frames, temporaries);
                    }
                }
            },
            .loop_boundary => |control| {
                try addNativeForFootprints(allocator, program, emission, scopes, control.body_region, locals, frames, temporaries);
                switch (control.boundary) {
                    .side_exit => |side_exit| try addNativeForFootprints(allocator, program, emission, scopes, side_exit.region, locals, frames, temporaries),
                    .side_escape => |side_escape| try addNativeForFootprints(allocator, program, emission, scopes, side_escape.region, locals, frames, temporaries),
                    else => {},
                }
            },
        }
    }
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
        // A constructor's frame holds its tail pack as written (`emittedConstructorFrame`).
        .make_table_literal => |constructor| return emittedConstructorFrame(program, emission, scopes, instruction, constructor),
        else => operationTemporaryFrameSize(instruction.operation) orelse return null,
    };
    const pack_id = switch (instruction.operation) {
        .call => |call| call.argument_pack,
        .namecall => |call| call.argument_pack,
        .protected_call => |call| call.argument_pack,
        .coroutine_resume => |call| call.argument_pack,
        .coroutine_yield => |call| call.argument_pack,
        .table_set_pack => |operation| operation.pack,
        else => null,
    } orelse return raw;
    const width = emittedPackWidth(program, emission, instruction.id, pack_id);
    return raw - 1 + width;
}

/// The frame of a table constructor, from its table register up, as the emitter writes it (`plannedTableConstructor`,
/// `emitTableConstructorInstruction`) and luau-compile builds it (`ItemPricing.constructorFrame`), its tail pack
/// included; a statement `__lifter_value_storage[k] = { ... }` also holds the key `k` in a register under the table.
/// A constructor with an item whose written form `ItemPricing` does not price keeps the per-field charge.
fn emittedConstructorFrame(
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    instruction: ir.Instruction,
    constructor: ir.TableConstructor,
) usize {
    const pricing: ItemPricing = .{ .program = program, .emission = emission, .scopes = scopes };
    const frame = pricing.constructorFrame(instruction.id, constructor, 0) orelse
        perFieldConstructorFrame(program, emission, instruction.id, constructor);
    const stored_statement = instruction.results.len == 1 and
        !emission.fused_values.contains(instruction.id) and
        emission.place_writes.consumerForProducer(instruction.id) == null and
        emission.names.valueUsesStorage(instruction.results[0]);
    return saturatingAdd(frame, @intFromBool(stored_statement));
}

/// The charge of a constructor whose items are not priced as built: the table, one register per field, the tail pack at
/// its written width, and at least the three registers a constructor with a keyed field takes.
fn perFieldConstructorFrame(
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    consumer: ir.InstructionId,
    constructor: ir.TableConstructor,
) usize {
    var frame = saturatingAdd(1, constructor.fields.len);
    if (constructor.tail_pack) |pack_id| frame = saturatingAdd(frame, emittedPackWidth(program, emission, consumer, pack_id));
    for (constructor.fields) |field| switch (field) {
        .keyed => return @max(frame, 3),
        .list => {},
    };
    return frame;
}

/// `unpack(name, 1, rawget(name, 0))`, the expansion of a stored pack: the captured unpack, the name, `1`, then the
/// nested call of the captured rawget in the fourth register.
const stored_pack_need: usize = 6;

/// An upvalue indexed by a key, `u[k]`: the upvalue, the key and the result.
const indexed_upvalue_need: usize = 3;

/// How luau-compile builds a written expression into its target register (a constructor's batch slot, a call's frame
/// slot, an operand register), every literal priced as at -O0, where it takes a register, `-5` is a unary minus and
/// `(0 / 0)` a division.
const Written = struct {
    /// Registers from the target up, the target included.
    need: usize,
    /// A local register of this function written by name: an operand that takes no register of its own.
    register: bool = false,
    /// Written as a call, or handing its target to one (`(f(x))`, `(f(x)).k`, `x or f()`): below the register top it is
    /// built above the top and moved down.
    relocates: bool = false,
    /// Written as an unparenthesized call: as the last item of a constructor it takes every result, built at its slot.
    multret: bool = false,
    /// Written as a literal: from -O1 luau-compile reads it as a constant operand of `and` and `or` (`ANDK`, `ORK`).
    constant: bool = false,
    /// Written as a table constructor: assigned to a local declared before, it is built above the register top and moved.
    table: bool = false,
    /// A field of an object (`o.name`): assigned to a local declared before, the object takes these registers above the
    /// register top and the field is read into the local.
    object_need: ?usize = null,
    /// An if-else composition: assigned to a local declared before or built in a register below the top, its condition
    /// and its arms take at most these registers above the register top.
    above: ?usize = null,
};

/// The registers an operand takes when luau-compile evaluates it for an instruction that reads registers: none for a
/// local register.
fn autoNeed(written: Written) usize {
    return if (written.register) 0 else written.need;
}

/// The register an evaluated left operand holds while the right one is evaluated: none for a local register.
fn heldRegister(written: Written) usize {
    return @intFromBool(!written.register);
}

/// The registers an operand that is not the last of a concatenation takes above the register top: built in its
/// register, its own register is below the top; built as a call, it is all above.
fn aboveTop(written: Written) usize {
    return if (written.relocates) written.need else written.need -| 1;
}

/// The register top of an array item, counted from the first register above the table: built at its batch slot (the
/// slot returns to 0 when a batch of `reserve` items is stored), or, for the last item below slot `reserve - 1` that is
/// not an unparenthesized call, above the reserve.
fn listItemTop(reserve: usize, slot: *usize, written: Written, last: bool) usize {
    if (slot.* == reserve) slot.* = 0;
    const at = slot.*;
    slot.* += 1;
    if (!last or written.multret or at + 1 == reserve) return saturatingAdd(at, written.need);
    return saturatingAdd(reserve, if (written.relocates) written.need else written.need -| 1);
}

/// A literal at -O0: one register; a negative number is a unary minus over its magnitude, and `(0 / 0)`, `(1 / 0)` or
/// `(-1 / 0)` a division of two constants.
fn literalNeed(literal_value: ir.Literal) usize {
    return switch (literal_value) {
        .special_number => 3,
        .integer => |text| if (text.len != 0 and text[0] == '-') 2 else 1,
        .number => |number| if (std.math.signbit(number)) 2 else 1,
        .nil_value, .boolean, .string => 1,
    };
}

/// A tail pack as written: one multi-value item (`...`, `select(k, ...)`, a stored pack's expansion or the invocation
/// that produces the pack), or the values of a `pack_values`, written as array items.
const Tail = struct {
    single: ?Written = null,
    items: []const ir.ValueId = &.{},

    fn count(self: Tail) usize {
        return @as(usize, @intFromBool(self.single != null)) + self.items.len;
    }
};

/// Prices the items of a constructor as `valueUseContext` and `fusedInstructionExpression` write them. Null for a form it
/// does not price: a value a branch composition may write in its place (`c and x`, `if c then x else y`), a producer
/// role or operation the renderer refuses, or an expression deeper than `max_fused_expression_operations`.
const ItemPricing = struct {
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    /// The compositions a statement root writes inline; without them (a constructor's items as charged at its
    /// instruction) a value a composition may write in its place is not priced.
    compositions: ?*const Compositions = null,
    level: PricingLevel = .o0,
    /// At -O1, the constant locals the statement reads.
    constant_reads: ?*ConstantReads = null,

    /// Registers a constructor holds from its table register up. luau-compile reserves R = min(16, L) registers above the
    /// table for its L array items (the written items of a tail included) before the first item and keeps them to the
    /// end. An array item before the last is built at its batch slot with the register top just above it; the slot
    /// returns to 0 when a batch of R is stored and at every keyed field, which is built above the whole reserve. The
    /// last array item is built at its slot when it is an unparenthesized call or `...` or sits at slot R - 1; otherwise
    /// what it needs above its slot sits above the reserve, one register more when it is built as a call.
    fn constructorFrame(self: ItemPricing, consumer: ir.InstructionId, constructor: ir.TableConstructor, depth: usize) ?usize {
        if (depth >= luau_runtime.max_fused_expression_operations) return null;
        const tail: Tail = if (constructor.tail_pack) |pack_id| self.tailItems(consumer, pack_id, depth) orelse return null else .{};
        var list_count: usize = tail.count();
        for (constructor.fields) |field| list_count += @intFromBool(field == .list);
        const item_count = constructor.fields.len + tail.count();
        if (item_count == 0) return 1;
        const reserve: usize = @min(16, list_count);
        var peak: usize = reserve;
        var slot: usize = 0;
        for (constructor.fields, 0..) |field, index| {
            const last = index + 1 == item_count;
            switch (field) {
                .keyed => |keyed| {
                    slot = 0;
                    peak = @max(peak, saturatingAdd(reserve, self.keyedNeed(keyed.key, keyed.value, depth) orelse return null));
                },
                .list => |item| peak = @max(peak, listItemTop(reserve, &slot, self.writtenValue(item, depth) orelse return null, last)),
            }
        }
        if (tail.single) |written| peak = @max(peak, listItemTop(reserve, &slot, written, true));
        for (tail.items, 0..) |item, index| {
            const last = index + 1 == tail.items.len;
            peak = @max(peak, listItemTop(reserve, &slot, self.writtenValue(item, depth) orelse return null, last));
        }
        return saturatingAdd(1, peak);
    }

    /// A keyed field above the reserve: `name = v` (the name a constant register) or `[k] = v`, the key held while the
    /// value is evaluated; a register key or value takes none.
    fn keyedNeed(self: ItemPricing, key_id: ir.ValueId, value_id: ir.ValueId, depth: usize) ?usize {
        const key: Written = if (self.identifierKey(key_id)) .{ .need = 1 } else self.writtenValue(key_id, depth) orelse return null;
        const field_value = self.writtenValue(value_id, depth) orelse return null;
        return @max(autoNeed(key), saturatingAdd(heldRegister(key), autoNeed(field_value)));
    }

    /// A pack as `plannedPackExpression` and `plannedArguments` write it.
    fn tailItems(self: ItemPricing, consumer: ir.InstructionId, pack_id: ir.ValuePackId, depth: usize) ?Tail {
        if (pack_id.index() >= self.program.value_packs.len) return null;
        switch (self.program.value_packs[pack_id.index()].origin) {
            .varargs => |owner| return .{ .single = .{ .need = self.varargNeed(owner, pack_id) orelse return null, .multret = true } },
            .instruction_result => |producer_id| {
                if (producer_id.index() >= self.program.instructions.len) return null;
                const producer = self.program.instructions[producer_id.index()];
                switch (producer.operation) {
                    .pack_values => |items| {
                        if (items.len == 0 or !self.emission.packs.packValuesServesInstruction(producer_id, consumer)) return null;
                        return .{ .items = items };
                    },
                    else => {},
                }
                if (self.emission.packs.storedPackServesInstruction(producer_id, consumer)) {
                    return .{ .single = .{ .need = stored_pack_need, .multret = true } };
                }
                switch (self.emission.packs.role(producer_id)) {
                    .fused_invocation_producer => |target| if (target == consumer) {
                        return .{ .single = .{ .need = self.invocationNeed(producer, depth + 1) orelse return null, .multret = true } };
                    },
                    else => {},
                }
                return null;
            },
        }
    }

    /// `...`, or `select(k, ...)` in the entry function after its fixed parameters and external bindings
    /// (`directVarargPackExpression`).
    fn varargNeed(self: ItemPricing, owner: ir.FunctionId, pack_id: ir.ValuePackId) ?usize {
        if (owner.index() >= self.program.functions.len) return null;
        const function = self.program.functions[owner.index()];
        const vararg_pack = function.vararg_pack orelse return null;
        if (!function.is_variadic or vararg_pack != pack_id) return null;
        if (owner == self.program.entry_function and function.parameters.len + self.program.external_bindings.len != 0) return 3;
        return 1;
    }

    /// A value as `valueUseContext` writes it: the producer it is fused into or inlined as, a fused place read, or a
    /// name: a local register, `__lifter_value_storage[k]` or an upvalue.
    fn writtenValue(self: ItemPricing, value_id: ir.ValueId, depth: usize) ?Written {
        if (depth >= luau_runtime.max_fused_expression_operations) return null;
        const resolved = self.emission.dead.resolveValue(value_id);
        if (resolved.index() >= self.program.values.len) return null;
        if (self.compositions) |compositions| {
            if (compositions.expressions.get(resolved)) |plan| return self.compositionWritten(plan, depth + 1);
            if (compositions.absorbed_values.get(resolved)) |producer_id| {
                if (producer_id.index() >= self.program.instructions.len) return null;
                return self.writtenProducer(self.program.instructions[producer_id.index()], depth + 1);
            }
        } else if (self.scopes.valueDeclaredAtSyntheticSite(resolved)) return null;
        const item = self.program.values[resolved.index()];
        switch (item.origin) {
            .instruction_result => |origin| if (origin.index == 0 and origin.instruction.index() < self.program.instructions.len) {
                const producer = self.program.instructions[origin.instruction.index()];
                if (self.emission.fused_values.contains(producer.id)) return self.writtenProducer(producer, depth + 1);
                if (self.emission.place_reads.contains(producer.id)) return switch (producer.operation) {
                    .place_read => |place_id| self.placeReadWritten(place_id),
                    else => null,
                };
                if (self.emission.dead.isInlined(producer.id)) return self.writtenOperation(producer.operation, depth + 1);
            },
            .capture => |capture_id| return self.capturedWritten(capture_id),
            .parameter, .block_parameter => {},
        }
        if (item.function != self.scopes.function.id) return null;
        if (self.emission.names.valueUsesStorage(resolved)) return .{ .need = 2 };
        if (self.level == .o1 and self.valueIsConstantLocal(resolved)) {
            if (self.constant_reads) |reads| reads.record(resolved.index());
            return .{ .need = 1, .constant = true };
        }
        return .{ .need = 1, .register = true };
    }

    /// A captured value: the entry function's bindings are its own locals; elsewhere an upvalue, written by name, or as
    /// `__lifter_value_storage[k]` of an enclosing function, read through that table's upvalue.
    fn capturedWritten(self: ItemPricing, capture_id: ir.CaptureId) Written {
        const function = self.scopes.function;
        if (function.id == self.program.entry_function) return .{ .need = 1, .register = true };
        const position = for (function.captures, 0..) |candidate, index| {
            if (candidate == capture_id) break index;
        } else return .{ .need = indexed_upvalue_need };
        for (self.program.instructions) |instruction| switch (instruction.operation) {
            .make_closure => |closure| if (closure.function == function.id) {
                if (position >= closure.bindings.len) return .{ .need = indexed_upvalue_need };
                switch (closure.bindings[position]) {
                    .value => |source| if (source.index() >= self.program.values.len or
                        self.emission.names.valueUsesStorage(source) or
                        self.program.values[source.index()].origin == .capture) return .{ .need = indexed_upvalue_need },
                    .place => return .{ .need = indexed_upvalue_need },
                }
            },
            else => {},
        };
        return .{ .need = 1 };
    }

    /// A fused place read as `emitRead` writes it: a local's name or `__lifter_place_storage[k]`; a captured place or a
    /// per-execution cell may be an upvalue, a box `holder[1]` or `rawget(binding, 1)`.
    fn placeReadWritten(self: ItemPricing, place_id: ir.PlaceId) ?Written {
        if (place_id.index() >= self.program.places.len) return null;
        const place = self.program.places[place_id.index()];
        if (place.origin == .capture or place.function != self.scopes.function.id or
            self.scopes.arbitraryPlaceNeedsPerExecutionCell(place_id))
        {
            return .{ .need = indexed_upvalue_need, .relocates = true };
        }
        if (self.emission.names.placeUsesStorage(place_id)) return .{ .need = 2 };
        if (self.level == .o1 and self.scopes.placeMovedLiteralInitializer(place_id) != null) {
            if (self.constant_reads) |reads| reads.record((@as(u64, 1) << 32) | place_id.index());
            return .{ .need = 1, .constant = true };
        }
        return .{ .need = 1, .register = true };
    }

    /// A producer fused into its consumer (`fusedInstructionExpression`): an invocation is written in parentheses
    /// where its adjustment is kept, so it is built as a call; a constructor is built in its target.
    fn writtenProducer(self: ItemPricing, producer: ir.Instruction, depth: usize) ?Written {
        switch (self.emission.packs.role(producer.id)) {
            .fused_adjustment => |invocation_id| {
                if (invocation_id.index() >= self.program.instructions.len) return null;
                const invocation = self.program.instructions[invocation_id.index()];
                return .{ .need = self.invocationNeed(invocation, depth) orelse return null, .relocates = true };
            },
            .ordinary => {},
            else => return null,
        }
        return switch (producer.operation) {
            .call, .namecall, .protected_call, .coroutine_create, .coroutine_resume, .coroutine_yield => .{
                .need = self.invocationNeed(producer, depth) orelse return null,
                .relocates = true,
            },
            .make_table_literal => |inner| .{ .need = self.constructorFrame(producer.id, inner, depth) orelse return null, .table = true },
            else => self.writtenOperation(producer.operation, depth),
        };
    }

    /// An inlined producer, or a fused one written as its expression (`expressionWithContext`).
    fn writtenOperation(self: ItemPricing, operation: ir.Operation, depth: usize) ?Written {
        return switch (operation) {
            .constant => |literal_value| .{ .need = literalNeed(literal_value), .constant = true },
            .function_ref => .{ .need = 1 },
            .make_table => .{ .need = 1, .table = true },
            .copy => |source| self.writtenValue(source, depth),
            .unary => |unary_operation| self.unaryWritten(unary_operation, depth),
            .binary => |binary_operation| self.binaryWritten(binary_operation, depth),
            .table_get => |get| self.tableGetWritten(get, depth),
            .environment_get => |get| self.environmentGetWritten(get, depth),
            .string_interpolate => |interpolation| self.interpolationWritten(interpolation, depth),
            else => null,
        };
    }

    fn unaryWritten(self: ItemPricing, operation: ir.Unary, depth: usize) ?Written {
        const operand = self.writtenValue(operation.operand, depth) orelse return null;
        // bnot(x): the captured bit32.bnot, then its argument
        if (operation.operator == .bit_not) return .{ .need = @max(2, saturatingAdd(1, operand.need)), .relocates = true, .multret = true };
        return .{ .need = saturatingAdd(1, autoNeed(operand)) };
    }

    fn binaryWritten(self: ItemPricing, operation: ir.Binary, depth: usize) ?Written {
        if (luau_runtime.bit32Capability(operation.operator) != null) {
            const call_left = self.writtenValue(operation.left, depth) orelse return null;
            const call_right = self.writtenValue(operation.right, depth) orelse return null;
            // cap(l, r): the captured bit32 function, then its two arguments
            const call_need = @max(3, @max(saturatingAdd(1, call_left.need), saturatingAdd(2, call_right.need)));
            const is_shift = operation.operator == .shift_left or operation.operator == .shift_right;
            if (!is_shift) {
                if (operation.shift_behavior != null) return null;
                return .{ .need = call_need, .relocates = true, .multret = true };
            }
            return switch (operation.shift_behavior orelse return null) {
                .luau_bit32 => .{ .need = call_need, .relocates = true, .multret = true },
                // (if r >= 32 then 0 else cap(l, r)): the test holds r and a register for 32, then either arm
                .zero_saturating => .{
                    .need = @max(call_need, saturatingAdd(1, @max(autoNeed(call_right), saturatingAdd(heldRegister(call_right), 1)))),
                    .relocates = true,
                },
            };
        }
        const left = self.writtenValue(operation.left, depth) orelse return null;
        if (operation.operator == .concat) return self.concatenationWritten(left, operation.right, depth);
        const right = self.writtenValue(operation.right, depth) orelse return null;
        return switch (operation.operator) {
            // luau-compile evaluates the left operand above the target when it is not a comparison or a logical operation
            // and the right operand is a register, and from -O1 also when the right operand is a constant (`ANDK`, `ORK`),
            // which -O0 evaluates into the target: such an operation takes the larger of the two forms. Otherwise each
            // operand is evaluated into the target.
            .logical_and, .logical_or => if (!self.writtenAsTest(operation.left) and right.register)
                .{ .need = saturatingAdd(1, autoNeed(left)) }
            else if (!self.writtenAsTest(operation.left) and right.constant)
                .{
                    .need = @max(@max(left.need, right.need), saturatingAdd(1, autoNeed(left))),
                    .relocates = left.relocates or right.relocates,
                }
            else
                .{ .need = @max(left.need, right.need), .relocates = left.relocates or right.relocates },
            else => .{ .need = saturatingAdd(1, @max(autoNeed(left), saturatingAdd(heldRegister(left), autoNeed(right)))) },
        };
    }

    /// `o_0 .. o_1 .. ... .. o_(n-1)`: luau-compile evaluates the operands along the right spine of concatenations,
    /// written without parentheses, into n consecutive registers above the target; a parenthesized left concatenation is
    /// one operand.
    fn concatenationWritten(self: ItemPricing, first: Written, right_id: ir.ValueId, depth: usize) ?Written {
        var count: usize = 1;
        var above = aboveTop(first);
        var right = right_id;
        var level = depth;
        while (self.inlineConcatenation(right)) |next| {
            level += 1;
            if (level >= luau_runtime.max_fused_expression_operations) return null;
            above = @max(above, aboveTop(self.writtenValue(next.left, level) orelse return null));
            count += 1;
            right = next.right;
        }
        const last = self.writtenValue(right, level) orelse return null;
        count += 1;
        return .{ .need = @max(@max(saturatingAdd(1, count), saturatingAdd(count, last.need)), saturatingAdd(saturatingAdd(1, count), above)) };
    }

    /// The concatenation a value is written as inline, its copies followed: the next link of a right spine.
    fn inlineConcatenation(self: ItemPricing, value_id: ir.ValueId) ?ir.Binary {
        var current = value_id;
        var remaining = luau_runtime.max_fused_expression_operations;
        while (remaining != 0) : (remaining -= 1) {
            const producer = self.inlineProducer(current) orelse return null;
            switch (producer.operation) {
                .binary => |operation| return if (operation.operator == .concat) operation else null,
                .copy => |source| current = source,
                else => return null,
            }
        }
        return null;
    }

    /// Whether a value is written inline as a comparison or a logical operation, the conditions luau-compile tests
    /// without a register for the left operand of `and` and `or`.
    fn writtenAsTest(self: ItemPricing, value_id: ir.ValueId) bool {
        var current = value_id;
        var remaining = luau_runtime.max_fused_expression_operations;
        while (remaining != 0) : (remaining -= 1) {
            if (self.compositions) |compositions| {
                // `c and x` and `c or y` are tests; an if-else is not. An absorbed producer is written inline.
                const resolved = self.emission.dead.resolveValue(current);
                if (compositions.expressions.get(resolved)) |plan| return compositionIsLogical(&self.emission.dead, plan);
                if (compositions.absorbed_values.get(resolved)) |producer_id| {
                    if (producer_id.index() >= self.program.instructions.len) return false;
                    return switch (self.program.instructions[producer_id.index()].operation) {
                        .binary => |operation| operatorIsTest(operation.operator),
                        else => false,
                    };
                }
            }
            const producer = self.inlineProducer(current) orelse return false;
            switch (producer.operation) {
                .binary => |operation| return operatorIsTest(operation.operator),
                .copy => |source| current = source,
                else => return false,
            }
        }
        return false;
    }

    /// The producer a value is written as inline: fused with the ordinary role, or inlined.
    fn inlineProducer(self: ItemPricing, value_id: ir.ValueId) ?ir.Instruction {
        const resolved = self.emission.dead.resolveValue(value_id);
        if (resolved.index() >= self.program.values.len or self.scopes.valueDeclaredAtSyntheticSite(resolved)) return null;
        const origin = switch (self.program.values[resolved.index()].origin) {
            .instruction_result => |origin| origin,
            else => return null,
        };
        if (origin.index != 0 or origin.instruction.index() >= self.program.instructions.len) return null;
        const producer = self.program.instructions[origin.instruction.index()];
        if (self.emission.fused_values.contains(producer.id)) return if (self.emission.packs.role(producer.id) == .ordinary) producer else null;
        if (self.emission.place_reads.contains(producer.id) or !self.emission.dead.isInlined(producer.id)) return null;
        return producer;
    }

    fn tableGetWritten(self: ItemPricing, operation: ir.TableGet, depth: usize) ?Written {
        const object = self.writtenValue(operation.table, depth) orelse return null;
        switch (operation.mode) {
            // rawget(t, k): the captured rawget, then its two arguments
            .raw => {
                const raw_key = self.writtenValue(operation.key, depth) orelse return null;
                return .{ .need = @max(3, @max(saturatingAdd(1, object.need), saturatingAdd(2, raw_key.need))), .relocates = true, .multret = true };
            },
            .semantic => {
                // `object.name`: the object's registers, then the field in the target
                if (self.identifierKey(operation.key)) return .{
                    .need = if (object.register) 1 else object.need,
                    .relocates = !object.register and object.relocates,
                    .object_need = if (object.register) 0 else object.need,
                };
                // `object[key]`: the object held while the key is evaluated
                const key = self.writtenValue(operation.key, depth) orelse return null;
                return .{ .need = saturatingAdd(1, @max(autoNeed(object), saturatingAdd(heldRegister(object), autoNeed(key)))) };
            },
        }
    }

    fn environmentGetWritten(self: ItemPricing, operation: ir.EnvironmentGet, depth: usize) ?Written {
        switch (operation.target) {
            // a global, or getfenv()["name"] for a name that is not an identifier
            .ambient => {
                if (operation.mode == .raw) return null;
                return .{ .need = if (luau_syntax.isIdentifier(operation.name)) 1 else 3 };
            },
            .value => |environment| {
                const object = self.writtenValue(environment, depth) orelse return null;
                if (operation.mode == .raw) return .{ .need = @max(3, saturatingAdd(1, object.need)), .relocates = true, .multret = true };
                if (luau_syntax.isIdentifier(operation.name)) return .{
                    .need = if (object.register) 1 else object.need,
                    .relocates = !object.register and object.relocates,
                    .object_need = if (object.register) 0 else object.need,
                };
                // `object["name"]`: the name constant in a register
                return .{ .need = saturatingAdd(1, @max(autoNeed(object), saturatingAdd(heldRegister(object), 1))) };
            },
        }
    }

    /// fmt("...", v1, ..., vn): the captured string.format, the format string, then the values.
    fn interpolationWritten(self: ItemPricing, operation: ir.StringInterpolation, depth: usize) ?Written {
        if (operation.segments.len != operation.values.len + 1) return null;
        var need = saturatingAdd(2, operation.values.len);
        for (operation.values, 0..) |item, index| {
            const written = self.writtenValue(item, depth) orelse return null;
            need = @max(need, saturatingAdd(saturatingAdd(2, index), written.need));
        }
        return .{ .need = need, .relocates = true, .multret = true };
    }

    /// A call's frame (`plannedInvocation`): slot k holds operand k, the callee first (the runtime capture for pcall,
    /// xpcall and the coroutine library), each built with the register top just above it, then the argument pack.
    fn invocationNeed(self: ItemPricing, producer: ir.Instruction, depth: usize) ?usize {
        var need = operationTemporaryFrameSize(producer.operation) orelse return null;
        switch (producer.operation) {
            .call => |operation| {
                need = @max(need, (self.writtenValue(operation.callee, depth) orelse return null).need);
                need = @max(need, self.argumentsNeed(producer.id, operation.arguments, operation.argument_pack, 1, depth) orelse return null);
            },
            .namecall => |operation| {
                need = @max(need, autoNeed(self.writtenValue(operation.receiver, depth) orelse return null));
                need = @max(need, self.argumentsNeed(producer.id, operation.arguments, operation.argument_pack, 2, depth) orelse return null);
            },
            .protected_call => |operation| {
                need = @max(need, saturatingAdd(1, (self.writtenValue(operation.callee, depth) orelse return null).need));
                var first: usize = 2;
                if (operation.error_handler) |handler| {
                    need = @max(need, saturatingAdd(2, (self.writtenValue(handler, depth) orelse return null).need));
                    first = 3;
                }
                need = @max(need, self.argumentsNeed(producer.id, operation.arguments, operation.argument_pack, first, depth) orelse return null);
            },
            .coroutine_create => |operation| need = @max(need, saturatingAdd(1, (self.writtenValue(operation.callee, depth) orelse return null).need)),
            .coroutine_resume => |operation| {
                need = @max(need, saturatingAdd(1, (self.writtenValue(operation.thread, depth) orelse return null).need));
                need = @max(need, self.argumentsNeed(producer.id, operation.arguments, operation.argument_pack, 2, depth) orelse return null);
            },
            .coroutine_yield => |operation| need = @max(need, self.argumentsNeed(producer.id, operation.arguments, operation.argument_pack, 1, depth) orelse return null),
            else => return null,
        }
        return need;
    }

    /// Arguments from frame slot `first` on, then the argument pack as `plannedArguments` writes it.
    fn argumentsNeed(
        self: ItemPricing,
        consumer: ir.InstructionId,
        arguments: []const ir.ValueId,
        argument_pack: ?ir.ValuePackId,
        first: usize,
        depth: usize,
    ) ?usize {
        var need: usize = 0;
        for (arguments, 0..) |argument, index| {
            const written = self.writtenValue(argument, depth) orelse return null;
            need = @max(need, saturatingAdd(first + index, written.need));
        }
        const pack_id = argument_pack orelse return need;
        const tail = self.tailItems(consumer, pack_id, depth) orelse return null;
        const slot = first + arguments.len;
        if (tail.single) |written| return @max(need, saturatingAdd(slot, written.need));
        for (tail.items, 0..) |item, index| {
            const written = self.writtenValue(item, depth) orelse return null;
            need = @max(need, saturatingAdd(slot + index, written.need));
        }
        return need;
    }

    /// Whether a key is written as a name (`semanticConstructorKey`, `semanticValueIndexSuffix`): a string constant that
    /// is an identifier.
    fn identifierKey(self: ItemPricing, key_id: ir.ValueId) bool {
        const resolved = self.emission.dead.resolveValue(key_id);
        if (resolved.index() >= self.program.values.len) return false;
        const origin = switch (self.program.values[resolved.index()].origin) {
            .instruction_result => |origin| origin,
            else => return false,
        };
        if (origin.index != 0 or origin.instruction.index() >= self.program.instructions.len) return false;
        return switch (self.program.instructions[origin.instruction.index()].operation) {
            .constant => |literal_value| switch (literal_value) {
                .string => |name| luau_syntax.isIdentifier(name),
                else => false,
            },
            else => false,
        };
    }

    /// A local the writer declares with a literal at its instruction (`local v = 5`): no statement assigns a value.
    fn valueIsConstantLocal(self: ItemPricing, value_id: ir.ValueId) bool {
        const origin = switch (self.program.values[value_id.index()].origin) {
            .instruction_result => |origin| origin,
            else => return false,
        };
        if (origin.index != 0 or origin.instruction.index() >= self.program.instructions.len) return false;
        const producer = self.program.instructions[origin.instruction.index()];
        if (producer.operation != .constant or producer.results.len != 1) return false;
        return self.scopes.instructionDeclaresResults(producer.id);
    }

    /// A composition as `branch_expression.emitValue` writes it: `c and x` when the else value is the condition, `c or y`
    /// when the then value is, otherwise `if c then x else y`, which luau-compile builds by testing the condition above
    /// the target and building each arm in the target.
    fn compositionWritten(self: ItemPricing, plan: branch_expression.Plan, depth: usize) ?Written {
        if (depth >= luau_runtime.max_fused_expression_operations) return null;
        const dead = &self.emission.dead;
        const condition = dead.resolveValue(plan.condition);
        if (dead.resolveValue(plan.else_value) == condition) {
            return self.binaryWritten(.{ .operator = .logical_and, .left = plan.condition, .right = plan.then_value }, depth);
        }
        if (dead.resolveValue(plan.then_value) == condition) {
            return self.binaryWritten(.{ .operator = .logical_or, .left = plan.condition, .right = plan.else_value }, depth);
        }
        const tested = self.conditionNeed(plan.condition, depth) orelse return null;
        const then_written = self.writtenValue(plan.then_value, depth) orelse return null;
        const else_written = self.writtenValue(plan.else_value, depth) orelse return null;
        return .{
            .need = @max(saturatingAdd(1, tested), @max(then_written.need, else_written.need)),
            .relocates = then_written.relocates or else_written.relocates or then_written.table or else_written.table,
            .above = @max(tested, @max(aboveTopForLocal(then_written), aboveTopForLocal(else_written))),
        };
    }

    /// The registers luau-compile holds above the register top while it tests a condition (`compileConditionValue`): a
    /// comparison holds its left operand while the right one is evaluated and keeps no result; `not`, `and` and `or` of
    /// conditions test each side in turn; any other value is evaluated into a register.
    fn conditionNeed(self: ItemPricing, value_id: ir.ValueId, depth: usize) ?usize {
        if (depth >= luau_runtime.max_fused_expression_operations) return null;
        const dead = &self.emission.dead;
        const resolved = dead.resolveValue(value_id);
        if (self.compositions) |compositions| {
            if (compositions.expressions.get(resolved)) |plan| {
                if (dead.resolveValue(plan.else_value) == dead.resolveValue(plan.condition)) {
                    return @max(self.conditionNeed(plan.condition, depth + 1) orelse return null, self.conditionNeed(plan.then_value, depth + 1) orelse return null);
                }
                if (dead.resolveValue(plan.then_value) == dead.resolveValue(plan.condition)) {
                    return @max(self.conditionNeed(plan.condition, depth + 1) orelse return null, self.conditionNeed(plan.else_value, depth + 1) orelse return null);
                }
                return autoNeed(self.compositionWritten(plan, depth + 1) orelse return null);
            }
            if (compositions.absorbed_values.get(resolved)) |producer_id| {
                if (producer_id.index() >= self.program.instructions.len) return null;
                return self.operationConditionNeed(self.program.instructions[producer_id.index()], depth + 1);
            }
        }
        if (self.inlineProducer(value_id)) |producer| return self.operationConditionNeed(producer, depth + 1);
        return autoNeed(self.writtenValue(value_id, depth) orelse return null);
    }

    fn operationConditionNeed(self: ItemPricing, producer: ir.Instruction, depth: usize) ?usize {
        switch (producer.operation) {
            .binary => |operation| {
                if (operatorIsComparison(operation.operator)) {
                    const left = self.writtenValue(operation.left, depth) orelse return null;
                    const right = self.writtenValue(operation.right, depth) orelse return null;
                    return @max(autoNeed(left), saturatingAdd(heldRegister(left), autoNeed(right)));
                }
                if (operation.operator == .logical_and or operation.operator == .logical_or) {
                    return @max(self.conditionNeed(operation.left, depth) orelse return null, self.conditionNeed(operation.right, depth) orelse return null);
                }
            },
            .unary => |operation| if (operation.operator == .logical_not) return self.conditionNeed(operation.operand, depth),
            .copy => |source| return self.conditionNeed(source, depth),
            else => {},
        }
        return autoNeed(self.writtenProducer(producer, depth) orelse return null);
    }

    /// A value the writer names directly (`render.valueName`): a local register, or a storage slot.
    fn nameWritten(self: ItemPricing, value_id: ir.ValueId) Written {
        if (self.emission.names.valueUsesStorage(value_id)) return .{ .need = 2 };
        return .{ .need = 1, .register = true };
    }

    fn resultDestination(self: ItemPricing, result: ir.ValueId, declare: bool) Destination {
        if (self.emission.names.valueUsesStorage(result)) return .slot;
        return if (declare) .declared else .local;
    }

    /// A binary operation of two written operands into a target: the left operand held while the right one is
    /// evaluated.
    fn operandsWritten(left: Written, right: Written) Written {
        return .{ .need = saturatingAdd(1, @max(autoNeed(left), saturatingAdd(heldRegister(left), autoNeed(right)))) };
    }

    /// The registers a statement root holds above the register top where it is written, or null for a form the
    /// pricing does not know.
    fn rootNeed(self: ItemPricing, allocator: std.mem.Allocator, root: Root) std.mem.Allocator.Error!?usize {
        return switch (root) {
            .instruction => |statement| try self.instructionNeed(allocator, statement.instruction, statement.declare_results, statement.declare_place),
            .terminator => |block| self.returnNeed(block),
            .condition => |value_id| self.conditionNeed(value_id, 0),
            .discarded_condition => |value_id| destinationNeed(.declared, self.writtenValue(value_id, 0) orelse return null),
            .edge => |edge| self.edgeNeed(edge.target, edge.arguments),
            .composition => |plan| self.compositionStatementNeed(plan),
            .native_header => |protocol| self.nativeHeaderNeed(protocol),
            .normalized_loop => |numeric| self.normalizedLoopNeed(numeric),
        };
    }

    /// A composition written as its own statement at its branch node (`branch_expression.emitAssignment`).
    fn compositionStatementNeed(self: ItemPricing, plan: branch_expression.Plan) ?usize {
        const written = self.compositionWritten(plan, 0) orelse return null;
        const target = self.emission.dead.resolveValue(plan.target);
        const destination: Destination = if (self.emission.names.valueUsesStorage(target))
            .slot
        else if (self.scopes.valueDeclaredAtSyntheticSite(target))
            .declared
        else
            .local;
        return destinationNeed(destination, written);
    }

    /// An instruction written as its own statement (`emitInstruction`).
    fn instructionNeed(
        self: ItemPricing,
        allocator: std.mem.Allocator,
        instruction: ir.Instruction,
        declare_results: bool,
        declare_place: bool,
    ) std.mem.Allocator.Error!?usize {
        const program = self.program;
        const emission = self.emission;
        if (emission.closure_stores.producerForConsumer(instruction.id)) |producer_id| {
            if (producer_id.index() >= program.instructions.len) return null;
            const destination: Destination = switch (instruction.operation) {
                .table_set => |store| .{ .table = .{
                    .object = self.writtenValue(store.table, 0) orelse return null,
                    .key = if (self.identifierKey(store.key)) null else self.writtenValue(store.key, 0) orelse return null,
                } },
                .environment_set => |store| self.environmentDestination(store.target, store.name) orelse return null,
                else => return null,
            };
            return try self.closureNeed(allocator, program.instructions[producer_id.index()], destination);
        }
        const declare_names = declare_results and !resultsUseStorage(emission, instruction.results);
        switch (emission.packs.role(instruction.id)) {
            .ordinary => {},
            .materialized_invocation_producer => |adjustment_id| {
                if (adjustment_id.index() >= program.instructions.len) return null;
                const adjustment = program.instructions[adjustment_id.index()];
                const declare = self.scopes.instructionDeclaresResults(adjustment_id) and !resultsUseStorage(emission, adjustment.results);
                return self.invocationListNeed(adjustment.results, instruction, declare);
            },
            .materialized_adjustment_copy => |primary_id| {
                if (primary_id.index() >= program.instructions.len) return null;
                const primary = program.instructions[primary_id.index()];
                if (primary.results.len < instruction.results.len) return null;
                var items: [max_list_items]ListItem = undefined;
                if (instruction.results.len > items.len) return null;
                for (primary.results[0..instruction.results.len], 0..) |value_id, index| {
                    items[index] = .{ .written = self.nameWritten(value_id), .value = value_id };
                }
                return self.destinationListNeed(instruction.results, items[0..instruction.results.len], declare_names);
            },
            .stored_invocation_producer => return saturatingAdd(1, self.invocationNeed(instruction, 0) orelse return null),
            .stored_adjustment => {
                var items: [max_list_items]ListItem = undefined;
                if (instruction.results.len > items.len) return null;
                // rawget(pack, i): the captured rawget, the pack's local and the index literal.
                for (items[0..instruction.results.len]) |*item| item.* = .{ .written = .{ .need = 3, .relocates = true, .multret = true } };
                return self.destinationListNeed(instruction.results, items[0..instruction.results.len], declare_names);
            },
            .fused_adjustment => |producer_id| {
                if (producer_id.index() >= program.instructions.len) return null;
                return self.invocationListNeed(instruction.results, program.instructions[producer_id.index()], declare_names);
            },
            .direct_vararg_adjustment => {
                const pack_id = switch (instruction.operation) {
                    .adjust_pack => |value| value,
                    else => return null,
                };
                if (pack_id.index() >= program.value_packs.len) return null;
                const owner = switch (program.value_packs[pack_id.index()].origin) {
                    .varargs => |owner| owner,
                    .instruction_result => return null,
                };
                const item: ListItem = .{ .written = .{ .need = self.varargNeed(owner, pack_id) orelse return null, .multret = true } };
                return self.destinationListNeed(instruction.results, &.{item}, declare_names);
            },
            .fused_pack_values_adjustment => |producer_id| {
                if (producer_id.index() >= program.instructions.len) return null;
                const packed_values = switch (program.instructions[producer_id.index()].operation) {
                    .pack_values => |items| items,
                    else => return null,
                };
                var items: [max_list_items]ListItem = undefined;
                if (packed_values.len > items.len or packed_values.len == 0) return null;
                for (packed_values, 0..) |value_id, index| {
                    items[index] = .{ .written = self.writtenValue(value_id, 0) orelse return null, .value = value_id };
                }
                return self.destinationListNeed(instruction.results, items[0..packed_values.len], declare_names);
            },
            else => return 0,
        }
        switch (instruction.operation) {
            .generic_for_next => |operation| return self.genericTransitionNeed(instruction, operation),
            .numeric_for_next => |operation| return switch (operation.mode) {
                .semantic_normalized => self.semanticTransitionNeed(instruction, operation, declare_names),
                .luau_numeric => self.numericGuardNeed(instruction, operation),
            },
            .call_repeated_table_get => |operation| {
                var frame = operationTemporaryFrameSize(instruction.operation) orelse return null;
                frame = @max(frame, saturatingAdd(1, (self.writtenValue(operation.callee, 0) orelse return null).need));
                var slot: usize = 2;
                for (operation.prefix_arguments) |argument| {
                    frame = @max(frame, saturatingAdd(slot, (self.writtenValue(argument, 0) orelse return null).need));
                    slot += 1;
                }
                for ([_]ir.ValueId{ operation.table, operation.key, operation.from, operation.to, operation.step }) |argument| {
                    frame = @max(frame, saturatingAdd(slot, (self.writtenValue(argument, 0) orelse return null).need));
                    slot += 1;
                }
                if (instruction.results.len == 0) return frame;
                const call: ListItem = .{ .written = .{ .need = frame, .relocates = true, .multret = true } };
                return self.destinationListNeed(instruction.results, &.{call}, declare_names);
            },
            .call, .namecall, .protected_call, .coroutine_create, .coroutine_resume, .coroutine_yield => {
                return self.invocationListNeed(instruction.results, instruction, declare_names);
            },
            .make_closure => {
                if (instruction.results.len != 1) return null;
                return try self.closureNeed(allocator, instruction, self.resultDestination(instruction.results[0], declare_names));
            },
            .place_read => |place_id| {
                if (instruction.results.len != 1) return null;
                return destinationNeed(self.resultDestination(instruction.results[0], declare_names), self.placeReadWritten(place_id) orelse return null);
            },
            .place_write => |write| return try self.placeWriteNeed(allocator, instruction, write, declare_place),
            .make_table_literal => |constructor| {
                if (instruction.results.len != 1) return null;
                const frame = self.constructorFrame(instruction.id, constructor, 0) orelse return null;
                return destinationNeed(self.resultDestination(instruction.results[0], declare_names), .{ .need = frame, .table = true });
            },
            .table_set_pack => |operation| {
                var frame = emittedOperationTemporaryFrameSize(program, emission, self.scopes, instruction) orelse return null;
                frame = @max(frame, saturatingAdd(1, (self.writtenValue(operation.table, 0) orelse return null).need));
                const tail = self.tailItems(instruction.id, operation.pack, 0) orelse return null;
                if (tail.single) |written| frame = @max(frame, saturatingAdd(3, written.need));
                for (tail.items, 0..) |item, index| {
                    frame = @max(frame, saturatingAdd(3 + index, (self.writtenValue(item, 0) orelse return null).need));
                }
                return frame;
            },
            .table_set => |store| {
                if (compound_update.matchTable(program, &emission.dead, &emission.fused_values, instruction)) |update| {
                    return self.compoundMemoryNeed(update);
                }
                return self.tableStoreNeed(store);
            },
            .environment_set => |store| {
                if (compound_update.matchEnvironment(program, &emission.dead, &emission.fused_values, instruction)) |update| {
                    return self.compoundMemoryNeed(update);
                }
                return self.environmentStoreNeed(store);
            },
            else => {},
        }
        if (instruction.results.len == 0) return 0;
        const written = self.writtenOperation(instruction.operation, 0) orelse return null;
        if (instruction.results.len == 1) return destinationNeed(self.resultDestination(instruction.results[0], declare_names), written);
        return self.destinationListNeed(instruction.results, &.{.{ .written = written }}, declare_names);
    }

    /// `[local] r1, ..., rn = f(...)`, or the call statement `f(...)` when there is no result.
    fn invocationListNeed(self: ItemPricing, results: []const ir.ValueId, producer: ir.Instruction, declare: bool) ?usize {
        const frame = self.invocationNeed(producer, 0) orelse return null;
        if (results.len == 0) return frame;
        return self.destinationListNeed(results, &.{.{ .written = .{ .need = frame, .relocates = true, .multret = true } }}, declare);
    }

    /// `[local] r1, ..., rn = v1, ..., vm`: one result is a single destination; a declared list is `compileStatLocal`;
    /// any other list is `compileStatAssign`.
    fn destinationListNeed(self: ItemPricing, results: []const ir.ValueId, items: []const ListItem, declare: bool) ?usize {
        if (results.len == 0) return null;
        if (results.len == 1 and items.len == 1) return destinationNeed(self.resultDestination(results[0], declare), items[0].written);
        if (declare) return declaredListNeed(results.len, items);
        var destinations: [max_list_items]ListDestination = undefined;
        if (results.len > destinations.len) return null;
        for (results, 0..) |result, index| {
            destinations[index] = .{ .slot = self.emission.names.valueUsesStorage(result), .value = result };
        }
        const listed = destinations[0..results.len];
        return assignListNeed(listed, items, listConflictCount(listed, items, self));
    }

    /// The copies of an edge into its target's parameters (`emitEdgeParameters`): `p1, ..., pn = a1, ..., an` over the
    /// parameters that are not value aliases.
    fn edgeNeed(self: ItemPricing, target: ir.Block, arguments: []const ir.ValueId) ?usize {
        if (target.parameters.len != arguments.len) return null;
        var destinations: [max_list_items]ListDestination = undefined;
        var items: [max_list_items]ListItem = undefined;
        var count: usize = 0;
        for (target.parameters, arguments) |parameter, argument| {
            if (self.emission.dead.isValueAlias(parameter)) continue;
            if (count == destinations.len) return null;
            destinations[count] = .{ .slot = self.emission.names.valueUsesStorage(parameter), .value = parameter };
            items[count] = .{ .written = self.writtenValue(argument, 0) orelse return null, .value = argument };
            count += 1;
        }
        if (count == 0) return 0;
        return assignListNeed(destinations[0..count], items[0..count], listConflictCount(destinations[0..count], items[0..count], self));
    }

    /// Whether a list item's written expression reads the local a destination names (`listConflictCount`).
    fn itemReadsDestination(self: ItemPricing, item: ListItem, destination: ir.ValueId) bool {
        return self.itemReads(item, self.emission.dead.resolveValue(destination));
    }

    /// Whether a list item's written expression reads `target` by name.
    fn itemReads(self: ItemPricing, item: ListItem, target: ir.ValueId) bool {
        const value_id = item.value orelse return false;
        var remaining: usize = luau_runtime.max_fused_expression_operations;
        return self.valueReads(value_id, target, &remaining);
    }

    fn valueReads(self: ItemPricing, value_id: ir.ValueId, target: ir.ValueId, remaining: *usize) bool {
        if (remaining.* == 0) return true;
        remaining.* -= 1;
        const resolved = self.emission.dead.resolveValue(value_id);
        if (resolved == target) return true;
        if (resolved.index() >= self.program.values.len) return true;
        if (self.compositions) |compositions| {
            if (compositions.expressions.get(resolved)) |plan| {
                return self.valueReads(plan.condition, target, remaining) or
                    self.valueReads(plan.then_value, target, remaining) or
                    self.valueReads(plan.else_value, target, remaining);
            }
            if (compositions.absorbed_values.get(resolved)) |producer_id| {
                if (producer_id.index() >= self.program.instructions.len) return true;
                return self.operationReads(self.program.instructions[producer_id.index()].operation, target, remaining);
            }
        }
        const origin = switch (self.program.values[resolved.index()].origin) {
            .instruction_result => |origin| origin,
            else => return false,
        };
        if (origin.index != 0 or origin.instruction.index() >= self.program.instructions.len) return false;
        const producer = self.program.instructions[origin.instruction.index()];
        if (self.emission.place_reads.contains(producer.id)) return false;
        if (self.emission.fused_values.contains(producer.id) or self.emission.dead.isInlined(producer.id)) {
            switch (self.emission.packs.role(producer.id)) {
                .fused_adjustment => |invocation_id| {
                    if (invocation_id.index() >= self.program.instructions.len) return true;
                    return self.operationReads(self.program.instructions[invocation_id.index()].operation, target, remaining);
                },
                else => return self.operationReads(producer.operation, target, remaining),
            }
        }
        return false;
    }

    fn operationReads(self: ItemPricing, operation: ir.Operation, target: ir.ValueId, remaining: *usize) bool {
        const Visitor = struct {
            pricing: ItemPricing,
            target: ir.ValueId,
            remaining: *usize,
            found: *bool,

            pub fn value(visitor: @This(), value_id: ir.ValueId) void {
                if (!visitor.found.* and visitor.pricing.valueReads(value_id, visitor.target, visitor.remaining)) visitor.found.* = true;
            }
            pub fn pack(_: @This(), _: ir.ValuePackId) void {}
            pub fn place(_: @This(), _: ir.PlaceId) void {}
        };
        var found = false;
        runtime_uses.visitOperationUses(operation, Visitor{ .pricing = self, .target = target, .remaining = remaining, .found = &found });
        return found;
    }

    /// A place write (`emitPlaceWriteInstruction`): its value, the producer fused into it, a closure created into it, or
    /// a compound update of a place read in it.
    fn placeWriteNeed(
        self: ItemPricing,
        allocator: std.mem.Allocator,
        instruction: ir.Instruction,
        write: ir.PlaceWrite,
        declare_place: bool,
    ) std.mem.Allocator.Error!?usize {
        const program = self.program;
        const emission = self.emission;
        const producer_id = emission.place_writes.producerForWrite(instruction.id) orelse {
            const destination = self.placeDestination(write.place, instruction.id, declare_place) orelse return null;
            return destinationNeed(destination, self.writtenValue(write.value, 0) orelse return null);
        };
        if (producer_id.index() >= program.instructions.len) return null;
        const producer = program.instructions[producer_id.index()];
        if (producer.operation == .make_closure) {
            const destination = self.placeDestination(write.place, instruction.id, declare_place) orelse return null;
            return try self.closureNeed(allocator, producer, destination);
        }
        if (!declare_place) {
            if (compound_update.matchPlace(program, &emission.dead, &emission.place_writes, &emission.place_reads, producer, instruction)) |update| {
                return self.compoundPlaceNeed(write.place, update);
            }
        }
        const written: Written = switch (emission.packs.role(producer.id)) {
            .fused_adjustment => |invocation_id| blk: {
                if (invocation_id.index() >= program.instructions.len) return null;
                break :blk .{ .need = self.invocationNeed(program.instructions[invocation_id.index()], 0) orelse return null, .relocates = true };
            },
            .ordinary => switch (producer.operation) {
                .call, .namecall, .protected_call, .coroutine_create, .coroutine_resume, .coroutine_yield => .{
                    .need = self.invocationNeed(producer, 0) orelse return null,
                    .relocates = true,
                },
                .make_table_literal => |constructor| .{ .need = self.constructorFrame(producer.id, constructor, 0) orelse return null, .table = true },
                else => self.writtenOperation(producer.operation, 0) orelse return null,
            },
            else => return null,
        };
        const destination = self.placeDestination(write.place, instruction.id, declare_place) orelse return null;
        return destinationNeed(destination, written);
    }

    /// The destination a place write names: this function's local or its storage slot, a box (`holder = { v }` at the
    /// box's allocating write, `holder[1] = v` elsewhere), or a captured place.
    fn placeDestination(self: ItemPricing, place_id: ir.PlaceId, write: ir.InstructionId, declare_place: bool) ?Destination {
        if (place_id.index() >= self.program.places.len) return null;
        const place = self.program.places[place_id.index()];
        if (place.origin == .capture or place.function != self.scopes.function.id) return self.capturedPlaceDestination(place_id);
        if (self.emission.names.placeUsesStorage(place_id)) return .slot;
        if (self.scopes.arbitraryPlaceNeedsPerExecutionCell(place_id)) {
            if (place.origin == .instruction and place.origin.instruction == write) return .local;
            return .slot;
        }
        return if (declare_place) .declared else .local;
    }

    /// A captured place written through its upvalue: the enclosing function's local by name, or a slot of its storage
    /// table or of a box it may hold for a per-execution cell; a place the entry chunk binds outside it through `rawset`.
    fn capturedPlaceDestination(self: ItemPricing, place_id: ir.PlaceId) Destination {
        var current = place_id;
        var remaining = self.program.functions.len + 1;
        while (remaining != 0) : (remaining -= 1) {
            if (current.index() >= self.program.places.len) return .external;
            const place = self.program.places[current.index()];
            switch (place.origin) {
                .capture => |capture_id| current = self.capturedPlaceSource(place.function, capture_id) orelse return .external,
                .local => return if (self.emission.names.placeUsesStorage(current)) .upvalue_slot else .upvalue,
                .instruction => return .upvalue_slot,
            }
        }
        return .external;
    }

    /// The enclosing function's place a closure of `function_id` binds to its capture `capture_id`.
    fn capturedPlaceSource(self: ItemPricing, function_id: ir.FunctionId, capture_id: ir.CaptureId) ?ir.PlaceId {
        if (function_id.index() >= self.program.functions.len) return null;
        const function = self.program.functions[function_id.index()];
        const position = for (function.captures, 0..) |candidate, index| {
            if (candidate == capture_id) break index;
        } else return null;
        for (self.program.instructions) |instruction| switch (instruction.operation) {
            .make_closure => |closure| if (closure.function == function_id) {
                if (position >= closure.bindings.len) return null;
                return switch (closure.bindings[position]) {
                    .place => |source| source,
                    .value => null,
                };
            },
            else => {},
        };
        return null;
    }

    /// `env.name = v`, `env["name"] = v`, `G = v` or `getfenv()["name"] = v` as a destination.
    fn environmentDestination(self: ItemPricing, target: ir.EnvironmentTarget, name: []const u8) ?Destination {
        switch (target) {
            .ambient => {
                if (luau_syntax.isIdentifier(name)) return .global;
                return .{ .table = .{ .object = .{ .need = 1, .relocates = true }, .key = .{ .need = 1 } } };
            },
            .value => |environment| {
                const object = self.writtenValue(environment, 0) orelse return null;
                return .{ .table = .{ .object = object, .key = if (luau_syntax.isIdentifier(name)) null else .{ .need = 1 } } };
            },
        }
    }

    /// A table store (`render.statement`): `t[k] = v`, `t.name = v`, or `rawset(t, k, v)`.
    fn tableStoreNeed(self: ItemPricing, store: ir.TableSet) ?usize {
        const value = self.writtenValue(store.value, 0) orelse return null;
        switch (store.mode) {
            .semantic => return destinationNeed(.{ .table = .{
                .object = self.writtenValue(store.table, 0) orelse return null,
                .key = if (self.identifierKey(store.key)) null else self.writtenValue(store.key, 0) orelse return null,
            } }, value),
            .raw => {
                const object = self.writtenValue(store.table, 0) orelse return null;
                const key = self.writtenValue(store.key, 0) orelse return null;
                return @max(@max(4, saturatingAdd(1, object.need)), @max(saturatingAdd(2, key.need), saturatingAdd(3, value.need)));
            },
        }
    }

    /// An environment store (`render.statement`): `G = v`, `getfenv()["name"] = v`, `env.name = v` or
    /// `rawset(env, "name", v)`.
    fn environmentStoreNeed(self: ItemPricing, store: ir.EnvironmentSet) ?usize {
        const value = self.writtenValue(store.value, 0) orelse return null;
        switch (store.mode) {
            .semantic => return destinationNeed(self.environmentDestination(store.target, store.name) orelse return null, value),
            .raw => {
                const environment = switch (store.target) {
                    .ambient => return null,
                    .value => |environment| environment,
                };
                const object = self.writtenValue(environment, 0) orelse return null;
                return @max(@max(4, saturatingAdd(1, object.need)), saturatingAdd(3, value.need));
            },
        }
    }

    /// `t[k] op= r`, `t.name op= r` or `G op= r` (`emitCompoundMemoryUpdate`): the address, then the loaded target and
    /// the right operand above it; `..=` loads the target and every operand of the right concatenation in a row.
    fn compoundMemoryNeed(self: ItemPricing, update: compound_update.MemoryUpdate) ?usize {
        const address: Address = switch (update.address) {
            .table => |table| blk: {
                const object = self.writtenValue(table.table, 0) orelse return null;
                if (self.identifierKey(table.key)) break :blk .{ .peak = autoNeed(object), .held = heldRegister(object) };
                const key = self.writtenValue(table.key, 0) orelse return null;
                break :blk .{
                    .peak = @max(autoNeed(object), saturatingAdd(heldRegister(object), autoNeed(key))),
                    .held = saturatingAdd(heldRegister(object), heldRegister(key)),
                };
            },
            .environment => |environment| switch (environment.target) {
                .ambient => if (luau_syntax.isIdentifier(environment.name)) Address{} else Address{ .peak = 2, .held = 2 },
                .value => |object_id| blk: {
                    const object = self.writtenValue(object_id, 0) orelse return null;
                    if (luau_syntax.isIdentifier(environment.name)) break :blk .{ .peak = autoNeed(object), .held = heldRegister(object) };
                    break :blk .{
                        .peak = @max(autoNeed(object), saturatingAdd(heldRegister(object), 1)),
                        .held = saturatingAdd(heldRegister(object), 1),
                    };
                },
            },
        };
        return self.compoundAddressNeed(address, update.operator, update.right);
    }

    fn compoundAddressNeed(self: ItemPricing, address: Address, operator: ir.BinaryOperator, right: ir.ValueId) ?usize {
        if (operator == .concat) {
            const concatenation = self.concatenationWritten(.{ .need = 1 }, right, 0) orelse return null;
            return @max(address.peak, saturatingAdd(address.held, concatenation.need));
        }
        const operand = self.writtenValue(right, 0) orelse return null;
        return @max(address.peak, saturatingAdd(saturatingAdd(address.held, 1), autoNeed(operand)));
    }

    /// `p op= r` (`emitPlaceWriteInstruction`'s compound form): into a local in place, otherwise through the slot,
    /// upvalue or box the place's name denotes.
    fn compoundPlaceNeed(self: ItemPricing, place_id: ir.PlaceId, update: compound_update.PlaceUpdate) ?usize {
        const destination = self.placeDestination(place_id, ir.InstructionId.fromIndex(std.math.maxInt(u32)), false) orelse return null;
        const address: Address = switch (destination) {
            .local, .declared => {
                if (update.operator == .concat) {
                    const concatenation = self.concatenationWritten(.{ .need = 1, .register = true }, update.right, 0) orelse return null;
                    return concatenation.need -| 1;
                }
                return autoNeed(self.writtenValue(update.right, 0) orelse return null);
            },
            .slot => .{ .peak = 1, .held = 1 },
            .upvalue => .{},
            .upvalue_slot => .{ .peak = 2, .held = 2 },
            else => return null,
        };
        return self.compoundAddressNeed(address, update.operator, update.right);
    }

    /// A closure creation (`emitClosure`): with snapshots, a `do` block that declares each value-binding and box
    /// snapshot local in turn and then stores the closure; without, the store alone.
    fn closureNeed(self: ItemPricing, allocator: std.mem.Allocator, producer: ir.Instruction, destination: Destination) std.mem.Allocator.Error!?usize {
        const closure = switch (producer.operation) {
            .make_closure => |value| value,
            else => return null,
        };
        if (closure.function.index() >= self.program.functions.len) return null;
        var closure_plan = lexical.ClosurePlan.initWithStableValues(
            allocator,
            self.program,
            self.program.functions[closure.function.index()],
            closure,
            &.{},
            StableCaptureValues{ .scopes = self.scopes },
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.InvalidClosureBinding => return null,
        };
        defer closure_plan.deinit();
        var frame: usize = 0;
        var snapshots: usize = 0;
        for (closure_plan.value_bindings) |binding| {
            const written = self.writtenValue(binding.source, 0) orelse return null;
            frame = @max(frame, saturatingAdd(snapshots, written.need));
            snapshots += 1;
        }
        for (closure_plan.snapshot_bindings) |binding| {
            const need: usize = if (self.emission.names.placeUsesStorage(binding.source)) 2 else 1;
            frame = @max(frame, saturatingAdd(snapshots, need));
            snapshots += 1;
        }
        const store: Destination = if (snapshots != 0 and destination == .declared) .local else destination;
        return @max(frame, saturatingAdd(snapshots, destinationNeed(store, .{ .need = 1 })));
    }

    /// A return or another terminator written as a statement (`call_emission.terminator`): the values from the first
    /// return slot up, a pack at the slot after them.
    fn returnNeed(self: ItemPricing, block: ir.Block) ?usize {
        const program = self.program;
        switch (self.emission.packs.terminatorRole(block.id)) {
            .fused_invocation_return => |producer_id| {
                if (producer_id.index() >= program.instructions.len) return null;
                const prefix: []const ir.ValueId = switch (block.terminator) {
                    .return_expanded => |expanded| expanded.values,
                    else => &.{},
                };
                const call = self.invocationNeed(program.instructions[producer_id.index()], 0) orelse return null;
                return @max(self.returnValuesNeed(prefix) orelse return null, saturatingAdd(prefix.len, call));
            },
            .fused_pack_values_return => |producer_id| {
                if (producer_id.index() >= program.instructions.len) return null;
                const packed_values = switch (program.instructions[producer_id.index()].operation) {
                    .pack_values => |items| items,
                    else => return null,
                };
                switch (block.terminator) {
                    .return_pack => {
                        if (self.returnIsContiguous(packed_values)) return 0;
                        return self.returnValuesNeed(packed_values);
                    },
                    .return_expanded => |expanded| {
                        var frame = self.returnValuesNeed(expanded.values) orelse return null;
                        for (packed_values, expanded.values.len..) |value_id, slot| {
                            frame = @max(frame, saturatingAdd(slot, (self.writtenValue(value_id, 0) orelse return null).need));
                        }
                        return frame;
                    },
                    else => return null,
                }
            },
            .stored_pack_return => {
                const prefix: []const ir.ValueId = switch (block.terminator) {
                    .return_expanded => |expanded| expanded.values,
                    else => &.{},
                };
                return @max(self.returnValuesNeed(prefix) orelse return null, saturatingAdd(prefix.len, stored_pack_need));
            },
            .ordinary => switch (block.terminator) {
                .return_values => |values| {
                    if (self.returnIsContiguous(values)) return 0;
                    return self.returnValuesNeed(values);
                },
                // `return ...` or `return select(k, ...)`: the tail at the slot after the values.
                .return_pack => |pack_id| return self.packNeed(pack_id),
                .return_expanded => |expanded| return @max(
                    self.returnValuesNeed(expanded.values) orelse return null,
                    saturatingAdd(expanded.values.len, self.packNeed(expanded.pack) orelse return null),
                ),
                .throw_error => |throw_error| {
                    const value = self.writtenValue(throw_error.value, 0) orelse return null;
                    const level: usize = if (throw_error.dynamic_level) |level| (self.writtenValue(level, 0) orelse return null).need else 1;
                    return @max(@max(3, saturatingAdd(1, value.need)), saturatingAdd(2, level));
                },
                .unreachable_block => return 2,
                .jump, .branch => return 0,
            },
        }
    }

    /// Return values at consecutive slots from the first: each value is built at its slot.
    fn returnValuesNeed(self: ItemPricing, values: []const ir.ValueId) ?usize {
        var frame: usize = values.len;
        for (values, 0..) |value_id, slot| {
            frame = @max(frame, saturatingAdd(slot, (self.writtenValue(value_id, 0) orelse return null).need));
        }
        return frame;
    }

    /// A run of consecutive locals is returned in place, unless at -O1 one of them is a literal there.
    fn returnIsContiguous(self: ItemPricing, values: []const ir.ValueId) bool {
        if (!valuesAreContiguousLexicalRun(self.program, self.scopes, values)) return false;
        if (self.level == .o0) return true;
        for (values) |value_id| {
            const resolved = self.emission.dead.resolveValue(value_id);
            if (resolved.index() < self.program.values.len and self.valueIsConstantLocal(resolved)) return false;
        }
        return true;
    }

    /// `...`, `select(k, ...)` or a stored pack's expansion as the last item of a list.
    fn packNeed(self: ItemPricing, pack_id: ir.ValuePackId) ?usize {
        if (pack_id.index() >= self.program.value_packs.len) return null;
        return switch (self.program.value_packs[pack_id.index()].origin) {
            .varargs => |owner| self.varargNeed(owner, pack_id),
            .instruction_result => stored_pack_need,
        };
    }

    /// A numeric `for` header (`for i = a, b, c do`) while it evaluates its values: its three registers (the limit, the
    /// step and the index); the start is built in the index register, the top one, and the limit and the step in theirs
    /// with what they need above the three.
    fn numericForFrame(self: ItemPricing, start: ir.ValueId, limit: ir.ValueId, step: ir.ValueId) ?usize {
        var frame = @max(3, saturatingAdd(2, (self.writtenValue(start, 0) orelse return null).need));
        for ([_]ir.ValueId{ limit, step }) |value_id| {
            frame = @max(frame, saturatingAdd(3, aboveTopForTemporary(self.writtenValue(value_id, 0) orelse return null)));
        }
        return frame;
    }

    /// A generic `for` header (`for v1, ..., vn in e1, ..., em do`) while it evaluates its initializers: the generator,
    /// state and control registers, each initializer built in its slot with what it needs above them, or one call filling
    /// them. The loop variables come after, where the body holds them with these registers.
    fn genericForFrame(self: ItemPricing, initializers: []const ir.ValueId, fused_producer: ?ir.Instruction) ?usize {
        var frame: usize = 3;
        if (fused_producer) |producer| return @max(frame, self.invocationNeed(producer, 0) orelse return null);
        for (initializers) |value_id| {
            frame = @max(frame, saturatingAdd(3, aboveTopForTemporary(self.writtenValue(value_id, 0) orelse return null)));
        }
        return frame;
    }

    /// A semantic-normalized numeric transition written as statements (`emitSemanticNormalizedTransition`).
    fn semanticTransitionNeed(self: ItemPricing, instruction: ir.Instruction, operation: ir.NumericForNext, declare: bool) ?usize {
        _ = declare;
        if (instruction.results.len != 4) return null;
        const has_value = instruction.results[0];
        const limit = instruction.results[1];
        const step = instruction.results[2];
        const control = instruction.results[3];
        var frame = destinationNeed(self.resultDestination(limit, false), self.writtenValue(operation.limit, 0) orelse return null);
        frame = @max(frame, destinationNeed(self.resultDestination(step, false), self.writtenValue(operation.step, 0) orelse return null));
        const advanced = operandsWritten(self.writtenValue(operation.control, 0) orelse return null, self.nameWritten(step));
        frame = @max(frame, destinationNeed(self.resultDestination(control, false), advanced));
        // `if step <= 0 then`: the step held while the literal is loaded.
        const step_name = self.nameWritten(step);
        frame = @max(frame, @max(autoNeed(step_name), saturatingAdd(heldRegister(step_name), 1)));
        const compared = operandsWritten(self.nameWritten(control), self.nameWritten(limit));
        return @max(frame, destinationNeed(self.resultDestination(has_value, false), compared));
    }

    /// A `luau_numeric` transition written as statements (`emitLuauNumericTransition`): the one-shot guard `for`, the
    /// coerced copies and the bound test.
    fn numericGuardNeed(self: ItemPricing, instruction: ir.Instruction, operation: ir.NumericForNext) ?usize {
        if (instruction.results.len != 4) return null;
        const has_value = instruction.results[0];
        const limit = instruction.results[1];
        const step = instruction.results[2];
        const control = instruction.results[3];
        const one: Written = .{ .need = 1, .constant = true };
        var frame = self.conditionNeed(operation.initial, 0) orelse return null;
        frame = @max(frame, self.numericForFrame(operation.control, operation.limit, operation.step) orelse return null);
        for ([_]ir.ValueId{ limit, step, control }, [_]ir.ValueId{ operation.limit, operation.step, operation.control }) |result, source| {
            const operand = self.writtenValue(source, 0) orelse return null;
            frame = @max(frame, destinationNeed(self.resultDestination(result, false), operandsWritten(operand, one)));
            frame = @max(frame, destinationNeed(self.resultDestination(result, false), operand));
        }
        const advanced = operandsWritten(self.writtenValue(operation.control, 0) orelse return null, self.nameWritten(step));
        frame = @max(frame, destinationNeed(self.resultDestination(control, false), advanced));
        const step_name = self.nameWritten(step);
        frame = @max(frame, @max(autoNeed(step_name), saturatingAdd(heldRegister(step_name), 1)));
        const compared = operandsWritten(self.nameWritten(control), self.nameWritten(limit));
        frame = @max(frame, destinationNeed(self.resultDestination(has_value, false), compared));
        // The flat layout's term for the transition.
        return @max(frame, 3);
    }

    /// A generic transition written as statements (`emitGenericForNextTransition`): a `do` block with the iterator,
    /// state and control locals, the `__iter` preparation under its `if`, the iterator call into the loop values and
    /// the has-value test; at least the flat layout's term for it, `3 + max(5, targets)`, a storage target counting 2.
    fn genericTransitionNeed(self: ItemPricing, instruction: ir.Instruction, operation: ir.GenericForNext) ?usize {
        const variables = @as(usize, operation.variable_count);
        if (variables == 0 or instruction.results.len != variables + 3) return null;
        var targets: usize = 0;
        var keys: usize = 0;
        for (instruction.results[3..]) |result| {
            const stored = self.emission.names.valueUsesStorage(result);
            targets = saturatingAdd(targets, if (stored) 2 else 1);
            keys += @intFromBool(stored);
        }
        var frame = saturatingAdd(3, @max(5, targets));
        frame = @max(frame, (self.writtenValue(operation.iterator, 0) orelse return null).need);
        frame = @max(frame, saturatingAdd(1, (self.writtenValue(operation.state, 0) orelse return null).need));
        frame = @max(frame, saturatingAdd(2, (self.writtenValue(operation.control, 0) orelse return null).need));
        frame = @max(frame, saturatingAdd(3, self.conditionNeed(operation.initial, 0) orelse return null));
        frame = @max(frame, saturatingAdd(saturatingAdd(3, keys), @max(variables, 3)));
        for (instruction.results[0..3]) |result| {
            frame = @max(frame, saturatingAdd(3, destinationNeed(self.resultDestination(result, false), .{ .need = 2 })));
        }
        return frame;
    }

    /// The node-sum bound of a root the pricing cannot price: every open frame of luau-compile's nested evaluation
    /// belongs to one node of the nesting chain and holds at most that node's own registers, so the sum over the nodes,
    /// with two registers for each destination, bounds the peak.
    fn fallbackNeed(self: ItemPricing, root: Root) usize {
        var budget: usize = fallback_node_budget;
        var sum: usize = 0;
        switch (root) {
            .instruction => |statement| {
                sum = saturatingAdd(2, saturatingAdd(statement.instruction.results.len, statement.instruction.results.len));
                sum = saturatingAdd(sum, self.operationNodeSum(statement.instruction.operation, &budget));
                if (self.emission.closure_stores.producerForConsumer(statement.instruction.id)) |producer_id| {
                    if (producer_id.index() < self.program.instructions.len) {
                        sum = saturatingAdd(sum, self.operationNodeSum(self.program.instructions[producer_id.index()].operation, &budget));
                    }
                }
                if (self.emission.place_writes.producerForWrite(statement.instruction.id)) |producer_id| {
                    if (producer_id.index() < self.program.instructions.len) {
                        sum = saturatingAdd(sum, self.operationNodeSum(self.program.instructions[producer_id.index()].operation, &budget));
                    }
                }
            },
            .terminator => |block| {
                const Visitor = struct {
                    pricing: ItemPricing,
                    budget: *usize,
                    sum: *usize,

                    pub fn value(visitor: @This(), value_id: ir.ValueId) void {
                        visitor.sum.* = saturatingAdd(visitor.sum.*, saturatingAdd(1, visitor.pricing.valueNodeSum(value_id, visitor.budget)));
                    }
                    pub fn pack(visitor: @This(), _: ir.ValuePackId) void {
                        visitor.sum.* = saturatingAdd(visitor.sum.*, stored_pack_need);
                    }
                    pub fn place(_: @This(), _: ir.PlaceId) void {}
                };
                sum = 3;
                runtime_uses.visitTerminatorUses(block.terminator, Visitor{ .pricing = self, .budget = &budget, .sum = &sum });
                switch (self.emission.packs.terminatorRole(block.id)) {
                    .ordinary => {},
                    .fused_invocation_return, .fused_pack_values_return, .stored_pack_return => |producer_id| {
                        if (producer_id.index() < self.program.instructions.len) {
                            sum = saturatingAdd(sum, self.operationNodeSum(self.program.instructions[producer_id.index()].operation, &budget));
                        }
                    },
                }
            },
            .condition, .discarded_condition => |value_id| sum = saturatingAdd(2, self.valueNodeSum(value_id, &budget)),
            .edge => |edge| {
                sum = 0;
                for (edge.arguments) |argument| sum = saturatingAdd(sum, saturatingAdd(2, self.valueNodeSum(argument, &budget)));
            },
            .composition => |plan| {
                sum = 4;
                for ([_]ir.ValueId{ plan.condition, plan.then_value, plan.else_value }) |value_id| {
                    sum = saturatingAdd(sum, self.valueNodeSum(value_id, &budget));
                }
            },
            .native_header => |protocol| {
                const arguments = switch (protocol) {
                    .numeric => |numeric| numeric.initial_arguments,
                    .generic => |generic| generic.initial_arguments,
                };
                sum = 8;
                for (arguments) |value_id| sum = saturatingAdd(sum, saturatingAdd(2, self.valueNodeSum(value_id, &budget)));
            },
            .normalized_loop => |numeric| {
                sum = 8;
                for (numeric.initial_arguments) |value_id| sum = saturatingAdd(sum, saturatingAdd(2, self.valueNodeSum(value_id, &budget)));
            },
        }
        return if (budget == 0) luau_runtime.max_registers + 1 else sum;
    }

    fn valueNodeSum(self: ItemPricing, value_id: ir.ValueId, budget: *usize) usize {
        if (budget.* == 0) return 0;
        budget.* -= 1;
        const resolved = self.emission.dead.resolveValue(value_id);
        if (resolved.index() >= self.program.values.len) return indexed_upvalue_need;
        if (self.compositions) |compositions| {
            if (compositions.expressions.get(resolved)) |plan| {
                var sum: usize = 2;
                for ([_]ir.ValueId{ plan.condition, plan.then_value, plan.else_value }) |item| sum = saturatingAdd(sum, self.valueNodeSum(item, budget));
                return sum;
            }
            if (compositions.absorbed_values.get(resolved)) |producer_id| {
                if (producer_id.index() >= self.program.instructions.len) return indexed_upvalue_need;
                return self.operationNodeSum(self.program.instructions[producer_id.index()].operation, budget);
            }
        }
        const item = self.program.values[resolved.index()];
        switch (item.origin) {
            .instruction_result => |origin| if (origin.index == 0 and origin.instruction.index() < self.program.instructions.len) {
                const producer = self.program.instructions[origin.instruction.index()];
                if (self.emission.place_reads.contains(producer.id)) return indexed_upvalue_need;
                if (self.emission.fused_values.contains(producer.id) or self.emission.dead.isInlined(producer.id)) {
                    switch (self.emission.packs.role(producer.id)) {
                        .fused_adjustment => |invocation_id| if (invocation_id.index() < self.program.instructions.len) {
                            return self.operationNodeSum(self.program.instructions[invocation_id.index()].operation, budget);
                        },
                        else => {},
                    }
                    return self.operationNodeSum(producer.operation, budget);
                }
            },
            .capture => return indexed_upvalue_need,
            .parameter, .block_parameter => {},
        }
        if (item.function != self.scopes.function.id) return indexed_upvalue_need;
        if (self.emission.names.valueUsesStorage(resolved)) return 2;
        return 0;
    }

    fn operationNodeSum(self: ItemPricing, operation: ir.Operation, budget: *usize) usize {
        const Visitor = struct {
            pricing: ItemPricing,
            budget: *usize,
            sum: *usize,

            pub fn value(visitor: @This(), value_id: ir.ValueId) void {
                visitor.sum.* = saturatingAdd(visitor.sum.*, saturatingAdd(1, visitor.pricing.valueNodeSum(value_id, visitor.budget)));
            }
            pub fn pack(visitor: @This(), _: ir.ValuePackId) void {
                visitor.sum.* = saturatingAdd(visitor.sum.*, stored_pack_need);
            }
            pub fn place(visitor: @This(), _: ir.PlaceId) void {
                visitor.sum.* = saturatingAdd(visitor.sum.*, indexed_upvalue_need);
            }
        };
        var sum: usize = switch (operation) {
            .constant => |literal_value| return literalNeed(literal_value),
            .make_table_literal => |constructor| saturatingAdd(2, @min(16, constructor.fields.len + @intFromBool(constructor.tail_pack != null))),
            else => 2,
        };
        runtime_uses.visitOperationUses(operation, Visitor{ .pricing = self, .budget = budget, .sum = &sum });
        return sum;
    }

    /// A native `for` header at -O0 and -O1 while it evaluates its values (`emitNumericForOpen`, `emitGenericForOpen`).
    fn nativeHeaderNeed(self: ItemPricing, protocol: iteration_protocol.Match) ?usize {
        switch (protocol) {
            .numeric => |numeric| {
                if (numeric.initial_arguments.len < 3) return null;
                return self.numericForFrame(numeric.initial_arguments[0], numeric.initial_arguments[1], numeric.initial_arguments[2]);
            },
            .generic => |generic| {
                if (generic.initial_arguments.len < 3) return null;
                const initializers = generic.initial_arguments[0..3];
                var count: usize = initializers.len;
                while (count > 1 and self.valueIsExactNil(initializers[count - 1])) count -= 1;
                const fused: ?ir.Instruction = if (count == 3) blk: {
                    const fusion = self.scopes.genericInitializerFusion(initializers, generic.transition.block) orelse break :blk null;
                    if (fusion.producer.index() >= self.program.instructions.len) return null;
                    break :blk self.program.instructions[fusion.producer.index()];
                } else null;
                return self.genericForFrame(initializers[0..count], fused);
            },
        }
    }

    /// A trailing `nil` the generic `for` line leaves out (`genericInitializerCount`).
    fn valueIsExactNil(self: ItemPricing, value_id: ir.ValueId) bool {
        const resolved = self.emission.dead.resolveValue(value_id);
        if (resolved.index() >= self.program.values.len) return false;
        const origin = switch (self.program.values[resolved.index()].origin) {
            .instruction_result => |value| value,
            else => return false,
        };
        if (origin.index != 0 or origin.instruction.index() >= self.program.instructions.len) return false;
        return switch (self.program.instructions[origin.instruction.index()].operation) {
            .constant => |literal_value| literal_value == .nil_value,
            else => false,
        };
    }

    /// The lines of a semantic-normalized numeric loop (`emitSemanticNormalizedNumericLoop`): the state locals declared
    /// from the initializers, `while true do`, the advance, the step test, the bound test into the has-value local, the
    /// exit test and the loop variable.
    fn normalizedLoopNeed(self: ItemPricing, numeric: iteration_protocol.NumericLoop) ?usize {
        if (numeric.initial_arguments.len < 3 or numeric.transition.results.len != 4) return null;
        const operation = numeric.operation;
        var frame: usize = 1;
        for ([_]ir.ValueId{ operation.control, operation.limit, operation.step }, numeric.initial_arguments[0..3]) |parameter, initial| {
            frame = @max(frame, destinationNeed(self.resultDestination(parameter, true), self.writtenValue(initial, 0) orelse return null));
        }
        frame = @max(frame, destinationNeed(self.resultDestination(operation.control, false), operandsWritten(self.nameWritten(operation.control), self.nameWritten(operation.step))));
        const step_name = self.nameWritten(operation.step);
        frame = @max(frame, @max(autoNeed(step_name), saturatingAdd(heldRegister(step_name), 1)));
        const has_value = numeric.transition.results[0];
        frame = @max(frame, destinationNeed(self.resultDestination(has_value, false), operandsWritten(self.nameWritten(operation.control), self.nameWritten(operation.limit))));
        frame = @max(frame, autoNeed(self.nameWritten(has_value)));
        return @max(frame, destinationNeed(self.resultDestination(numeric.body_parameter, true), self.nameWritten(operation.control)));
    }
};

/// The level luau-compile builds a statement at. At -O0 every literal operand and table key takes a register; from -O1
/// a local declared alone with a literal and never assigned holds no register, and each read of it is built as that
/// literal where an operand must be a register. Every other -O1 difference only frees registers.
const PricingLevel = enum { o0, o1 };

/// The locals a statement reads as literals at -O1. The registers they free are taken off its -O1 frame; counting fewer
/// than it reads takes off less, so a statement that reads more than the capacity stays covered.
const ConstantReads = struct {
    keys: [32]u64 = undefined,
    len: usize = 0,

    fn record(self: *ConstantReads, key: u64) void {
        for (self.keys[0..self.len]) |existing| {
            if (existing == key) return;
        }
        if (self.len == self.keys.len) return;
        self.keys[self.len] = key;
        self.len += 1;
    }
};

/// The branch compositions of a structured function as its writer composes them, the `branch_expression.Composition`
/// of every region merged: a deferred composition is written inline where its value is used, and an absorbed condition
/// producer inline as its composition's condition.
const Compositions = struct {
    expressions: std.AutoHashMapUnmanaged(ir.ValueId, branch_expression.Plan) = .empty,
    absorbed_values: std.AutoHashMapUnmanaged(ir.ValueId, ir.InstructionId) = .empty,
    absorbed_instructions: std.AutoHashMapUnmanaged(ir.InstructionId, void) = .empty,

    fn deinit(self: *Compositions, allocator: std.mem.Allocator) void {
        self.absorbed_instructions.deinit(allocator);
        self.absorbed_values.deinit(allocator);
        self.expressions.deinit(allocator);
    }

    /// Whether a value is written inline where it is used: a deferred composition or an absorbed condition producer.
    fn writesInline(self: *const Compositions, value_id: ir.ValueId) bool {
        return self.expressions.contains(value_id) or self.absorbed_values.contains(value_id);
    }

    fn addRegion(
        self: *Compositions,
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        emission: *const emission_planning.Plan,
        scopes: *const emission_scope.Plan,
        region: *const structure.Region,
    ) !void {
        {
            var composition = try branch_expression.Composition.init(allocator, program, emission, scopes, region);
            defer composition.deinit();
            var expressions = composition.expressions.iterator();
            while (expressions.next()) |entry| try self.expressions.put(allocator, entry.key_ptr.*, entry.value_ptr.*);
            var absorbed = composition.absorbed_values.iterator();
            while (absorbed.next()) |entry| {
                try self.absorbed_values.put(allocator, entry.key_ptr.*, entry.value_ptr.*);
                try self.absorbed_instructions.put(allocator, entry.value_ptr.*, {});
            }
        }
        for (region.nodes) |*node| switch (node.*) {
            .block, .loop_control, .loop_terminal => {},
            .branch => |branch| {
                try self.addRegion(allocator, program, emission, scopes, branch.then_region);
                try self.addRegion(allocator, program, emission, scopes, branch.else_region);
            },
            .loop => |loop| try self.addRegion(allocator, program, emission, scopes, loop.body_region),
            .latch_loop => |loop| try self.addRegion(allocator, program, emission, scopes, loop.body_region),
            .infinite_loop => |loop| {
                try self.addRegion(allocator, program, emission, scopes, loop.body_region);
                if (loop.shared_side_exit) |side_exit| {
                    for (side_exit.entries) |entry| try self.addRegion(allocator, program, emission, scopes, entry.region);
                }
            },
            .loop_boundary => |control| {
                try self.addRegion(allocator, program, emission, scopes, control.body_region);
                switch (control.boundary) {
                    .side_exit => |side_exit| try self.addRegion(allocator, program, emission, scopes, side_exit.region),
                    .side_escape => |side_escape| try self.addRegion(allocator, program, emission, scopes, side_escape.region),
                    else => {},
                }
            },
        };
    }
};

fn compositionIsLogical(dead: *const dead_code.Plan, plan: branch_expression.Plan) bool {
    const condition = dead.resolveValue(plan.condition);
    return dead.resolveValue(plan.else_value) == condition or dead.resolveValue(plan.then_value) == condition;
}

fn operatorIsTest(operator: ir.BinaryOperator) bool {
    return switch (operator) {
        .equal, .not_equal, .less, .less_equal, .greater, .greater_equal, .logical_and, .logical_or => true,
        else => false,
    };
}

fn operatorIsComparison(operator: ir.BinaryOperator) bool {
    return switch (operator) {
        .equal, .not_equal, .less, .less_equal, .greater, .greater_equal => true,
        else => false,
    };
}

/// The registers a value written into a local declared before takes above the register top: a call or a constructor
/// is built there and moved down, a field of an object that is not a register reads its object there, and an if-else
/// tests its condition and builds its arms there; any other value is built in the local itself.
fn aboveTopForLocal(written: Written) usize {
    if (written.above) |above| return above;
    if (written.relocates or written.table) return written.need;
    if (written.object_need) |object_need| return object_need;
    return written.need -| 1;
}

/// The registers a value built into a temporary register below the register top takes above the top (a `for`
/// header's slots, a value of a declaration list that is not in its last slot).
fn aboveTopForTemporary(written: Written) usize {
    if (written.above) |above| return above;
    if (written.relocates or written.table) return written.need;
    return written.need -| 1;
}

/// Where a statement writes its one value, as the writer names the destination.
const Destination = union(enum) {
    /// `local x = e`: built in the new local's register, which the local count already holds.
    declared,
    /// `x = e`, a local of this function declared before.
    local,
    /// `t[k] = e` with `t` a local of this function and `k` a literal: a storage table's slot or a box's slot.
    slot,
    /// `u = e`, an upvalue.
    upvalue,
    /// `t[k] = e` with `t` an upvalue and `k` a literal: a captured box or an enclosing function's storage slot.
    upvalue_slot,
    /// `rawset(b, 1, e)`, a place bound outside the chunk.
    external,
    /// `t[k] = e`, or `t.name = e` when `key` is null, as `compileStatAssign` builds a table store: the object, then
    /// the key, then the value.
    table: struct { object: Written, key: ?Written },
    /// `G = e`.
    global,
};

/// The registers above the register top a statement holds while it writes `value` to `destination`.
fn destinationNeed(destination: Destination, value: Written) usize {
    return switch (destination) {
        .declared => value.need -| 1,
        .local => aboveTopForLocal(value),
        .slot => saturatingAdd(1, autoNeed(value)),
        .upvalue, .global => autoNeed(value),
        .upvalue_slot => saturatingAdd(2, autoNeed(value)),
        .external => @max(4, saturatingAdd(3, value.need)),
        .table => |table| if (table.key) |key|
            @max(
                @max(autoNeed(table.object), saturatingAdd(heldRegister(table.object), autoNeed(key))),
                saturatingAdd(saturatingAdd(heldRegister(table.object), heldRegister(key)), autoNeed(value)),
            )
        else
            @max(autoNeed(table.object), saturatingAdd(heldRegister(table.object), autoNeed(value))),
    };
}

/// The registers a compound assignment's target address holds: the most it takes while it is built, and what it
/// keeps while the update is evaluated.
const Address = struct { peak: usize = 0, held: usize = 0 };

/// One destination of a list assignment (`d1, ..., dn = ...`): a local of this function, written by its value, or a
/// literal-keyed slot of a local table.
const ListDestination = struct {
    slot: bool,
    value: ir.ValueId,
};

/// One value of a list assignment or declaration as written, and the value whose expression it is (null for a value
/// the statement builds itself, which reads no destination).
const ListItem = struct {
    written: Written,
    value: ?ir.ValueId = null,
};

/// `local d1, ..., dn = v1, ..., vm` as luau-compile's `compileStatLocal` builds it, above the n new locals the local
/// count already holds: the value in the last slot, and a multi-value item that fills the slots from its own, is built
/// at its slot; every other value is built at its slot with what it needs above the new locals.
fn declaredListNeed(count: usize, items: []const ListItem) usize {
    var peak = count;
    for (items, 0..) |item, index| {
        if (index + 1 == count or (index + 1 == items.len and item.written.multret and index < count)) {
            peak = @max(peak, saturatingAdd(index, item.written.need));
        } else {
            peak = @max(peak, saturatingAdd(count, aboveTopForTemporary(item.written)));
        }
    }
    return peak - count;
}

/// `d1, ..., dn = v1, ..., vm` as luau-compile's `compileStatAssign` builds it: each slot destination's key in a
/// register, in order; then one conflict register for each local destination that a value read after the local is
/// assigned reads (`conflicts`, counted in `resolveAssignConflicts`' order); then the values: one built into a local
/// destination in place, one for another destination kept in a register, and a last multi-value item filling every
/// remaining destination from one register range.
fn assignListNeed(destinations: []const ListDestination, items: []const ListItem, conflicts: usize) usize {
    var top: usize = 0;
    var peak: usize = 0;
    for (destinations) |destination| {
        if (!destination.slot) continue;
        peak = @max(peak, saturatingAdd(top, 1));
        top = saturatingAdd(top, 1);
    }
    top = saturatingAdd(top, conflicts);
    peak = @max(peak, top);
    for (items, 0..) |item, index| {
        if (index >= destinations.len) {
            peak = @max(peak, saturatingAdd(top, item.written.need));
            continue;
        }
        if (index + 1 == items.len and destinations.len > items.len) {
            const rest = destinations.len - items.len + 1;
            peak = @max(peak, saturatingAdd(top, @max(rest, item.written.need)));
            top = saturatingAdd(top, rest);
        } else if (!destinations[index].slot) {
            peak = @max(peak, saturatingAdd(top, aboveTopForLocal(item.written)));
        } else if (!item.written.register) {
            peak = @max(peak, saturatingAdd(top, item.written.need));
            top = saturatingAdd(top, 1);
        }
    }
    return peak;
}

/// The conflict registers of a list assignment, in `resolveAssignConflicts`' order: the values of the local
/// destinations in order, each local marked assigned after its own value is visited; then the values of the other
/// destinations and the values past the last destination. A local destination is a conflict when a value visited after
/// it was marked reads it.
/// `reads` answers `itemReadsDestination(item, destination)`: whether a value's written expression reads the local a
/// destination names (`ItemPricing`, which follows the written forms).
fn listConflictCount(destinations: []const ListDestination, items: []const ListItem, reads: anytype) usize {
    var count: usize = 0;
    for (destinations, 0..) |destination, assigned_index| {
        if (destination.slot) continue;
        var conflict = false;
        for (destinations[assigned_index + 1 ..], assigned_index + 1..) |later, later_index| {
            if (later.slot or later_index >= items.len) continue;
            if (reads.itemReadsDestination(items[later_index], destination.value)) conflict = true;
        }
        for (destinations, 0..) |other, other_index| {
            if (!other.slot or other_index >= items.len) continue;
            if (reads.itemReadsDestination(items[other_index], destination.value)) conflict = true;
        }
        if (items.len > destinations.len) {
            for (items[destinations.len..]) |item| {
                if (reads.itemReadsDestination(item, destination.value)) conflict = true;
            }
        }
        if (conflict) count += 1;
    }
    return count;
}

/// What a statement root prices: an instruction written as its own statement (with the declaration choices the
/// writer makes for it), a terminator, a branch condition, a discarded condition (`local _ = c`), an edge copy, a
/// composition statement, a native `for` header, or the lines of a semantic-normalized numeric loop.
const Root = union(enum) {
    instruction: struct { instruction: ir.Instruction, declare_results: bool, declare_place: bool },
    terminator: ir.Block,
    condition: ir.ValueId,
    discarded_condition: ir.ValueId,
    edge: struct { target: ir.Block, arguments: []const ir.ValueId },
    composition: branch_expression.Plan,
    native_header: iteration_protocol.Match,
    normalized_loop: iteration_protocol.NumericLoop,
};

/// Prices statement roots at -O0 and at -O1: a root's frame is the larger of its -O0 frame and its -O1 frame less the
/// constant locals it reads, which hold no register at -O1; a root the pricing cannot price is charged its node sum.
const RootPricing = struct {
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    compositions: ?*const Compositions,
    reads: ConstantReads = .{},

    fn at(self: *RootPricing, level: PricingLevel) ItemPricing {
        return .{
            .program = self.program,
            .emission = self.emission,
            .scopes = self.scopes,
            .compositions = self.compositions,
            .level = level,
            .constant_reads = if (level == .o1) &self.reads else null,
        };
    }

    fn frame(self: *RootPricing, root: Root) std.mem.Allocator.Error!usize {
        self.reads = .{};
        const o0 = try self.at(.o0).rootNeed(self.allocator, root);
        const o1 = try self.at(.o1).rootNeed(self.allocator, root);
        if (o0) |frame_o0| {
            if (o1) |frame_o1| return levelFrame(frame_o0, frame_o1, self.reads.len);
        }
        return self.at(.o0).fallbackNeed(root);
    }
};

/// A statement root's frame from its two levels: its -O0 frame, or its -O1 frame less the constant locals it reads, each
/// of which holds no register at -O1, so the register a read of one takes as its literal is the one the local would
/// have held.
fn levelFrame(frame_o0: usize, frame_o1: usize, constant_reads: usize) usize {
    return @max(frame_o0, frame_o1 -| constant_reads);
}

/// The most items one list statement is priced for; a longer list is charged its node sum.
const max_list_items = 256;

/// The most expression nodes the node-sum bound visits for one root; past it the root is charged above the limit.
const fallback_node_budget = 1 << 16;

fn resultsUseStorage(emission: *const emission_planning.Plan, results: []const ir.ValueId) bool {
    for (results) |result| {
        if (emission.names.valueUsesStorage(result)) return true;
    }
    return false;
}

/// Charges every statement root of a function its frame at the host it is written in, joined with the host's other
/// frames by `@max` (statements run one after another): each instruction written as a statement, each return and
/// other terminator, each branch condition, each edge copy, each composition statement, each loop's `while true`
/// literal, each transfer wrapper's `until true` literal and each native `for` header. The flat layout writes every
/// statement at the function's root, under its dispatch tests.
fn addStatementRootFrames(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    function: ir.Function,
    root: *const structure.Region,
    compositions: *const Compositions,
    temporaries: []usize,
) !void {
    var pricing: RootPricing = .{
        .allocator = allocator,
        .program = program,
        .emission = emission,
        .scopes = scopes,
        .compositions = if (root.arbitrary_cfg) null else compositions,
    };
    // Blocks whose branch condition the region walk prices (a composition, a discarded condition, a native `for`
    // header) and blocks whose edges carry a composition's arms, which the writer never copies.
    const condition_priced = try allocator.alloc(bool, program.blocks.len);
    defer allocator.free(condition_priced);
    @memset(condition_priced, false);
    const edges_composed = try allocator.alloc(bool, program.blocks.len);
    defer allocator.free(edges_composed);
    @memset(edges_composed, false);

    if (root.arbitrary_cfg) {
        // `while true do`, `if __lifter_pc == k then` and `if __lifter_pc <= k then`: a literal in a register at -O0.
        addTemporaryAtScope(temporaries, scopes, scopes.rootScope(), 1);
    } else {
        try addRegionLiteralFrames(&pricing, root, false, temporaries, condition_priced, edges_composed);
    }

    for (function.blocks) |block_id| {
        if (!readable.block(block_id) or block_id.index() >= program.blocks.len) continue;
        const block = program.blocks[block_id.index()];
        if (scopes.blockScope(block_id)) |scope| {
            addTemporaryAtScope(temporaries, scopes, scope, try terminatorRootFrame(&pricing, block));
            switch (block.terminator) {
                .branch => |branch| if (!condition_priced[block_id.index()] and !scopes.nativeIterationConsumesParameters(block_id)) {
                    addTemporaryAtScope(temporaries, scopes, scope, try pricing.frame(.{ .condition = branch.condition }));
                },
                else => {},
            }
        }
        if (!edges_composed[block_id.index()]) switch (block.terminator) {
            .jump => |edge| try edgeCopyRootFrame(&pricing, block_id, edge, temporaries),
            .branch => |branch| {
                try edgeCopyRootFrame(&pricing, block_id, branch.then_edge, temporaries);
                try edgeCopyRootFrame(&pricing, block_id, branch.else_edge, temporaries);
            },
            else => {},
        };
        for (block.instructions) |instruction_id| {
            if (!readable.instruction(instruction_id) or instruction_id.index() >= program.instructions.len) continue;
            const instruction = program.instructions[instruction_id.index()];
            if (!instructionIsStatement(emission, scopes, compositions, instruction)) continue;
            const scope = scopes.renderedPressureScope(instruction_id) orelse continue;
            const declare_place = switch (instruction.operation) {
                .place_write => |write| if (root.arbitrary_cfg)
                    scopes.arbitraryLeafDeclaresPlace(write.place) and write.place.index() < program.places.len and
                        program.places[write.place.index()].origin == .instruction and
                        program.places[write.place.index()].origin.instruction == instruction_id
                else
                    !emission.names.placeUsesStorage(write.place) and scopes.instructionDeclaresPlace(instruction_id, write.place),
                else => false,
            };
            const frame = try statementRootFrame(&pricing, instruction, scopes.instructionDeclaresResults(instruction_id), declare_place);
            addTemporaryAtScope(temporaries, scopes, scope, frame);
        }
    }
}

/// The frame of an instruction the writer writes as a statement of its own, with the declarations it writes for it.
fn statementRootFrame(pricing: *RootPricing, instruction: ir.Instruction, declare_results: bool, declare_place: bool) !usize {
    return pricing.frame(.{ .instruction = .{
        .instruction = instruction,
        .declare_results = declare_results,
        .declare_place = declare_place,
    } });
}

/// The frame of a block's terminator: a return, `error(...)`, or nothing for a jump or a branch.
fn terminatorRootFrame(pricing: *RootPricing, block: ir.Block) !usize {
    return pricing.frame(.{ .terminator = block });
}

/// Whether `emitInstruction` writes an instruction as a statement of its own: not absorbed into a composition, not
/// written inside another statement, not suppressed by a native loop and not a moved literal initializer.
fn instructionIsStatement(
    emission: *const emission_planning.Plan,
    scopes: *const emission_scope.Plan,
    compositions: *const Compositions,
    instruction: ir.Instruction,
) bool {
    if (compositions.absorbed_instructions.contains(instruction.id)) return false;
    if (!emission.instructionMayEmit(instruction)) return false;
    if (scopes.instructionIsMovedLiteralInitializer(instruction.id)) return false;
    return !scopes.instructionSuppressedByControl(instruction.id);
}

/// An edge's parameter copy at the blocks on both sides, where `addEdgeTemporaryFrame` places the copy's cycles.
fn edgeCopyRootFrame(pricing: *RootPricing, source: ir.BlockId, edge: ir.Edge, temporaries: []usize) !void {
    const program = pricing.program;
    const scopes = pricing.scopes;
    if (edge.target.index() >= program.blocks.len or scopes.edgeParametersConsumed(edge.target)) return;
    const target = program.blocks[edge.target.index()];
    if (target.parameters.len == 0) return;
    const frame = try pricing.frame(.{ .edge = .{ .target = target, .arguments = edge.arguments } });
    if (frame == 0) return;
    if (scopes.blockScope(source)) |scope| addTemporaryAtScope(temporaries, scopes, scope, frame);
    if (scopes.blockScope(edge.target)) |scope| addTemporaryAtScope(temporaries, scopes, scope, frame);
}

/// The roots the structured layout writes around its nodes: each loop's `while true` literal (a register at -O0,
/// tested before the body's locals), each transfer wrapper's `until true` literal (compiled inside the `repeat` body,
/// above the wrapped region's locals), each native `for` header, and each branch node written as a composition
/// statement or a discarded condition.
fn addRegionLiteralFrames(
    pricing: *RootPricing,
    region: *const structure.Region,
    loop_body: bool,
    temporaries: []usize,
    condition_priced: []bool,
    edges_composed: []bool,
) !void {
    const allocator = pricing.allocator;
    const program = pricing.program;
    const scopes = pricing.scopes;
    if (region.nodes.len != 0 and try structured_escape.regionIsWrapped(allocator, region)) {
        if (wrapperLiteralHost(scopes, region, loop_body)) |host| addTemporaryAtScope(temporaries, scopes, host, 1);
    }
    for (region.nodes, 0..) |*node, node_index| {
        const node_scope = scopes.nodeScope(node);
        switch (node.*) {
            .block, .loop_control, .loop_terminal => {},
            .branch => |branch| {
                if (scopes.nativeIterationConsumesParameters(branch.block)) {
                    if (try iteration_protocol.matchAcyclicBranch(allocator, program, branch)) |acyclic| {
                        condition_priced[branch.block.index()] = true;
                        if (node_scope) |scope| addTemporaryAtScope(temporaries, scopes, scope, try nativeHeaderFrame(pricing, region, node_index, acyclic.protocol));
                        try addRegionLiteralFrames(pricing, branch.then_region, branch.then_region == acyclic.body_region, temporaries, condition_priced, edges_composed);
                        try addRegionLiteralFrames(pricing, branch.else_region, branch.else_region == acyclic.body_region, temporaries, condition_priced, edges_composed);
                        continue;
                    }
                }
                try addBranchFormFrame(pricing, node, branch, temporaries, condition_priced, edges_composed);
                try addRegionLiteralFrames(pricing, branch.then_region, false, temporaries, condition_priced, edges_composed);
                try addRegionLiteralFrames(pricing, branch.else_region, false, temporaries, condition_priced, edges_composed);
            },
            .loop => |loop| {
                const native = if (scopes.nativeIterationConsumesParameters(loop.header))
                    try iteration_protocol.matchLoop(allocator, program, loop)
                else
                    null;
                if (node_scope) |scope| {
                    const frame = if (native) |protocol| try nativeHeaderFrame(pricing, region, node_index, protocol) else 1;
                    addTemporaryAtScope(temporaries, scopes, scope, frame);
                }
                if (native != null) condition_priced[loop.header.index()] = true;
                try addRegionLiteralFrames(pricing, loop.body_region, true, temporaries, condition_priced, edges_composed);
            },
            .latch_loop => |loop| {
                if (node_scope) |scope| addTemporaryAtScope(temporaries, scopes, scope, 1);
                try addRegionLiteralFrames(pricing, loop.body_region, true, temporaries, condition_priced, edges_composed);
            },
            .infinite_loop => |loop| {
                if (node_scope) |scope| addTemporaryAtScope(temporaries, scopes, scope, 1);
                try addRegionLiteralFrames(pricing, loop.body_region, true, temporaries, condition_priced, edges_composed);
                if (loop.shared_side_exit) |side_exit| {
                    for (side_exit.entries) |entry| try addRegionLiteralFrames(pricing, entry.region, false, temporaries, condition_priced, edges_composed);
                }
            },
            .loop_boundary => |control| {
                var native_body: ?*const structure.Region = null;
                if (scopes.nativeIterationConsumesParameters(control.block)) {
                    if (try iteration_protocol.matchAcyclicLoopBoundary(allocator, program, control)) |acyclic| {
                        condition_priced[control.block.index()] = true;
                        if (node_scope) |scope| addTemporaryAtScope(temporaries, scopes, scope, try nativeHeaderFrame(pricing, region, node_index, acyclic.protocol));
                        switch (control.boundary) {
                            .side_exit => |side_exit| native_body = side_exit.region,
                            else => {},
                        }
                    }
                }
                try addRegionLiteralFrames(pricing, control.body_region, false, temporaries, condition_priced, edges_composed);
                switch (control.boundary) {
                    .side_exit => |side_exit| try addRegionLiteralFrames(pricing, side_exit.region, native_body == side_exit.region, temporaries, condition_priced, edges_composed),
                    .side_escape => |side_escape| try addRegionLiteralFrames(pricing, side_escape.region, false, temporaries, condition_priced, edges_composed),
                    else => {},
                }
            },
        }
    }
}

/// The host whose count holds what is live at a wrapped region's `until true`: the region's own container, whose
/// locals the `repeat` body declares. A region written in `do` groups closes them before `until true`: inside a loop
/// the literal sits above the loop's registers and variables, which the first group's host counts with its own locals;
/// elsewhere it sits at the host around the groups.
fn wrapperLiteralHost(scopes: *const emission_scope.Plan, region: *const structure.Region, loop_body: bool) ?emission_scope.ScopeId {
    const first = scopes.nodeContainerScope(&region.nodes[0]) orelse return null;
    const last = scopes.nodeContainerScope(&region.nodes[region.nodes.len - 1]) orelse return null;
    if (first == last or loop_body) return first;
    const host = scopes.physicalHost(first) orelse return null;
    return scopes.parentPhysicalHost(host) orelse first;
}

/// A branch node written as a discarded condition (`local _ = c`, both edges the same) or as a composition
/// (`branch_expression.match`): a statement at its node unless its region defers it into its consumer. Either way the
/// writer writes no `if` for its condition and no copy for a composition's arms.
fn addBranchFormFrame(
    pricing: *RootPricing,
    node: *const structure.Node,
    branch_plan: structure.Branch,
    temporaries: []usize,
    condition_priced: []bool,
    edges_composed: []bool,
) !void {
    const program = pricing.program;
    const emission = pricing.emission;
    const scopes = pricing.scopes;
    if (branch_plan.block.index() >= program.blocks.len) return;
    const block = program.blocks[branch_plan.block.index()];
    const branch = switch (block.terminator) {
        .branch => |value| value,
        else => return,
    };
    if (branch_plan.join != null and branch_plan.then_edge_override == null and branch_plan.else_edge_override == null and
        branch_plan.then_shared_reentry == null and branch_plan.else_shared_reentry == null and emission.branchEdgesAreIdentical(block))
    {
        condition_priced[block.id.index()] = true;
        if (emission.discardedBranchConditionNeedsLocal(program, block)) {
            if (scopes.blockScope(block.id)) |scope| addTemporaryAtScope(temporaries, scopes, scope, try pricing.frame(.{ .discarded_condition = branch.condition }));
        }
        return;
    }
    const plan = branch_expression.match(program, emission, scopes, branch, branch_plan) orelse return;
    condition_priced[block.id.index()] = true;
    edges_composed[block.id.index()] = true;
    for ([_]*const structure.Region{ branch_plan.then_region, branch_plan.else_region }) |arm| {
        for (arm.nodes) |arm_node| switch (arm_node) {
            .block => |arm_block| if (arm_block.index() < edges_composed.len) {
                edges_composed[arm_block.index()] = true;
            },
            else => {},
        };
    }
    const compositions = pricing.compositions orelse return;
    if (compositions.expressions.contains(emission.dead.resolveValue(plan.target))) return;
    if (scopes.nodeScope(node)) |scope| addTemporaryAtScope(temporaries, scopes, scope, try pricing.frame(.{ .composition = plan }));
}

/// A native `for` header at its node, above what the node's host counts: its registers and the values built into
/// them, less the header parameters the scope plan counts as locals of the host although no line declares them
/// (they stand for the `for`'s own registers, as `addNativeForFootprints` counts them). A semantic-normalized
/// numeric loop is written `while true do` after declaring its state locals.
fn nativeHeaderFrame(pricing: *RootPricing, region: *const structure.Region, node_index: usize, protocol: iteration_protocol.Match) !usize {
    const program = pricing.program;
    const emission = pricing.emission;
    const scopes = pricing.scopes;
    const native = try emit_luau.nativeForAt(pricing.allocator, program, emission, scopes, region, node_index) orelse return switch (protocol) {
        .numeric => |numeric| try pricing.frame(.{ .normalized_loop = numeric }),
        .generic => 1,
    };
    var covered: usize = 0;
    for (program.blocks[native.header.index()].parameters) |parameter| {
        if (!emission.names.valueUsesStorage(parameter) and scopes.valueScope(parameter) != null) covered += 1;
    }
    const completion: usize = @intFromBool(native.completion);
    const completion_uncovered = completion -| covered;
    const header_frame = try pricing.frame(.{ .native_header = protocol });
    return saturatingAdd(header_frame, completion) -| saturatingAdd(covered, completion_uncovered);
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
    if (edge.target.index() >= program.blocks.len or scopes.edgeParametersConsumed(edge.target)) return;
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

test "a list assignment counts its conflict registers in luau-compile's order" {
    // luau-compile's resolveAssignConflicts visits the value of each local destination in turn and marks the local
    // assigned after it, then the values of the other destinations and the values past the last one; a local read by
    // a value visited after it was marked is copied to a register of its own before the stores. The reads below are
    // the destination locals each value names.
    const Reads = struct {
        matrix: []const []const bool,

        fn itemReadsDestination(self: @This(), item: ListItem, destination: ir.ValueId) bool {
            return self.matrix[item.value.?.index()][destination.index()];
        }
    };
    const slot = ListDestination{ .slot = true, .value = ir.ValueId.fromIndex(0) };
    const local = ListDestination{ .slot = false, .value = ir.ValueId.fromIndex(1) };
    const reads_local = Reads{ .matrix = &.{ &.{ false, true }, &.{ false, false } } };
    // `T[300], p = f(p)`: p takes the call's second result, so its own value is none; the slot's value, the call, reads
    // p after p is marked: one conflict register, above the key, then the call's two results (luau-compile 4).
    const call = [_]ListItem{.{ .written = .{ .need = 2, .relocates = true, .multret = true }, .value = ir.ValueId.fromIndex(0) }};
    try std.testing.expectEqual(@as(usize, 1), listConflictCount(&.{ slot, local }, &call, reads_local));
    try std.testing.expectEqual(@as(usize, 4), assignListNeed(&.{ slot, local }, &call, 1));
    // `T[300], p = p + a, b`: the slot's value is visited after p's own value, b, has marked p, so it is a conflict,
    // although it comes first in the list (luau-compile 3; the list order alone would give 2).
    const sum = [_]ListItem{
        .{ .written = .{ .need = 1 }, .value = ir.ValueId.fromIndex(0) },
        .{ .written = .{ .need = 1, .register = true }, .value = ir.ValueId.fromIndex(1) },
    };
    try std.testing.expectEqual(@as(usize, 1), listConflictCount(&.{ slot, local }, &sum, reads_local));
    try std.testing.expectEqual(@as(usize, 3), assignListNeed(&.{ slot, local }, &sum, 1));
    // `T[300], j = j + 1, y`: the literal takes a register at -O0 (luau-compile 4).
    const advance = [_]ListItem{
        .{ .written = .{ .need = 2 }, .value = ir.ValueId.fromIndex(0) },
        .{ .written = .{ .need = 1, .register = true }, .value = ir.ValueId.fromIndex(1) },
    };
    try std.testing.expectEqual(@as(usize, 4), assignListNeed(&.{ slot, local }, &advance, listConflictCount(&.{ slot, local }, &advance, reads_local)));
    // `p, q = q, p`: q's own value reads p, marked before it: one conflict (luau-compile 1).
    const swap = [_]ListItem{
        .{ .written = .{ .need = 1, .register = true }, .value = ir.ValueId.fromIndex(0) },
        .{ .written = .{ .need = 1, .register = true }, .value = ir.ValueId.fromIndex(1) },
    };
    const reads_swap = Reads{ .matrix = &.{ &.{ false, true }, &.{ true, false } } };
    const first = ListDestination{ .slot = false, .value = ir.ValueId.fromIndex(0) };
    const second = ListDestination{ .slot = false, .value = ir.ValueId.fromIndex(1) };
    try std.testing.expectEqual(@as(usize, 1), listConflictCount(&.{ first, second }, &swap, reads_swap));
    try std.testing.expectEqual(@as(usize, 1), assignListNeed(&.{ first, second }, &swap, 1));
}

test "at -O1 a statement builds a constant local's reads as its literal" {
    // `local k = 5` and then `T[300], T[301], T[302] = k, k, k`. At -O0 each key takes a register and each value is k's
    // register: 3. At -O1 k holds no register and each value is built as the literal in a register of its own: 6, less
    // the one register k would have held: the root is charged 5 (luau-compile 9 at -O0 and 11 at -O1 above five held
    // locals, the second without k).
    const slots = [_]ListDestination{
        .{ .slot = true, .value = ir.ValueId.fromIndex(0) },
        .{ .slot = true, .value = ir.ValueId.fromIndex(1) },
        .{ .slot = true, .value = ir.ValueId.fromIndex(2) },
    };
    const register: ListItem = .{ .written = .{ .need = 1, .register = true } };
    const literal: ListItem = .{ .written = .{ .need = 1, .constant = true } };
    const frame_o0 = assignListNeed(&slots, &.{ register, register, register }, 0);
    const frame_o1 = assignListNeed(&slots, &.{ literal, literal, literal }, 0);
    try std.testing.expectEqual(@as(usize, 3), frame_o0);
    try std.testing.expectEqual(@as(usize, 6), frame_o1);
    try std.testing.expectEqual(@as(usize, 5), levelFrame(frame_o0, frame_o1, 1));
    // When a statement assigns k first, k is a register at both levels: 3.
    try std.testing.expectEqual(@as(usize, 3), levelFrame(frame_o0, frame_o0, 0));
}

test "a wrapped loop body written in groups charges its until-true literal inside the loop" {
    // The worker of a numeric `for` whose body continues from two nested `if`s is written as two `do` groups inside
    // `repeat ... until true` (eight nodes, more than one group holds). The literal is compiled after the groups close,
    // above the loop's registers and variables: it is charged at the first group's host, whose chain holds them,
    // never at the host above the groups, which is the host of the loop node's own container, outside the loop.
    const allocator = std.testing.allocator;
    const parsed = try std.json.parseFromSlice(ir.Program, allocator, grouped_loop_body_ir, .{
        .allocate = .alloc_always,
        .ignore_unknown_fields = true,
    });
    defer parsed.deinit();
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const program = try lexical_transfer.prepareInArena(arena.allocator(), &parsed.value);
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
    const loop_node = &structured.root.nodes[1];
    const body = switch (loop_node.*) {
        .loop => |loop| loop.body_region,
        else => return error.TestUnexpectedResult,
    };
    try std.testing.expect(try structured_escape.regionIsWrapped(allocator, body));
    const first = scopes.nodeContainerScope(&body.nodes[0]).?;
    try std.testing.expect(first != scopes.nodeContainerScope(&body.nodes[body.nodes.len - 1]).?);
    try std.testing.expectEqual(first, wrapperLiteralHost(&scopes, body, true).?);
    const outside = scopes.physicalHost(scopes.nodeContainerScope(loop_node).?).?;
    try std.testing.expectEqual(outside, scopes.parentPhysicalHost(scopes.physicalHost(first).?).?);
    try std.testing.expect(outside != first);

    // A branch arm written in groups inside a loop: the worker of a numeric `for` whose body is `if c then repeat ...
    // until true end` and `x = q`, the `repeat` leaving by `break` from two nested `if`s twice around five one-line
    // `if`s, writes the arm (nine nodes) as two `do` groups inside `repeat ... until true` in the `if`. That literal is
    // compiled after the groups close, inside the `if`: it is charged at the host above the groups, the host of the
    // container that holds the branch node, which is the loop body's and so inside the loop.
    const arm_parsed = try std.json.parseFromSlice(ir.Program, allocator, grouped_branch_arm_ir, .{
        .allocate = .alloc_always,
        .ignore_unknown_fields = true,
    });
    defer arm_parsed.deinit();
    var arm_arena = std.heap.ArenaAllocator.init(allocator);
    defer arm_arena.deinit();
    const arm_program = try lexical_transfer.prepareInArena(arm_arena.allocator(), &arm_parsed.value);
    var arm_emission = try emission_planning.Plan.init(allocator, &arm_program, .standard_luau);
    defer arm_emission.deinit();
    var arm_analysis = try cfg.Analysis.init(allocator, &arm_program, arm_program.functions[1]);
    defer arm_analysis.deinit();
    var arm_structured = try structure.Plan.initWithArbitraryFallback(allocator, &arm_analysis);
    defer arm_structured.deinit();
    var arm_scopes = try emission_scope.Plan.init(
        allocator,
        &arm_program,
        arm_program.functions[1],
        &arm_analysis,
        &arm_structured,
        &arm_emission.packs,
        &arm_emission.dead,
        &arm_emission.place_writes,
        &arm_emission.place_reads,
        &arm_emission.fused_values,
        &arm_emission.closure_stores,
    );
    defer arm_scopes.deinit();
    const arm_loop = &arm_structured.root.nodes[1];
    const branch_node = switch (arm_loop.*) {
        .loop => |loop| &loop.body_region.nodes[0],
        else => return error.TestUnexpectedResult,
    };
    const arm = switch (branch_node.*) {
        .branch => |branch| branch.then_region,
        else => return error.TestUnexpectedResult,
    };
    try std.testing.expect(try structured_escape.regionIsWrapped(allocator, arm));
    const arm_first = arm_scopes.nodeContainerScope(&arm.nodes[0]).?;
    try std.testing.expect(arm_first != arm_scopes.nodeContainerScope(&arm.nodes[arm.nodes.len - 1]).?);
    const holding = arm_scopes.physicalHost(arm_scopes.nodeContainerScope(branch_node).?).?;
    try std.testing.expectEqual(holding, wrapperLiteralHost(&arm_scopes, arm, false).?);
    try std.testing.expect(holding != arm_scopes.physicalHost(arm_scopes.nodeContainerScope(arm_loop).?).?);
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
    const pressure = try maximumPressure(allocator, &program, &readable, &emission, &scopes, function, base, structured.root);
    // The certified total must cover the emitted peak.
    // Both loops also declare their owned exits' flags at the top of each pass, and maxOwnedDepth counts them.
    try std.testing.expectEqual(@as(usize, 13), pressure.total);
}

/// The worker (function 1) of a numeric `for` whose body continues from two nested `if`s twice: the source frontend's
/// lift, resolved, of `for i = 1, n do` with an `if p then if q then x = r; continue end end`, five one-line `if`s and
/// an `if q then if r then x = p; continue end end` before `x = i`, written as a wrapped body in two `do` groups.
const grouped_loop_body_ir =
    \\{"schema_version":"lifter_ir_v1","program_id":"grouped-loop-body","source_semantics":"luau","entry_function":0,"functions":[
    \\{"id":0,"name_hint":"chunk","lexical_parent":null,"parameters":[],"captures":[],"local_places":[],"blocks":[0],"entry_block":0,"is_variadic":true,"vararg_pack":0},
    \\{"id":1,"name_hint":"closure","lexical_parent":0,"parameters":[0,1,2,3],"captures":[],"local_places":[0],"blocks":[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],"entry_block":1,"is_variadic":false,"vararg_pack":null}]
    \\,"blocks":[
    \\{"id":0,"function":0,"name_hint":"entry","parameters":[],"instructions":[16],"terminator":{"return_values":[19]}},
    \\{"id":1,"function":1,"name_hint":"entry","parameters":[],"instructions":[0,1,2,3,4,5],"terminator":{"jump":{"target":2,"arguments":[5,0,6,7]}}},
    \\{"id":2,"function":1,"name_hint":"numeric_for_header","parameters":[9,10,11,12],"instructions":[6],"terminator":{"branch":{"condition":14,"then_edge":{"target":3,"arguments":[17]},"else_edge":{"target":4,"arguments":[]}}}},
    \\{"id":3,"function":1,"name_hint":"numeric_for_body","parameters":[13],"instructions":[],"terminator":{"branch":{"condition":1,"then_edge":{"target":5,"arguments":[]},"else_edge":{"target":6,"arguments":[]}}}},
    \\{"id":4,"function":1,"name_hint":"numeric_for_exit","parameters":[],"instructions":[15],"terminator":{"return_values":[18]}},
    \\{"id":5,"function":1,"name_hint":"then","parameters":[],"instructions":[],"terminator":{"branch":{"condition":2,"then_edge":{"target":7,"arguments":[]},"else_edge":{"target":8,"arguments":[]}}}},
    \\{"id":6,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":10,"arguments":[]}}},
    \\{"id":7,"function":1,"name_hint":"then","parameters":[],"instructions":[7],"terminator":{"jump":{"target":2,"arguments":[17,15,16,8]}}},
    \\{"id":8,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":9,"arguments":[]}}},
    \\{"id":9,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"jump":{"target":10,"arguments":[]}}},
    \\{"id":10,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"branch":{"condition":3,"then_edge":{"target":11,"arguments":[]},"else_edge":{"target":12,"arguments":[]}}}},
    \\{"id":11,"function":1,"name_hint":"then","parameters":[],"instructions":[8],"terminator":{"jump":{"target":13,"arguments":[]}}},
    \\{"id":12,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":13,"arguments":[]}}},
    \\{"id":13,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"branch":{"condition":1,"then_edge":{"target":14,"arguments":[]},"else_edge":{"target":15,"arguments":[]}}}},
    \\{"id":14,"function":1,"name_hint":"then","parameters":[],"instructions":[9],"terminator":{"jump":{"target":16,"arguments":[]}}},
    \\{"id":15,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":16,"arguments":[]}}},
    \\{"id":16,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"branch":{"condition":2,"then_edge":{"target":17,"arguments":[]},"else_edge":{"target":18,"arguments":[]}}}},
    \\{"id":17,"function":1,"name_hint":"then","parameters":[],"instructions":[10],"terminator":{"jump":{"target":19,"arguments":[]}}},
    \\{"id":18,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":19,"arguments":[]}}},
    \\{"id":19,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"branch":{"condition":3,"then_edge":{"target":20,"arguments":[]},"else_edge":{"target":21,"arguments":[]}}}},
    \\{"id":20,"function":1,"name_hint":"then","parameters":[],"instructions":[11],"terminator":{"jump":{"target":22,"arguments":[]}}},
    \\{"id":21,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":22,"arguments":[]}}},
    \\{"id":22,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"branch":{"condition":1,"then_edge":{"target":23,"arguments":[]},"else_edge":{"target":24,"arguments":[]}}}},
    \\{"id":23,"function":1,"name_hint":"then","parameters":[],"instructions":[12],"terminator":{"jump":{"target":25,"arguments":[]}}},
    \\{"id":24,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":25,"arguments":[]}}},
    \\{"id":25,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"branch":{"condition":2,"then_edge":{"target":26,"arguments":[]},"else_edge":{"target":27,"arguments":[]}}}},
    \\{"id":26,"function":1,"name_hint":"then","parameters":[],"instructions":[],"terminator":{"branch":{"condition":3,"then_edge":{"target":28,"arguments":[]},"else_edge":{"target":29,"arguments":[]}}}},
    \\{"id":27,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":31,"arguments":[]}}},
    \\{"id":28,"function":1,"name_hint":"then","parameters":[],"instructions":[13],"terminator":{"jump":{"target":2,"arguments":[17,15,16,8]}}},
    \\{"id":29,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":30,"arguments":[]}}},
    \\{"id":30,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"jump":{"target":31,"arguments":[]}}},
    \\{"id":31,"function":1,"name_hint":"join","parameters":[],"instructions":[14],"terminator":{"jump":{"target":2,"arguments":[17,15,16,8]}}}]
    \\,"instructions":[
    \\{"id":0,"block":1,"operation":{"constant":{"integer":"0"}},"results":[4],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":1,"block":1,"operation":{"place_write":{"place":0,"value":4}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":2,"block":1,"operation":{"constant":{"integer":"1"}},"results":[5],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":3,"block":1,"operation":{"constant":{"integer":"1"}},"results":[6],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":4,"block":1,"operation":{"constant":{"boolean":true}},"results":[7],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":5,"block":1,"operation":{"constant":{"boolean":false}},"results":[8],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":6,"block":2,"operation":{"numeric_for_next":{"control":9,"limit":10,"step":11,"initial":12}},"results":[14,15,16,17],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":true,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":7,"block":7,"operation":{"place_write":{"place":0,"value":3}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":8,"block":11,"operation":{"place_write":{"place":0,"value":1}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":9,"block":14,"operation":{"place_write":{"place":0,"value":2}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":10,"block":17,"operation":{"place_write":{"place":0,"value":3}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":11,"block":20,"operation":{"place_write":{"place":0,"value":2}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":12,"block":23,"operation":{"place_write":{"place":0,"value":3}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":13,"block":28,"operation":{"place_write":{"place":0,"value":1}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":14,"block":31,"operation":{"place_write":{"place":0,"value":13}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":15,"block":4,"operation":{"place_read":0},"results":[18],"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":16,"block":0,"operation":{"make_closure":{"function":1,"bindings":[]}},"results":[19],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}}]
    \\,"values":[
    \\{"id":0,"function":1,"name_hint":"n","origin":{"parameter":0}},
    \\{"id":1,"function":1,"name_hint":"p","origin":{"parameter":1}},
    \\{"id":2,"function":1,"name_hint":"q","origin":{"parameter":2}},
    \\{"id":3,"function":1,"name_hint":"r","origin":{"parameter":3}},
    \\{"id":4,"function":1,"type":{"kind":"integer","bit_width":64,"signed":true},"name_hint":"x","origin":{"instruction_result":{"instruction":0,"index":0}}},
    \\{"id":5,"function":1,"type":{"kind":"integer","bit_width":64,"signed":true},"name_hint":"numeric_initial","origin":{"instruction_result":{"instruction":2,"index":0}}},
    \\{"id":6,"function":1,"type":{"kind":"integer","bit_width":64,"signed":true},"name_hint":"numeric_step","origin":{"instruction_result":{"instruction":3,"index":0}}},
    \\{"id":7,"function":1,"type":{"kind":"boolean","bit_width":0,"signed":false},"name_hint":"numeric_initial_transition","origin":{"instruction_result":{"instruction":4,"index":0}}},
    \\{"id":8,"function":1,"type":{"kind":"boolean","bit_width":0,"signed":false},"name_hint":"numeric_later_transition","origin":{"instruction_result":{"instruction":5,"index":0}}},
    \\{"id":9,"function":1,"name_hint":"numeric_control","origin":{"block_parameter":{"block":2,"index":0}}},
    \\{"id":10,"function":1,"name_hint":"numeric_limit","origin":{"block_parameter":{"block":2,"index":1}}},
    \\{"id":11,"function":1,"name_hint":"numeric_step","origin":{"block_parameter":{"block":2,"index":2}}},
    \\{"id":12,"function":1,"type":{"kind":"boolean","bit_width":0,"signed":false},"name_hint":"numeric_initial_transition","origin":{"block_parameter":{"block":2,"index":3}}},
    \\{"id":13,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":"i","origin":{"block_parameter":{"block":3,"index":0}}},
    \\{"id":14,"function":1,"type":{"kind":"boolean","bit_width":0,"signed":false},"name_hint":"numeric_has_value","origin":{"instruction_result":{"instruction":6,"index":0}}},
    \\{"id":15,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":"numeric_normalized_limit","origin":{"instruction_result":{"instruction":6,"index":1}}},
    \\{"id":16,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":"numeric_normalized_step","origin":{"instruction_result":{"instruction":6,"index":2}}},
    \\{"id":17,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":"i","origin":{"instruction_result":{"instruction":6,"index":3}}},
    \\{"id":18,"function":1,"name_hint":"x","origin":{"instruction_result":{"instruction":15,"index":0}}},
    \\{"id":19,"function":0,"type":{"kind":"function","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":16,"index":0}}}]
    \\,"value_packs":[
    \\{"id":0,"function":0,"origin":{"varargs":0},"shape":{"prefix":[],"tail":"open"}}]
    \\,"places":[
    \\{"id":0,"function":1,"name_hint":"x","origin":{"local":0}}]
    \\,"solver_terms":[
    \\{"id":0,"sort":{"kind":"boolean","bit_width":0,"signed":false},"operation":{"value":12}},
    \\{"id":1,"sort":{"kind":"boolean","bit_width":0,"signed":false},"operation":{"value":14}},
    \\{"id":2,"sort":{"kind":"boolean","bit_width":0,"signed":false},"operation":{"logical_not":1}},
    \\{"id":3,"sort":{"kind":"boolean","bit_width":0,"signed":false},"operation":{"logical_not":0}}]
    \\,"constraints":[
    \\{"id":0,"predicate":0,"scope":{"edge":{"source":1,"kind":"jump","target":2}},"path_rewrites":[]},
    \\{"id":1,"predicate":1,"scope":{"edge":{"source":2,"kind":"branch_then","target":3}},"path_rewrites":[]},
    \\{"id":2,"predicate":2,"scope":{"edge":{"source":2,"kind":"branch_else","target":4}},"path_rewrites":[]},
    \\{"id":3,"predicate":3,"scope":{"edge":{"source":7,"kind":"jump","target":2}},"path_rewrites":[]},
    \\{"id":4,"predicate":3,"scope":{"edge":{"source":28,"kind":"jump","target":2}},"path_rewrites":[]},
    \\{"id":5,"predicate":3,"scope":{"edge":{"source":31,"kind":"jump","target":2}},"path_rewrites":[]}]
    \\}
;

/// The worker (function 1) of a numeric `for` whose body is a branch arm written in groups: the source frontend's lift,
/// resolved, of `for i = 1, n do` with `if c then repeat ... until true end` and `x = q`, the `repeat` holding an
/// `if p then if q then x = r; break end end`, five one-line `if`s, an `if q then if r then x = p; break end end` and
/// `x = i`.
const grouped_branch_arm_ir =
    \\{"schema_version":"lifter_ir_v1","program_id":"grouped-branch-arm","source_semantics":"luau","entry_function":0,"functions":[
    \\{"id":0,"name_hint":"chunk","lexical_parent":null,"parameters":[],"captures":[],"local_places":[],"blocks":[0],"entry_block":0,"is_variadic":true,"vararg_pack":0},
    \\{"id":1,"name_hint":"closure","lexical_parent":0,"parameters":[0,1,2,3,4],"captures":[],"local_places":[0],"blocks":[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39],"entry_block":1,"is_variadic":false,"vararg_pack":null}]
    \\,"blocks":[
    \\{"id":0,"function":0,"name_hint":"entry","parameters":[],"instructions":[18],"terminator":{"return_values":[21]}},
    \\{"id":1,"function":1,"name_hint":"entry","parameters":[],"instructions":[0,1,2,3,4,5],"terminator":{"jump":{"target":2,"arguments":[6,0,7,8]}}},
    \\{"id":2,"function":1,"name_hint":"numeric_for_header","parameters":[10,11,12,13],"instructions":[6],"terminator":{"branch":{"condition":15,"then_edge":{"target":3,"arguments":[18]},"else_edge":{"target":4,"arguments":[]}}}},
    \\{"id":3,"function":1,"name_hint":"numeric_for_body","parameters":[14],"instructions":[],"terminator":{"branch":{"condition":4,"then_edge":{"target":7,"arguments":[]},"else_edge":{"target":37,"arguments":[]}}}},
    \\{"id":4,"function":1,"name_hint":"numeric_for_exit","parameters":[],"instructions":[17],"terminator":{"return_values":[20]}},
    \\{"id":5,"function":1,"name_hint":"then","parameters":[],"instructions":[],"terminator":{"jump":{"target":7,"arguments":[]}}},
    \\{"id":6,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":37,"arguments":[]}}},
    \\{"id":7,"function":1,"name_hint":"repeat_body","parameters":[],"instructions":[],"terminator":{"branch":{"condition":1,"then_edge":{"target":10,"arguments":[]},"else_edge":{"target":15,"arguments":[]}}}},
    \\{"id":8,"function":1,"name_hint":"repeat_latch","parameters":[],"instructions":[15],"terminator":{"jump":{"target":37,"arguments":[]}}},
    \\{"id":9,"function":1,"name_hint":"repeat_exit","parameters":[],"instructions":[],"terminator":{"jump":{"target":37,"arguments":[]}}},
    \\{"id":10,"function":1,"name_hint":"then","parameters":[],"instructions":[],"terminator":{"branch":{"condition":2,"then_edge":{"target":12,"arguments":[]},"else_edge":{"target":15,"arguments":[]}}}},
    \\{"id":11,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":15,"arguments":[]}}},
    \\{"id":12,"function":1,"name_hint":"then","parameters":[],"instructions":[7],"terminator":{"jump":{"target":37,"arguments":[]}}},
    \\{"id":13,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":14,"arguments":[]}}},
    \\{"id":14,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"jump":{"target":15,"arguments":[]}}},
    \\{"id":15,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"branch":{"condition":2,"then_edge":{"target":16,"arguments":[]},"else_edge":{"target":18,"arguments":[]}}}},
    \\{"id":16,"function":1,"name_hint":"then","parameters":[],"instructions":[8],"terminator":{"jump":{"target":18,"arguments":[]}}},
    \\{"id":17,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":18,"arguments":[]}}},
    \\{"id":18,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"branch":{"condition":3,"then_edge":{"target":19,"arguments":[]},"else_edge":{"target":21,"arguments":[]}}}},
    \\{"id":19,"function":1,"name_hint":"then","parameters":[],"instructions":[9],"terminator":{"jump":{"target":21,"arguments":[]}}},
    \\{"id":20,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":21,"arguments":[]}}},
    \\{"id":21,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"branch":{"condition":1,"then_edge":{"target":22,"arguments":[]},"else_edge":{"target":24,"arguments":[]}}}},
    \\{"id":22,"function":1,"name_hint":"then","parameters":[],"instructions":[10],"terminator":{"jump":{"target":24,"arguments":[]}}},
    \\{"id":23,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":24,"arguments":[]}}},
    \\{"id":24,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"branch":{"condition":2,"then_edge":{"target":25,"arguments":[]},"else_edge":{"target":27,"arguments":[]}}}},
    \\{"id":25,"function":1,"name_hint":"then","parameters":[],"instructions":[11],"terminator":{"jump":{"target":27,"arguments":[]}}},
    \\{"id":26,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":27,"arguments":[]}}},
    \\{"id":27,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"branch":{"condition":3,"then_edge":{"target":28,"arguments":[]},"else_edge":{"target":30,"arguments":[]}}}},
    \\{"id":28,"function":1,"name_hint":"then","parameters":[],"instructions":[12],"terminator":{"jump":{"target":30,"arguments":[]}}},
    \\{"id":29,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":30,"arguments":[]}}},
    \\{"id":30,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"branch":{"condition":2,"then_edge":{"target":31,"arguments":[]},"else_edge":{"target":36,"arguments":[]}}}},
    \\{"id":31,"function":1,"name_hint":"then","parameters":[],"instructions":[],"terminator":{"branch":{"condition":3,"then_edge":{"target":33,"arguments":[]},"else_edge":{"target":36,"arguments":[]}}}},
    \\{"id":32,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":36,"arguments":[]}}},
    \\{"id":33,"function":1,"name_hint":"then","parameters":[],"instructions":[13],"terminator":{"jump":{"target":39,"arguments":[]}}},
    \\{"id":34,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":35,"arguments":[]}}},
    \\{"id":35,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"jump":{"target":36,"arguments":[]}}},
    \\{"id":36,"function":1,"name_hint":"join","parameters":[],"instructions":[14],"terminator":{"jump":{"target":8,"arguments":[]}}},
    \\{"id":37,"function":1,"name_hint":"join","parameters":[],"instructions":[16],"terminator":{"jump":{"target":2,"arguments":[18,16,17,9]}}},
    \\{"id":38,"function":1,"name_hint":"repeat_exit","parameters":[],"instructions":[],"terminator":{"jump":{"target":39,"arguments":[]}}},
    \\{"id":39,"function":1,"name_hint":"join","parameters":[],"instructions":[19],"terminator":{"jump":{"target":2,"arguments":[18,16,17,9]}}}]
    \\,"instructions":[
    \\{"id":0,"block":1,"operation":{"constant":{"integer":"0"}},"results":[5],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":1,"block":1,"operation":{"place_write":{"place":0,"value":5}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":2,"block":1,"operation":{"constant":{"integer":"1"}},"results":[6],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":3,"block":1,"operation":{"constant":{"integer":"1"}},"results":[7],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":4,"block":1,"operation":{"constant":{"boolean":true}},"results":[8],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":5,"block":1,"operation":{"constant":{"boolean":false}},"results":[9],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":6,"block":2,"operation":{"numeric_for_next":{"control":10,"limit":11,"step":12,"initial":13}},"results":[15,16,17,18],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":true,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":7,"block":12,"operation":{"place_write":{"place":0,"value":3}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":8,"block":16,"operation":{"place_write":{"place":0,"value":1}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":9,"block":19,"operation":{"place_write":{"place":0,"value":2}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":10,"block":22,"operation":{"place_write":{"place":0,"value":3}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":11,"block":25,"operation":{"place_write":{"place":0,"value":3}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":12,"block":28,"operation":{"place_write":{"place":0,"value":1}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":13,"block":33,"operation":{"place_write":{"place":0,"value":1}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":14,"block":36,"operation":{"place_write":{"place":0,"value":14}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":15,"block":8,"operation":{"constant":{"boolean":true}},"results":[19],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":16,"block":37,"operation":{"place_write":{"place":0,"value":2}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":17,"block":4,"operation":{"place_read":0},"results":[20],"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":18,"block":0,"operation":{"make_closure":{"function":1,"bindings":[]}},"results":[21],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":19,"block":39,"operation":{"place_write":{"place":0,"value":2}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}}]
    \\,"values":[
    \\{"id":0,"function":1,"name_hint":"n","origin":{"parameter":0}},
    \\{"id":1,"function":1,"name_hint":"p","origin":{"parameter":1}},
    \\{"id":2,"function":1,"name_hint":"q","origin":{"parameter":2}},
    \\{"id":3,"function":1,"name_hint":"r","origin":{"parameter":3}},
    \\{"id":4,"function":1,"name_hint":"c","origin":{"parameter":4}},
    \\{"id":5,"function":1,"type":{"kind":"integer","bit_width":64,"signed":true},"name_hint":"x","origin":{"instruction_result":{"instruction":0,"index":0}}},
    \\{"id":6,"function":1,"type":{"kind":"integer","bit_width":64,"signed":true},"name_hint":"numeric_initial","origin":{"instruction_result":{"instruction":2,"index":0}}},
    \\{"id":7,"function":1,"type":{"kind":"integer","bit_width":64,"signed":true},"name_hint":"numeric_step","origin":{"instruction_result":{"instruction":3,"index":0}}},
    \\{"id":8,"function":1,"type":{"kind":"boolean","bit_width":0,"signed":false},"name_hint":"numeric_initial_transition","origin":{"instruction_result":{"instruction":4,"index":0}}},
    \\{"id":9,"function":1,"type":{"kind":"boolean","bit_width":0,"signed":false},"name_hint":"numeric_later_transition","origin":{"instruction_result":{"instruction":5,"index":0}}},
    \\{"id":10,"function":1,"name_hint":"numeric_control","origin":{"block_parameter":{"block":2,"index":0}}},
    \\{"id":11,"function":1,"name_hint":"numeric_limit","origin":{"block_parameter":{"block":2,"index":1}}},
    \\{"id":12,"function":1,"name_hint":"numeric_step","origin":{"block_parameter":{"block":2,"index":2}}},
    \\{"id":13,"function":1,"type":{"kind":"boolean","bit_width":0,"signed":false},"name_hint":"numeric_initial_transition","origin":{"block_parameter":{"block":2,"index":3}}},
    \\{"id":14,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":"i","origin":{"block_parameter":{"block":3,"index":0}}},
    \\{"id":15,"function":1,"type":{"kind":"boolean","bit_width":0,"signed":false},"name_hint":"numeric_has_value","origin":{"instruction_result":{"instruction":6,"index":0}}},
    \\{"id":16,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":"numeric_normalized_limit","origin":{"instruction_result":{"instruction":6,"index":1}}},
    \\{"id":17,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":"numeric_normalized_step","origin":{"instruction_result":{"instruction":6,"index":2}}},
    \\{"id":18,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":"i","origin":{"instruction_result":{"instruction":6,"index":3}}},
    \\{"id":19,"function":1,"type":{"kind":"boolean","bit_width":0,"signed":false},"name_hint":"until_condition","origin":{"instruction_result":{"instruction":15,"index":0}}},
    \\{"id":20,"function":1,"name_hint":"x","origin":{"instruction_result":{"instruction":17,"index":0}}},
    \\{"id":21,"function":0,"type":{"kind":"function","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":18,"index":0}}}]
    \\,"value_packs":[
    \\{"id":0,"function":0,"origin":{"varargs":0},"shape":{"prefix":[],"tail":"open"}}]
    \\,"places":[
    \\{"id":0,"function":1,"name_hint":"x","origin":{"local":0}}]
    \\,"solver_terms":[
    \\{"id":0,"sort":{"kind":"boolean","bit_width":0,"signed":false},"operation":{"value":19}},
    \\{"id":1,"sort":{"kind":"boolean","bit_width":0,"signed":false},"operation":{"value":13}},
    \\{"id":2,"sort":{"kind":"boolean","bit_width":0,"signed":false},"operation":{"value":15}},
    \\{"id":3,"sort":{"kind":"boolean","bit_width":0,"signed":false},"operation":{"logical_not":2}},
    \\{"id":4,"sort":{"kind":"boolean","bit_width":0,"signed":false},"operation":{"logical_not":1}}]
    \\,"constraints":[
    \\{"id":0,"predicate":1,"scope":{"edge":{"source":1,"kind":"jump","target":2}},"path_rewrites":[]},
    \\{"id":1,"predicate":2,"scope":{"edge":{"source":2,"kind":"branch_then","target":3}},"path_rewrites":[]},
    \\{"id":2,"predicate":3,"scope":{"edge":{"source":2,"kind":"branch_else","target":4}},"path_rewrites":[]},
    \\{"id":3,"predicate":4,"scope":{"edge":{"source":37,"kind":"jump","target":2}},"path_rewrites":[]},
    \\{"id":4,"predicate":4,"scope":{"edge":{"source":39,"kind":"jump","target":2}},"path_rewrites":[]}]
    \\,"queries":[
    \\{"id":0,"kind":"prove_true","assumptions":[],"path_rewrites":[],"goal":0}]
    \\,"unsat_cores":[
    \\{"id":0,"query":0,"constraints":[]}]
    \\,"certificates":[
    \\{"id":0,"query":0,"engine":"internal_facts","resolution":"proved","certificate_digest":"sha256:lifter-proof-v9:473f602a4f3cbd3f455daac75ca0d3e1610763240ce95644e84cd94ff2e7cfed","model":null,"unsat_core":0}]
    \\,"edge_rewrites":[
    \\{"id":0,"source":38,"kind":"jump","from":{"target":37,"arguments":[]},"to":{"target":39,"arguments":[]},"rule":"node_split","certificate":null,"node_split_group":0},
    \\{"id":1,"source":33,"kind":"jump","from":{"target":9,"arguments":[]},"to":{"target":38,"arguments":[]},"rule":"node_split","certificate":null,"node_split_group":0},
    \\{"id":2,"source":3,"kind":"branch_then","from":{"target":5,"arguments":[]},"to":{"target":7,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":3,"source":3,"kind":"branch_else","from":{"target":6,"arguments":[]},"to":{"target":37,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":4,"source":8,"kind":"jump","from":{"target":9,"arguments":[]},"to":{"target":37,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":5,"source":12,"kind":"jump","from":{"target":9,"arguments":[]},"to":{"target":37,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":6,"source":7,"kind":"branch_else","from":{"target":11,"arguments":[]},"to":{"target":15,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":7,"source":10,"kind":"branch_else","from":{"target":13,"arguments":[]},"to":{"target":14,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":8,"source":10,"kind":"branch_else","from":{"target":14,"arguments":[]},"to":{"target":15,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":9,"source":15,"kind":"branch_else","from":{"target":17,"arguments":[]},"to":{"target":18,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":10,"source":18,"kind":"branch_else","from":{"target":20,"arguments":[]},"to":{"target":21,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":11,"source":21,"kind":"branch_else","from":{"target":23,"arguments":[]},"to":{"target":24,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":12,"source":24,"kind":"branch_else","from":{"target":26,"arguments":[]},"to":{"target":27,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":13,"source":27,"kind":"branch_else","from":{"target":29,"arguments":[]},"to":{"target":30,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":14,"source":30,"kind":"branch_else","from":{"target":32,"arguments":[]},"to":{"target":36,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":15,"source":31,"kind":"branch_else","from":{"target":34,"arguments":[]},"to":{"target":35,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":16,"source":31,"kind":"branch_else","from":{"target":35,"arguments":[]},"to":{"target":36,"arguments":[]},"rule":"forwarding_jump","certificate":null},
    \\{"id":17,"source":33,"kind":"jump","from":{"target":38,"arguments":[]},"to":{"target":39,"arguments":[]},"rule":"forwarding_jump","certificate":null}]
    \\,"obligations":[
    \\{"id":0,"kind":"control_structure","subject":{"control_branch":{"block":8,"branch":{"condition":19,"then_edge":{"target":9,"arguments":[]},"else_edge":{"target":7,"arguments":[]}}}},"status":"discharged","blocks_profile":"readable_luau","detail":"pre-normalization exact branch truthiness fact","requirement":{"kind":"prove_true","predicate":0},"query":0,"certificate":0}]
    \\}
;

/// The workers of the native-loop register tests: worker(f, observe, marker, first, last, stride), function 1,
/// returned by the chunk; every loop runs over first, last and stride.
const NativeLoopShape = enum {
    /// Nested native numeric loops whose exhaustion edges pass no value.
    numeric_chain,
    /// The same loops, each exhaustion edge passing the outer value to an exit-block parameter that the exit block
    /// observes, so each loop declares a completion local before its `for`.
    numeric_completion_chain,
    /// Nested one-name native generic loops whose exhaustion edges pass no value.
    generic_chain,
    /// The generic loops with completion locals.
    generic_completion_chain,
    /// Two native numeric loops with completion locals per level, one after the other in one block: a side loop,
    /// then the loop whose body holds the next level.
    completion_tower,
    /// Nested one-shot native numeric loops (no latch): each header is entered by a jump from the outer level's body,
    /// so its four parameters are aliases, and each body joins the header's exit target.
    one_shot_chain,
};

/// Appends IR entities in creation order, as the LifterIR builder does, so the worker of a shape the native-loop
/// conformance builder also writes gets the same ids.
const NativeLoopBuilder = struct {
    allocator: std.mem.Allocator,
    evidence: []const ir.EvidenceId,
    blocks: []ir.Block,
    instructions: []ir.Instruction,
    values: []ir.Value,
    block_count: usize = 0,
    instruction_count: usize = 0,
    value_count: usize = 0,

    fn block(self: *NativeLoopBuilder, function: ir.FunctionId) ir.BlockId {
        const id = ir.BlockId.fromIndex(self.block_count);
        self.blocks[self.block_count] = .{ .id = id, .function = function, .terminator = .unreachable_block, .evidence = self.evidence };
        self.block_count += 1;
        return id;
    }

    fn value(self: *NativeLoopBuilder, function: ir.FunctionId, value_type: ir.ValueType, origin: ir.ValueOrigin) ir.ValueId {
        const id = ir.ValueId.fromIndex(self.value_count);
        self.values[self.value_count] = .{ .id = id, .function = function, .type = value_type, .origin = origin };
        self.value_count += 1;
        return id;
    }

    fn parameters(self: *NativeLoopBuilder, block_id: ir.BlockId, types: []const ir.ValueType) std.mem.Allocator.Error![]const ir.ValueId {
        const ids = try self.allocator.alloc(ir.ValueId, types.len);
        const function = self.blocks[block_id.index()].function;
        for (types, 0..) |value_type, index| {
            ids[index] = self.value(function, value_type, .{ .block_parameter = .{ .block = block_id, .index = @intCast(index) } });
        }
        self.blocks[block_id.index()].parameters = ids;
        return ids;
    }

    fn instruction(
        self: *NativeLoopBuilder,
        block_id: ir.BlockId,
        operation: ir.Operation,
        result_types: []const ir.ValueType,
        effects: ir.EffectSummary,
    ) std.mem.Allocator.Error![]const ir.ValueId {
        const id = ir.InstructionId.fromIndex(self.instruction_count);
        self.instruction_count += 1;
        const target = &self.blocks[block_id.index()];
        const results = try self.allocator.alloc(ir.ValueId, result_types.len);
        for (result_types, 0..) |value_type, index| {
            results[index] = self.value(target.function, value_type, .{ .instruction_result = .{ .instruction = id, .index = @intCast(index) } });
        }
        self.instructions[id.index()] = .{ .id = id, .block = block_id, .operation = operation, .results = results, .effects = effects, .evidence = self.evidence };
        const listed = try self.allocator.alloc(ir.InstructionId, target.instructions.len + 1);
        @memcpy(listed[0..target.instructions.len], target.instructions);
        listed[target.instructions.len] = id;
        target.instructions = listed;
        return results;
    }

    /// `callee(arguments)` with `result_count` dynamic results (0 or 1).
    fn call(self: *NativeLoopBuilder, block_id: ir.BlockId, callee: ir.ValueId, arguments: []const ir.ValueId, result_count: u16) std.mem.Allocator.Error![]const ir.ValueId {
        const operation: ir.Operation = .{ .call = .{
            .callee = callee,
            .arguments = try self.allocator.dupe(ir.ValueId, arguments),
            .result_arity = .{ .fixed = result_count },
        } };
        const result_types: []const ir.ValueType = if (result_count == 0) &.{} else &.{.dynamic};
        return self.instruction(block_id, operation, result_types, .dynamic_call);
    }

    fn jump(self: *NativeLoopBuilder, source: ir.BlockId, target: ir.BlockId, arguments: []const ir.ValueId) std.mem.Allocator.Error!void {
        self.blocks[source.index()].terminator = .{ .jump = .{ .target = target, .arguments = try self.allocator.dupe(ir.ValueId, arguments) } };
    }

    fn branch(
        self: *NativeLoopBuilder,
        source: ir.BlockId,
        condition: ir.ValueId,
        then_target: ir.BlockId,
        then_arguments: []const ir.ValueId,
        else_target: ir.BlockId,
        else_arguments: []const ir.ValueId,
    ) std.mem.Allocator.Error!void {
        self.blocks[source.index()].terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = then_target, .arguments = try self.allocator.dupe(ir.ValueId, then_arguments) },
            .else_edge = .{ .target = else_target, .arguments = try self.allocator.dupe(ir.ValueId, else_arguments) },
        } };
    }
};

/// One native loop level: the header block (four parameters and the transition), the body block with the loop
/// variable, and the transition's results (the first decides between the body and the exit).
const NativeLoopHeader = struct {
    header: ir.BlockId,
    body: ir.BlockId,
    index: ir.ValueId,
    results: []const ir.ValueId,
};

const NativeLoopWorker = struct {
    builder: *NativeLoopBuilder,
    shape: NativeLoopShape,
    depth: usize,
    worker: ir.FunctionId,
    observe: ir.ValueId,
    first: ir.ValueId,
    last: ir.ValueId,
    stride: ir.ValueId,
    initial_transition: ir.ValueId,
    later_transition: ?ir.ValueId,

    fn header(self: *const NativeLoopWorker, generic: bool) std.mem.Allocator.Error!NativeLoopHeader {
        const builder = self.builder;
        const header_block = builder.block(self.worker);
        const state_type: ir.ValueType = if (generic) .dynamic else .number;
        const state = try builder.parameters(header_block, &.{ state_type, state_type, state_type, .boolean });
        const body = builder.block(self.worker);
        const index = (try builder.parameters(body, &.{state_type}))[0];
        const results = if (generic)
            try builder.instruction(header_block, .{ .generic_for_next = .{
                .iterator = state[0],
                .state = state[1],
                .control = state[2],
                .initial = state[3],
                .variable_count = 1,
            } }, &.{ .boolean, .dynamic, .dynamic, .dynamic }, .generic_for_next)
        else
            try builder.instruction(header_block, .{ .numeric_for_next = .{
                .control = state[0],
                .limit = state[1],
                .step = state[2],
                .initial = state[3],
            } }, &.{ .boolean, .number, .number, .number }, .numeric_for_next);
        return .{ .header = header_block, .body = body, .index = index, .results = results };
    }

    /// The latch of a native loop passes the transition's state back to the header.
    fn latch(self: *const NativeLoopWorker, loop: NativeLoopHeader, generic: bool) std.mem.Allocator.Error!ir.BlockId {
        const builder = self.builder;
        const latch_block = builder.block(self.worker);
        if (generic) {
            try builder.jump(latch_block, loop.header, &.{ loop.results[1], loop.results[2], loop.results[3], self.later_transition.? });
        } else {
            try builder.jump(latch_block, loop.header, &.{ loop.results[3], loop.results[1], loop.results[2], self.later_transition.? });
        }
        return latch_block;
    }

    /// Level k of a chain: one native loop entered from `preheader`, whose body holds level k + 1, and whose exit
    /// block jumps to `after`.
    fn chainLevel(self: *const NativeLoopWorker, k: usize, preheader: ir.BlockId, after: ir.BlockId, outer: ir.ValueId) std.mem.Allocator.Error!void {
        const builder = self.builder;
        const generic = self.shape == .generic_chain or self.shape == .generic_completion_chain;
        const completion = self.shape == .numeric_completion_chain or self.shape == .generic_completion_chain;
        const hold_exit = builder.block(self.worker);
        const exit_marker: ?ir.ValueId = if (completion) (try builder.parameters(hold_exit, &.{.dynamic}))[0] else null;
        const loop = try self.header(generic);
        try builder.jump(preheader, loop.header, &.{ self.first, self.last, self.stride, self.initial_transition });
        const exit_arguments: []const ir.ValueId = if (completion) &.{outer} else &.{};
        try builder.branch(loop.header, loop.results[0], loop.body, &.{loop.results[3]}, hold_exit, exit_arguments);
        const latch_block = try self.latch(loop, generic);
        if (k < self.depth) {
            try self.chainLevel(k + 1, loop.body, latch_block, loop.index);
        } else {
            _ = try builder.call(loop.body, self.observe, &.{loop.index}, 0);
            try builder.jump(loop.body, latch_block, &.{});
        }
        if (exit_marker) |marker| _ = try builder.call(hold_exit, self.observe, &.{marker}, 0);
        try builder.jump(hold_exit, after, &.{});
    }

    /// Level k of the tower: a side loop over the level, then the loop whose body holds level k + 1, each passing the
    /// outer value to its exit block's parameter.
    fn towerLevel(self: *const NativeLoopWorker, k: usize, preheader: ir.BlockId, after: ir.BlockId, outer: ir.ValueId) std.mem.Allocator.Error!void {
        const builder = self.builder;
        const side_exit = builder.block(self.worker);
        const side_marker = (try builder.parameters(side_exit, &.{.dynamic}))[0];
        const side = try self.header(false);
        try builder.jump(preheader, side.header, &.{ self.first, self.last, self.stride, self.initial_transition });
        try builder.branch(side.header, side.results[0], side.body, &.{side.results[3]}, side_exit, &.{outer});
        const side_latch = try self.latch(side, false);
        _ = try builder.call(side.body, self.observe, &.{side.index}, 0);
        try builder.jump(side.body, side_latch, &.{});
        _ = try builder.call(side_exit, self.observe, &.{side_marker}, 0);
        const hold_exit = builder.block(self.worker);
        const hold_marker = (try builder.parameters(hold_exit, &.{.dynamic}))[0];
        const hold = try self.header(false);
        try builder.jump(side_exit, hold.header, &.{ self.first, self.last, self.stride, self.initial_transition });
        try builder.branch(hold.header, hold.results[0], hold.body, &.{hold.results[3]}, hold_exit, &.{outer});
        const hold_latch = try self.latch(hold, false);
        if (k < self.depth) {
            try self.towerLevel(k + 1, hold.body, hold_latch, hold.index);
        } else {
            _ = try builder.call(hold.body, self.observe, &.{hold.index}, 0);
            try builder.jump(hold.body, hold_latch, &.{});
        }
        _ = try builder.call(hold_exit, self.observe, &.{hold_marker}, 0);
        try builder.jump(hold_exit, after, &.{});
    }

    /// Level k of the one-shot chain: a header entered by a jump from `preheader` that leaves to `join`; its body
    /// enters level k + 1, whose own join jumps to `join`.
    fn oneShotLevel(self: *const NativeLoopWorker, k: usize, preheader: ir.BlockId, join: ir.BlockId) std.mem.Allocator.Error!void {
        const builder = self.builder;
        const loop = try self.header(false);
        try builder.jump(preheader, loop.header, &.{ self.first, self.last, self.stride, self.initial_transition });
        try builder.branch(loop.header, loop.results[0], loop.body, &.{loop.results[3]}, join, &.{});
        if (k < self.depth) {
            const inner_join = builder.block(self.worker);
            try self.oneShotLevel(k + 1, loop.body, inner_join);
            try builder.jump(inner_join, join, &.{});
        } else {
            _ = try builder.call(loop.body, self.observe, &.{loop.index}, 0);
            try builder.jump(loop.body, join, &.{});
        }
    }
};

fn nativeLoopProgram(allocator: std.mem.Allocator, shape: NativeLoopShape, depth: usize) std.mem.Allocator.Error!ir.Program {
    const capacity = 32 * depth + 32;
    var builder: NativeLoopBuilder = .{
        .allocator = allocator,
        .evidence = try allocator.dupe(ir.EvidenceId, &.{ir.EvidenceId.fromIndex(0)}),
        .blocks = try allocator.alloc(ir.Block, capacity),
        .instructions = try allocator.alloc(ir.Instruction, capacity),
        .values = try allocator.alloc(ir.Value, capacity),
    };
    const chunk = ir.FunctionId.fromIndex(0);
    const worker = ir.FunctionId.fromIndex(1);
    const chunk_entry = builder.block(chunk);
    const f = builder.value(worker, .function, .{ .parameter = 0 });
    const observe = builder.value(worker, .function, .{ .parameter = 1 });
    const marker = builder.value(worker, .dynamic, .{ .parameter = 2 });
    const first = builder.value(worker, .number, .{ .parameter = 3 });
    const last = builder.value(worker, .number, .{ .parameter = 4 });
    const stride = builder.value(worker, .number, .{ .parameter = 5 });
    const entry = builder.block(worker);

    const initial_transition = (try builder.instruction(entry, .{ .constant = .{ .boolean = true } }, &.{.boolean}, .pure))[0];
    const later_transition: ?ir.ValueId = if (shape == .one_shot_chain)
        null
    else
        (try builder.instruction(entry, .{ .constant = .{ .boolean = false } }, &.{.boolean}, .pure))[0];
    const seed = (try builder.call(entry, f, &.{marker}, 1))[0];
    const loops: NativeLoopWorker = .{
        .builder = &builder,
        .shape = shape,
        .depth = depth,
        .worker = worker,
        .observe = observe,
        .first = first,
        .last = last,
        .stride = stride,
        .initial_transition = initial_transition,
        .later_transition = later_transition,
    };
    if (shape == .one_shot_chain) _ = try builder.call(entry, observe, &.{seed}, 0);
    const done = builder.block(worker);
    switch (shape) {
        .numeric_chain, .numeric_completion_chain, .generic_chain, .generic_completion_chain => try loops.chainLevel(1, entry, done, seed),
        .completion_tower => try loops.towerLevel(1, entry, done, seed),
        .one_shot_chain => try loops.oneShotLevel(1, entry, done),
    }
    builder.blocks[done.index()].terminator = .{ .return_values = try allocator.dupe(ir.ValueId, &.{marker}) };

    const exported = try builder.instruction(chunk_entry, .{ .function_ref = worker }, &.{.function}, .pure);
    builder.blocks[chunk_entry.index()].terminator = .{ .return_values = exported };
    const block_ids = try allocator.alloc(ir.BlockId, builder.block_count);
    for (block_ids, 0..) |*block_id, index| block_id.* = ir.BlockId.fromIndex(index);
    const functions = try allocator.dupe(ir.Function, &.{
        .{ .id = chunk, .blocks = block_ids[0..1], .entry_block = chunk_entry, .evidence = builder.evidence },
        .{
            .id = worker,
            .parameters = try allocator.dupe(ir.ValueId, &.{ f, observe, marker, first, last, stride }),
            .blocks = block_ids[1..],
            .entry_block = entry,
            .evidence = builder.evidence,
        },
    });
    const evidence = try allocator.dupe(ir.Evidence, &.{.{
        .id = ir.EvidenceId.fromIndex(0),
        .kind = .dynamic_fixture,
        .locator = "fixture:nested-native-loops",
    }});
    return .{
        .program_id = "nested-native-loops",
        .entry_function = chunk,
        .functions = functions,
        .blocks = builder.blocks[0..builder.block_count],
        .instructions = builder.instructions[0..builder.instruction_count],
        .values = builder.values[0..builder.value_count],
        .evidence = evidence,
    };
}

/// The register certificate of `nativeLoopProgram`'s worker on the per-function path of `validatePrepared`, as the
/// nested_repeat test runs it.
fn nativeLoopPressure(shape: NativeLoopShape, depth: usize, target: luau_runtime.Target) !Pressure {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const built = try nativeLoopProgram(arena.allocator(), shape, depth);
    const program = try lexical_transfer.prepareInArena(arena.allocator(), &built);
    var readable = try readable_scope.Scope.init(allocator, &program);
    defer readable.deinit();
    var emission = try emission_planning.Plan.init(allocator, &program, target);
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
    return maximumPressure(allocator, &program, &readable, &emission, &scopes, function, base, structured.root);
}

test "nested native loops count their for frames and completion locals under value storage" {
    // Fourteen levels hold more than 120 candidate values, so the worker keeps its values in storage: the header
    // parameters are storage values, and the certificate counts the six parameters, the storage table and one loop
    // variable per level (21 locals) whatever each loop holds. A native numeric `for` also holds its limit and step,
    // a one-name generic `for` its generator, state, control and a second variable slot, and a loop whose exit edge
    // writes a parameter declares a completion local before its `for`, live to the end of the enclosing block. Each
    // total equals the pinned compiler's register count for the emitted text (51, 65, 79 and 93).
    var pressure = try nativeLoopPressure(.numeric_chain, 14, .standard_luau);
    try std.testing.expectEqual(@as(usize, 21), pressure.locals);
    try std.testing.expectEqual(@as(usize, 51), pressure.total);
    pressure = try nativeLoopPressure(.numeric_completion_chain, 14, .standard_luau);
    try std.testing.expectEqual(@as(usize, 35), pressure.locals);
    try std.testing.expectEqual(@as(usize, 65), pressure.total);
    pressure = try nativeLoopPressure(.generic_chain, 14, .standard_luau);
    try std.testing.expectEqual(@as(usize, 21), pressure.locals);
    try std.testing.expectEqual(@as(usize, 79), pressure.total);
    pressure = try nativeLoopPressure(.generic_completion_chain, 14, .standard_luau);
    try std.testing.expectEqual(@as(usize, 35), pressure.locals);
    try std.testing.expectEqual(@as(usize, 93), pressure.total);
    // Two loops per level declare their completion locals in one block, so both are live at once: 7 + 14 loop
    // variables + 14 completion locals. The compiler needs 44 registers; the certificate also counts each side loop's
    // variable through its whole block, after its loop has ended.
    pressure = try nativeLoopPressure(.completion_tower, 7, .standard_luau);
    try std.testing.expectEqual(@as(usize, 35), pressure.locals);
    try std.testing.expectEqual(@as(usize, 51), pressure.total);
}

test "a one-name generic loop with a completion local needs one register beyond its header parameters" {
    // In direct locals each loop's four header parameters are counted locals although no line declares them (the
    // `for` holds the loop state). They cover a numeric loop's limit, step and completion local, but a one-name
    // generic loop with a completion local needs five registers beyond its loop variable: one more per level. The
    // compiler needs 79 registers for the generic chain and 59 for the numeric one.
    var pressure = try nativeLoopPressure(.generic_completion_chain, 10, .direct_locals_luau);
    try std.testing.expectEqual(@as(usize, 69), pressure.locals);
    try std.testing.expectEqual(@as(usize, 81), pressure.total);
    pressure = try nativeLoopPressure(.numeric_completion_chain, 10, .direct_locals_luau);
    try std.testing.expectEqual(@as(usize, 69), pressure.locals);
    try std.testing.expectEqual(@as(usize, 71), pressure.total);
}

test "nested one-shot native loops count their for frames when the header parameters are aliases" {
    // Each one-shot header is entered by a jump, so its four parameters are aliases of the jump's arguments and get
    // no value scope: the certificate counts the six parameters, the initial-transition constant and one loop
    // variable per level (17 locals), and nothing covers the limit and step each `for` holds, with or without value
    // storage. The compiler needs 38 registers.
    const pressure = try nativeLoopPressure(.one_shot_chain, 10, .direct_locals_luau);
    try std.testing.expectEqual(@as(usize, 17), pressure.locals);
    try std.testing.expectEqual(@as(usize, 39), pressure.total);
}

/// The register certificate of one function of a program written out as LifterIR JSON, one entity per line, on the
/// per-function path of `validatePrepared` in the standard target under the automatic strategy, as the nested_repeat
/// test runs it.
fn writtenProgramPressure(program_json: []const u8, function_index: usize) !Pressure {
    const allocator = std.testing.allocator;
    const parsed = try std.json.parseFromSlice(ir.Program, allocator, program_json, .{
        .allocate = .alloc_always,
        .ignore_unknown_fields = true,
    });
    defer parsed.deinit();
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const program = try lexical_transfer.prepareInArena(arena.allocator(), &parsed.value);
    var readable = try readable_scope.Scope.init(allocator, &program);
    defer readable.deinit();
    var emission = try emission_planning.Plan.init(allocator, &program, .standard_luau);
    defer emission.deinit();
    const function = program.functions[function_index];
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
    return maximumPressure(allocator, &program, &readable, &emission, &scopes, function, base, structured.root);
}

test "a branch composition written in a call argument is charged as luau-compile builds it" {
    // Each worker (function 1, five parameters a, b, c, f, g) is the source frontend's lift, resolved, of a function
    // whose one statement the emitter writes back as it reads; each total is the register count luau-compile gives the
    // emitted text at -O0 and at the default level. The composition is built in the call's third slot: `c` is tested
    // there and the arm's call or constructor is built from that slot.
    // `g(a, c and f(a, b, a, b))`: g and a, then the five registers of the call: 12.
    try std.testing.expectEqual(@as(usize, 12), (try writtenProgramPressure(and_call_argument_ir, 1)).total);
    // `g(a, if c then f(a, b, a, b, a, b) else a)`: the then arm's call holds seven registers from the slot: 14.
    try std.testing.expectEqual(@as(usize, 14), (try writtenProgramPressure(if_call_argument_ir, 1)).total);
    // `g(a, if c then { a, b, a, b, a, b, a, b } else a)`: the table and its eight items from the slot: 16.
    try std.testing.expectEqual(@as(usize, 16), (try writtenProgramPressure(if_constructor_argument_ir, 1)).total);
}

test "a wrapped loop body's until-true literal is charged above the body's locals" {
    // The worker (function 1) of a `while` loop whose body declares a captured local `z` and continues from two
    // nested `if`s is written as `repeat ... until true` around the body, with the pass's escape flag declared before it.
    // luau-compile builds the `true` in a register above every local the body declared: the three parameters, `x`,
    // `i`, the flag and `z` hold seven registers and the literal is the eighth (-O0; the default level reads it as a
    // constant and needs seven).
    try std.testing.expectEqual(@as(usize, 8), (try writtenProgramPressure(wrapped_body_local_ir, 1)).total);
}

/// The source frontend's lift, resolved, of `return function(a, b, c, f, g) g(a, c and f(a, b, a, b)) end`.
const and_call_argument_ir =
    \\{"schema_version":"lifter_ir_v1","program_id":"and-call-argument","source_semantics":"luau","entry_function":0,"functions":[
    \\{"id":0,"name_hint":"chunk","lexical_parent":null,"parameters":[],"captures":[],"local_places":[],"blocks":[0],"entry_block":0,"is_variadic":true,"vararg_pack":0},
    \\{"id":1,"name_hint":"closure","lexical_parent":0,"parameters":[0,1,2,3,4],"captures":[],"local_places":[],"blocks":[1,2,3,4],"entry_block":1,"is_variadic":false,"vararg_pack":null}]
    \\,"blocks":[
    \\{"id":0,"function":0,"name_hint":"entry","parameters":[],"instructions":[2],"terminator":{"return_values":[7]}},
    \\{"id":1,"function":1,"name_hint":"entry","parameters":[],"instructions":[],"terminator":{"branch":{"condition":2,"then_edge":{"target":2,"arguments":[]},"else_edge":{"target":3,"arguments":[]}}}},
    \\{"id":2,"function":1,"name_hint":"logical_right","parameters":[],"instructions":[0],"terminator":{"jump":{"target":4,"arguments":[6]}}},
    \\{"id":3,"function":1,"name_hint":"logical_short","parameters":[],"instructions":[],"terminator":{"jump":{"target":4,"arguments":[2]}}},
    \\{"id":4,"function":1,"name_hint":"logical_join","parameters":[5],"instructions":[1],"terminator":{"return_values":[]}}]
    \\,"instructions":[
    \\{"id":0,"block":2,"operation":{"call":{"callee":3,"arguments":[0,1,0,1],"argument_pack":null,"result_arity":{"fixed":1}}},"results":[6],"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true}},
    \\{"id":1,"block":4,"operation":{"call":{"callee":4,"arguments":[0,5],"argument_pack":null,"result_arity":{"fixed":0}}},"results":[],"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true}},
    \\{"id":2,"block":0,"operation":{"make_closure":{"function":1,"bindings":[]}},"results":[7],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}}]
    \\,"values":[
    \\{"id":0,"function":1,"name_hint":"a","origin":{"parameter":0}},
    \\{"id":1,"function":1,"name_hint":"b","origin":{"parameter":1}},
    \\{"id":2,"function":1,"name_hint":"c","origin":{"parameter":2}},
    \\{"id":3,"function":1,"name_hint":"f","origin":{"parameter":3}},
    \\{"id":4,"function":1,"name_hint":"g","origin":{"parameter":4}},
    \\{"id":5,"function":1,"name_hint":"logical_result","origin":{"block_parameter":{"block":4,"index":0}}},
    \\{"id":6,"function":1,"name_hint":"call_result","origin":{"instruction_result":{"instruction":0,"index":0}}},
    \\{"id":7,"function":0,"type":{"kind":"function","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":2,"index":0}}}]
    \\,"value_packs":[
    \\{"id":0,"function":0,"origin":{"varargs":0},"shape":{"prefix":[],"tail":"open"}}]
    \\}
;

/// The source frontend's lift, resolved, of `return function(a, b, c, f, g) g(a, if c then f(a, b, a, b, a, b) else a) end`.
const if_call_argument_ir =
    \\{"schema_version":"lifter_ir_v1","program_id":"if-call-argument","source_semantics":"luau","entry_function":0,"functions":[
    \\{"id":0,"name_hint":"chunk","lexical_parent":null,"parameters":[],"captures":[],"local_places":[],"blocks":[0],"entry_block":0,"is_variadic":true,"vararg_pack":0},
    \\{"id":1,"name_hint":"closure","lexical_parent":0,"parameters":[0,1,2,3,4],"captures":[],"local_places":[],"blocks":[1,2,3,4],"entry_block":1,"is_variadic":false,"vararg_pack":null}]
    \\,"blocks":[
    \\{"id":0,"function":0,"name_hint":"entry","parameters":[],"instructions":[2],"terminator":{"return_values":[7]}},
    \\{"id":1,"function":1,"name_hint":"entry","parameters":[],"instructions":[],"terminator":{"branch":{"condition":2,"then_edge":{"target":2,"arguments":[]},"else_edge":{"target":3,"arguments":[]}}}},
    \\{"id":2,"function":1,"name_hint":"if_value_true","parameters":[],"instructions":[0],"terminator":{"jump":{"target":4,"arguments":[6]}}},
    \\{"id":3,"function":1,"name_hint":"if_value_false","parameters":[],"instructions":[],"terminator":{"jump":{"target":4,"arguments":[0]}}},
    \\{"id":4,"function":1,"name_hint":"if_value_join","parameters":[5],"instructions":[1],"terminator":{"return_values":[]}}]
    \\,"instructions":[
    \\{"id":0,"block":2,"operation":{"call":{"callee":3,"arguments":[0,1,0,1,0,1],"argument_pack":null,"result_arity":{"fixed":1}}},"results":[6],"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true}},
    \\{"id":1,"block":4,"operation":{"call":{"callee":4,"arguments":[0,5],"argument_pack":null,"result_arity":{"fixed":0}}},"results":[],"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true}},
    \\{"id":2,"block":0,"operation":{"make_closure":{"function":1,"bindings":[]}},"results":[7],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}}]
    \\,"values":[
    \\{"id":0,"function":1,"name_hint":"a","origin":{"parameter":0}},
    \\{"id":1,"function":1,"name_hint":"b","origin":{"parameter":1}},
    \\{"id":2,"function":1,"name_hint":"c","origin":{"parameter":2}},
    \\{"id":3,"function":1,"name_hint":"f","origin":{"parameter":3}},
    \\{"id":4,"function":1,"name_hint":"g","origin":{"parameter":4}},
    \\{"id":5,"function":1,"name_hint":"if_result","origin":{"block_parameter":{"block":4,"index":0}}},
    \\{"id":6,"function":1,"name_hint":"call_result","origin":{"instruction_result":{"instruction":0,"index":0}}},
    \\{"id":7,"function":0,"type":{"kind":"function","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":2,"index":0}}}]
    \\,"value_packs":[
    \\{"id":0,"function":0,"origin":{"varargs":0},"shape":{"prefix":[],"tail":"open"}}]
    \\}
;

/// The source frontend's lift, resolved, of
/// `return function(a, b, c, f, g) g(a, if c then { a, b, a, b, a, b, a, b } else a) end`.
const if_constructor_argument_ir =
    \\{"schema_version":"lifter_ir_v1","program_id":"if-constructor-argument","source_semantics":"luau","entry_function":0,"functions":[
    \\{"id":0,"name_hint":"chunk","lexical_parent":null,"parameters":[],"captures":[],"local_places":[],"blocks":[0],"entry_block":0,"is_variadic":true,"vararg_pack":0},
    \\{"id":1,"name_hint":"closure","lexical_parent":0,"parameters":[0,1,2,3,4],"captures":[],"local_places":[],"blocks":[1,2,3,4],"entry_block":1,"is_variadic":false,"vararg_pack":null}]
    \\,"blocks":[
    \\{"id":0,"function":0,"name_hint":"entry","parameters":[],"instructions":[2],"terminator":{"return_values":[7]}},
    \\{"id":1,"function":1,"name_hint":"entry","parameters":[],"instructions":[],"terminator":{"branch":{"condition":2,"then_edge":{"target":2,"arguments":[]},"else_edge":{"target":3,"arguments":[]}}}},
    \\{"id":2,"function":1,"name_hint":"if_value_true","parameters":[],"instructions":[0],"terminator":{"jump":{"target":4,"arguments":[6]}}},
    \\{"id":3,"function":1,"name_hint":"if_value_false","parameters":[],"instructions":[],"terminator":{"jump":{"target":4,"arguments":[0]}}},
    \\{"id":4,"function":1,"name_hint":"if_value_join","parameters":[5],"instructions":[1],"terminator":{"return_values":[]}}]
    \\,"instructions":[
    \\{"id":0,"block":2,"operation":{"make_table_literal":{"fields":[{"list":0},{"list":1},{"list":0},{"list":1},{"list":0},{"list":1},{"list":0},{"list":1}],"tail_pack":null}},"results":[6],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":true,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":1,"block":4,"operation":{"call":{"callee":4,"arguments":[0,5],"argument_pack":null,"result_arity":{"fixed":0}}},"results":[],"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true}},
    \\{"id":2,"block":0,"operation":{"make_closure":{"function":1,"bindings":[]}},"results":[7],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}}]
    \\,"values":[
    \\{"id":0,"function":1,"name_hint":"a","origin":{"parameter":0}},
    \\{"id":1,"function":1,"name_hint":"b","origin":{"parameter":1}},
    \\{"id":2,"function":1,"name_hint":"c","origin":{"parameter":2}},
    \\{"id":3,"function":1,"name_hint":"f","origin":{"parameter":3}},
    \\{"id":4,"function":1,"name_hint":"g","origin":{"parameter":4}},
    \\{"id":5,"function":1,"name_hint":"if_result","origin":{"block_parameter":{"block":4,"index":0}}},
    \\{"id":6,"function":1,"type":{"kind":"table","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":0,"index":0}}},
    \\{"id":7,"function":0,"type":{"kind":"function","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":2,"index":0}}}]
    \\,"value_packs":[
    \\{"id":0,"function":0,"origin":{"varargs":0},"shape":{"prefix":[],"tail":"open"}}]
    \\}
;

/// The source frontend's lift, resolved, of a function `(n, p, q)` with `local x = 0` and `local i = 0` and a
/// `while i < n do` whose body is `i += 1`, `local z = i * p`, `z *= z`, `x = function() return z end`,
/// `if p then if q then continue end end` and `x = z`, returning `x`.
const wrapped_body_local_ir =
    \\{"schema_version":"lifter_ir_v1","program_id":"wrapped-body-local","source_semantics":"luau","entry_function":0,"functions":[
    \\{"id":0,"name_hint":"chunk","lexical_parent":null,"parameters":[],"captures":[],"local_places":[],"blocks":[0],"entry_block":0,"is_variadic":true,"vararg_pack":0},
    \\{"id":1,"name_hint":"closure","lexical_parent":0,"parameters":[0,1,2],"captures":[],"local_places":[0,1,2],"blocks":[1,2,3,4,6,7,8,9,10,11],"entry_block":1,"is_variadic":false,"vararg_pack":null},
    \\{"id":2,"name_hint":"assigned_1","lexical_parent":1,"parameters":[],"captures":[0],"local_places":[],"blocks":[5],"entry_block":5,"is_variadic":false,"vararg_pack":null}]
    \\,"blocks":[
    \\{"id":0,"function":0,"name_hint":"entry","parameters":[],"instructions":[23],"terminator":{"return_values":[19]}},
    \\{"id":1,"function":1,"name_hint":"entry","parameters":[],"instructions":[0,1,2,3],"terminator":{"jump":{"target":2,"arguments":[]}}},
    \\{"id":2,"function":1,"name_hint":"while_header","parameters":[],"instructions":[4,5],"terminator":{"branch":{"condition":6,"then_edge":{"target":3,"arguments":[]},"else_edge":{"target":4,"arguments":[]}}}},
    \\{"id":3,"function":1,"name_hint":"while_body","parameters":[],"instructions":[6,7,8,9,10,11,12,13,14,15,16,18,19],"terminator":{"branch":{"condition":1,"then_edge":{"target":6,"arguments":[]},"else_edge":{"target":7,"arguments":[]}}}},
    \\{"id":4,"function":1,"name_hint":"while_exit","parameters":[],"instructions":[22],"terminator":{"return_values":[18]}},
    \\{"id":5,"function":2,"name_hint":"entry","parameters":[],"instructions":[17],"terminator":{"return_values":[15]}},
    \\{"id":6,"function":1,"name_hint":"then","parameters":[],"instructions":[],"terminator":{"branch":{"condition":2,"then_edge":{"target":8,"arguments":[]},"else_edge":{"target":9,"arguments":[]}}}},
    \\{"id":7,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":11,"arguments":[]}}},
    \\{"id":8,"function":1,"name_hint":"then","parameters":[],"instructions":[],"terminator":{"jump":{"target":2,"arguments":[]}}},
    \\{"id":9,"function":1,"name_hint":"else","parameters":[],"instructions":[],"terminator":{"jump":{"target":10,"arguments":[]}}},
    \\{"id":10,"function":1,"name_hint":"join","parameters":[],"instructions":[],"terminator":{"jump":{"target":11,"arguments":[]}}},
    \\{"id":11,"function":1,"name_hint":"join","parameters":[],"instructions":[20,21],"terminator":{"jump":{"target":2,"arguments":[]}}}]
    \\,"instructions":[
    \\{"id":0,"block":1,"operation":{"constant":{"integer":"0"}},"results":[3],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":1,"block":1,"operation":{"place_write":{"place":0,"value":3}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":2,"block":1,"operation":{"constant":{"integer":"0"}},"results":[4],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":3,"block":1,"operation":{"place_write":{"place":1,"value":4}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":4,"block":2,"operation":{"place_read":1},"results":[5],"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":5,"block":2,"operation":{"binary":{"operator":"less","left":5,"right":0,"mode":"semantic","shift_behavior":null}},"results":[6],"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true}},
    \\{"id":6,"block":3,"operation":{"constant":{"integer":"1"}},"results":[7],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":7,"block":3,"operation":{"place_read":1},"results":[8],"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":8,"block":3,"operation":{"binary":{"operator":"add","left":8,"right":7,"mode":"semantic","shift_behavior":null}},"results":[9],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":9,"block":3,"operation":{"place_write":{"place":1,"value":9}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":10,"block":3,"operation":{"place_read":1},"results":[10],"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":11,"block":3,"operation":{"binary":{"operator":"multiply","left":10,"right":1,"mode":"semantic","shift_behavior":null}},"results":[11],"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true}},
    \\{"id":12,"block":3,"operation":{"place_write":{"place":2,"value":11}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":13,"block":3,"operation":{"place_read":2},"results":[12],"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":14,"block":3,"operation":{"place_read":2},"results":[13],"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":15,"block":3,"operation":{"binary":{"operator":"multiply","left":13,"right":12,"mode":"semantic","shift_behavior":null}},"results":[14],"effects":{"precision":"conservative","reads_memory":true,"writes_memory":true,"may_throw":true,"may_yield":true,"invokes_unknown_code":true}},
    \\{"id":16,"block":3,"operation":{"place_write":{"place":2,"value":14}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":17,"block":5,"operation":{"place_read":3},"results":[15],"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":18,"block":3,"operation":{"make_closure":{"function":2,"bindings":[{"place":2}]}},"results":[16],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":19,"block":3,"operation":{"place_write":{"place":0,"value":16}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":20,"block":11,"operation":{"place_read":2},"results":[17],"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":21,"block":11,"operation":{"place_write":{"place":0,"value":17}},"results":[],"effects":{"precision":"exact","reads_memory":false,"writes_memory":true,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":22,"block":4,"operation":{"place_read":0},"results":[18],"effects":{"precision":"exact","reads_memory":true,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}},
    \\{"id":23,"block":0,"operation":{"make_closure":{"function":1,"bindings":[]}},"results":[19],"effects":{"precision":"exact","reads_memory":false,"writes_memory":false,"may_throw":false,"may_yield":false,"invokes_unknown_code":false}}]
    \\,"values":[
    \\{"id":0,"function":1,"name_hint":"n","origin":{"parameter":0}},
    \\{"id":1,"function":1,"name_hint":"p","origin":{"parameter":1}},
    \\{"id":2,"function":1,"name_hint":"q","origin":{"parameter":2}},
    \\{"id":3,"function":1,"type":{"kind":"integer","bit_width":64,"signed":true},"name_hint":"x","origin":{"instruction_result":{"instruction":0,"index":0}}},
    \\{"id":4,"function":1,"type":{"kind":"integer","bit_width":64,"signed":true},"name_hint":"i","origin":{"instruction_result":{"instruction":2,"index":0}}},
    \\{"id":5,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":"i","origin":{"instruction_result":{"instruction":4,"index":0}}},
    \\{"id":6,"function":1,"type":{"kind":"boolean","bit_width":0,"signed":false},"name_hint":"while_condition","origin":{"instruction_result":{"instruction":5,"index":0}}},
    \\{"id":7,"function":1,"type":{"kind":"integer","bit_width":64,"signed":true},"name_hint":null,"origin":{"instruction_result":{"instruction":6,"index":0}}},
    \\{"id":8,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":"i","origin":{"instruction_result":{"instruction":7,"index":0}}},
    \\{"id":9,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":"compound_result","origin":{"instruction_result":{"instruction":8,"index":0}}},
    \\{"id":10,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":"i","origin":{"instruction_result":{"instruction":10,"index":0}}},
    \\{"id":11,"function":1,"name_hint":"z","origin":{"instruction_result":{"instruction":11,"index":0}}},
    \\{"id":12,"function":1,"name_hint":"z","origin":{"instruction_result":{"instruction":13,"index":0}}},
    \\{"id":13,"function":1,"name_hint":"z","origin":{"instruction_result":{"instruction":14,"index":0}}},
    \\{"id":14,"function":1,"name_hint":"compound_result","origin":{"instruction_result":{"instruction":15,"index":0}}},
    \\{"id":15,"function":2,"name_hint":"z","origin":{"instruction_result":{"instruction":17,"index":0}}},
    \\{"id":16,"function":1,"type":{"kind":"function","bit_width":0,"signed":false},"name_hint":"assigned_1","origin":{"instruction_result":{"instruction":18,"index":0}}},
    \\{"id":17,"function":1,"name_hint":"z","origin":{"instruction_result":{"instruction":20,"index":0}}},
    \\{"id":18,"function":1,"name_hint":"x","origin":{"instruction_result":{"instruction":22,"index":0}}},
    \\{"id":19,"function":0,"type":{"kind":"function","bit_width":0,"signed":false},"name_hint":null,"origin":{"instruction_result":{"instruction":23,"index":0}}}]
    \\,"value_packs":[
    \\{"id":0,"function":0,"origin":{"varargs":0},"shape":{"prefix":[],"tail":"open"}}]
    \\,"places":[
    \\{"id":0,"function":1,"name_hint":"x","origin":{"local":0}},
    \\{"id":1,"function":1,"type":{"kind":"number","bit_width":64,"signed":false},"name_hint":"i","origin":{"local":1}},
    \\{"id":2,"function":1,"name_hint":"z","origin":{"instruction":12}},
    \\{"id":3,"function":2,"name_hint":"z","origin":{"capture":0}}]
    \\,"captures":[
    \\{"id":0,"function":2,"kind":{"shared_place":3}}]
    \\,"solver_terms":[
    \\{"id":0,"sort":{"kind":"boolean","bit_width":0,"signed":false},"operation":{"value":6}},
    \\{"id":1,"sort":{"kind":"boolean","bit_width":0,"signed":false},"operation":{"logical_not":0}}]
    \\,"constraints":[
    \\{"id":0,"predicate":0,"scope":{"edge":{"source":2,"kind":"branch_then","target":3}},"path_rewrites":[]},
    \\{"id":1,"predicate":1,"scope":{"edge":{"source":2,"kind":"branch_else","target":4}},"path_rewrites":[]}]
    \\}
;
