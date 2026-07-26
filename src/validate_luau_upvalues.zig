const std = @import("std");
const diagnostics = @import("diagnostics.zig");
const emission_planning = @import("emit_luau_plan.zig");
const ir = @import("ir.zig");
const lexical = @import("emit_luau_lexical.zig");
const luau_runtime = @import("luau_runtime.zig");
const readable_scope = @import("readable_scope.zig");
const runtime_uses = @import("runtime_uses.zig");

// Keys model source locals as the Luau compiler sees them. Explicit capture
// slots can alias one key, while runtime names, root functions, and external
// bindings are locals owned by the emitted chunk.
const BindingKey = union(enum) {
    value: struct {
        id: ir.ValueId,
        owner: ir.FunctionId,
    },
    place: struct {
        id: ir.PlaceId,
        owner: ir.FunctionId,
    },
    external_binding: ir.ExternalBindingId,
    runtime_capability: luau_runtime.Capability,
    root_function: ir.FunctionId,

    fn owner(self: BindingKey, entry: ir.FunctionId) ir.FunctionId {
        return switch (self) {
            .value => |value| value.owner,
            .place => |place| place.owner,
            .external_binding, .runtime_capability, .root_function => entry,
        };
    }
};

const FreeBindings = struct {
    items: std.ArrayList(BindingKey) = .empty,

    fn init(allocator: std.mem.Allocator) !FreeBindings {
        var result: FreeBindings = .{};
        try result.items.ensureUnusedCapacity(allocator, luau_runtime.max_upvalue_registers + 1);
        return result;
    }

    fn deinit(self: *FreeBindings, allocator: std.mem.Allocator) void {
        self.items.deinit(allocator);
    }

    fn add(self: *FreeBindings, key: BindingKey) void {
        for (self.items.items) |existing| {
            if (sameBinding(existing, key)) return;
        }
        if (self.items.items.len > luau_runtime.max_upvalue_registers) return;
        self.items.appendAssumeCapacity(key);
    }
};

const ValueCapture = struct {
    captured: ir.ValueId,
    source: BindingKey,
};

const PlaceCapture = struct {
    captured: ir.PlaceId,
    source: BindingKey,
};

const CaptureMap = struct {
    values: std.ArrayList(ValueCapture) = .empty,
    places: std.ArrayList(PlaceCapture) = .empty,

    fn deinit(self: *CaptureMap, allocator: std.mem.Allocator) void {
        self.places.deinit(allocator);
        self.values.deinit(allocator);
    }

    fn value(self: *const CaptureMap, captured: ir.ValueId) ?BindingKey {
        for (self.values.items) |binding| if (binding.captured == captured) return binding.source;
        return null;
    }

    fn place(self: *const CaptureMap, captured: ir.PlaceId) ?BindingKey {
        for (self.places.items) |binding| if (binding.captured == captured) return binding.source;
        return null;
    }
};

const StableValues = struct {
    values: []const bool,

    pub fn contains(self: StableValues, value_id: ir.ValueId) bool {
        return value_id.index() < self.values.len and self.values[value_id.index()];
    }
};

const Context = struct {
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
    stable_values: []const bool,
    reported: []bool,

    fn collectFunction(
        self: *Context,
        function: ir.Function,
        captures: *const CaptureMap,
        depth: usize,
    ) std.mem.Allocator.Error!FreeBindings {
        std.debug.assert(depth <= self.program.functions.len);
        var free = try FreeBindings.init(self.allocator);
        errdefer free.deinit(self.allocator);

        for (function.blocks) |block_id| {
            if (!self.readable.block(block_id) or block_id.index() >= self.program.blocks.len) continue;
            const block = self.program.blocks[block_id.index()];
            for (block.instructions) |instruction_id| {
                if (!self.readable.instruction(instruction_id) or instruction_id.index() >= self.program.instructions.len) continue;
                const instruction = self.program.instructions[instruction_id.index()];
                if (!instructionSurvives(self.emission, instruction.id)) continue;
                try self.recordOperation(function, captures, &free, instruction, depth);
            }
            self.recordTerminator(function, captures, &free, block.id, block.terminator);
        }

        if (function.id != self.program.entry_function and
            free.items.items.len > luau_runtime.max_upvalue_registers and
            !self.reported[function.id.index()])
        {
            try self.report.add(.unsupported_readable_upvalue_pressure, function.id.index());
            self.reported[function.id.index()] = true;
        }
        return free;
    }

    fn recordOperation(
        self: *Context,
        function: ir.Function,
        captures: *const CaptureMap,
        free: *FreeBindings,
        instruction: ir.Instruction,
        depth: usize,
    ) std.mem.Allocator.Error!void {
        const operation = instruction.operation;
        self.recordOperationRuntime(function.id, free, operation);
        var planned_runtime: luau_runtime.Set = .{};
        switch (self.emission.packs.role(instruction.id)) {
            .stored_invocation_producer => {
                planned_runtime.mark(.rawset);
                planned_runtime.mark(.select);
            },
            .stored_adjustment => planned_runtime.mark(.rawget),
            else => {},
        }
        if (instructionConsumesStoredPack(self.program, self.emission, instruction)) {
            planned_runtime.mark(.rawget);
            planned_runtime.mark(.table_unpack);
        }
        self.recordRuntimeSet(function.id, free, planned_runtime);
        switch (operation) {
            .make_closure => |closure| {
                try self.recordClosure(function, captures, free, closure, depth);
                return;
            },
            .function_ref => |target| {
                self.recordKey(function.id, free, .{ .root_function = target });
                return;
            },
            else => {},
        }

        const visitor: UseVisitor = .{
            .context = self,
            .function = function.id,
            .captures = captures,
            .free = free,
        };
        runtime_uses.visitOperationUses(operation, visitor);
        switch (operation) {
            .place_read => |place_id| if (self.placeKey(function.id, captures, place_id)) |key| {
                if (key == .external_binding) self.recordKey(function.id, free, .{ .runtime_capability = .rawget });
            },
            .place_write => |write| if (self.placeKey(function.id, captures, write.place)) |key| {
                if (key == .external_binding) self.recordKey(function.id, free, .{ .runtime_capability = .rawset });
            },
            else => {},
        }
    }

    fn instructionConsumesStoredPack(
        program: *const ir.Program,
        emission: *const emission_planning.Plan,
        instruction: ir.Instruction,
    ) bool {
        const pack_id = switch (instruction.operation) {
            .call => |operation| operation.argument_pack,
            .namecall => |operation| operation.argument_pack,
            .protected_call => |operation| operation.argument_pack,
            .coroutine_resume => |operation| operation.argument_pack,
            .coroutine_yield => |operation| operation.argument_pack,
            .make_table_literal => |operation| operation.tail_pack,
            .table_set_pack => |operation| operation.pack,
            else => null,
        } orelse return false;
        if (pack_id.index() >= program.value_packs.len) return false;
        const producer_id = switch (program.value_packs[pack_id.index()].origin) {
            .instruction_result => |value| value,
            .varargs => return false,
        };
        return emission.packs.storedPackServesInstruction(producer_id, instruction.id);
    }

    fn recordClosure(
        self: *Context,
        function: ir.Function,
        captures: *const CaptureMap,
        free: *FreeBindings,
        closure: ir.Closure,
        depth: usize,
    ) std.mem.Allocator.Error!void {
        const target = self.program.functions[closure.function.index()];
        var plan = lexical.ClosurePlan.initWithStableValues(
            self.allocator,
            self.program,
            target,
            closure,
            &.{},
            StableValues{ .values = self.stable_values },
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.InvalidClosureBinding => unreachable,
        };
        defer plan.deinit();

        for (plan.value_bindings) |binding| {
            self.recordValue(function.id, captures, free, binding.source);
        }

        var child_captures: CaptureMap = .{};
        defer child_captures.deinit(self.allocator);
        try child_captures.values.ensureUnusedCapacity(self.allocator, target.captures.len);
        try child_captures.places.ensureUnusedCapacity(self.allocator, target.captures.len);
        for (target.captures, closure.bindings) |capture_id, binding| {
            const capture = self.program.captures[capture_id.index()];
            switch (capture.kind) {
                .immutable_value => |captured| {
                    const source = switch (binding) {
                        .value => |value_id| value_id,
                        .place => unreachable,
                    };
                    const key: BindingKey = if (hasSnapshot(plan.value_bindings, captured))
                        .{ .value = .{ .id = captured, .owner = function.id } }
                    else
                        self.valueKey(captures, source);
                    child_captures.values.appendAssumeCapacity(.{ .captured = captured, .source = key });
                },
                .shared_place => |captured| {
                    const source = switch (binding) {
                        .place => |place_id| place_id,
                        .value => unreachable,
                    };
                    child_captures.places.appendAssumeCapacity(.{
                        .captured = captured,
                        .source = self.placeKey(function.id, captures, source).?,
                    });
                },
            }
        }

        var child = try self.collectFunction(target, &child_captures, depth + 1);
        defer child.deinit(self.allocator);
        // A child binding owned outside this function must be forwarded through
        // this function's own upvalue table, even when only the child reads it.
        for (child.items.items) |key| {
            if (key.owner(self.program.entry_function) != function.id) free.add(key);
        }
    }

    fn recordTerminator(
        self: *Context,
        function: ir.Function,
        captures: *const CaptureMap,
        free: *FreeBindings,
        block_id: ir.BlockId,
        terminator: ir.Terminator,
    ) void {
        var required: luau_runtime.Set = .{};
        required.markTerminator(terminator);
        if (self.emission.packs.terminatorRole(block_id) == .stored_pack_return) {
            required.mark(.rawget);
            required.mark(.table_unpack);
        }
        self.recordRuntimeSet(function.id, free, required);
        runtime_uses.visitTerminatorUses(terminator, UseVisitor{
            .context = self,
            .function = function.id,
            .captures = captures,
            .free = free,
        });
    }

    fn recordOperationRuntime(self: *Context, function: ir.FunctionId, free: *FreeBindings, operation: ir.Operation) void {
        var required: luau_runtime.Set = .{};
        required.markOperation(operation);
        self.recordRuntimeSet(function, free, required);
    }

    fn recordRuntimeSet(self: *Context, function: ir.FunctionId, free: *FreeBindings, required: luau_runtime.Set) void {
        for (luau_runtime.capabilities) |capability| {
            if (required.has(capability)) self.recordKey(function, free, .{ .runtime_capability = capability });
        }
    }

    fn recordValue(self: *Context, function: ir.FunctionId, captures: *const CaptureMap, free: *FreeBindings, value_id: ir.ValueId) void {
        self.recordKey(function, free, self.valueKey(captures, value_id));
    }

    fn recordPlace(self: *Context, function: ir.FunctionId, captures: *const CaptureMap, free: *FreeBindings, place_id: ir.PlaceId) void {
        if (self.placeKey(function, captures, place_id)) |key| self.recordKey(function, free, key);
    }

    fn valueKey(self: *Context, captures: *const CaptureMap, value_id: ir.ValueId) BindingKey {
        if (captures.value(value_id)) |key| return key;
        const resolved = self.emission.dead.resolveValue(value_id);
        if (captures.value(resolved)) |key| return key;
        const value = self.program.values[resolved.index()];
        return .{ .value = .{ .id = resolved, .owner = value.function } };
    }

    fn placeKey(self: *Context, function: ir.FunctionId, captures: *const CaptureMap, place_id: ir.PlaceId) ?BindingKey {
        _ = function;
        if (captures.place(place_id)) |key| return key;
        if (place_id.index() >= self.program.places.len) return null;
        const place = self.program.places[place_id.index()];
        return .{ .place = .{ .id = place_id, .owner = place.function } };
    }

    fn recordKey(self: *Context, function: ir.FunctionId, free: *FreeBindings, key: BindingKey) void {
        if (key.owner(self.program.entry_function) != function) free.add(key);
    }
};

const UseVisitor = struct {
    context: *Context,
    function: ir.FunctionId,
    captures: *const CaptureMap,
    free: *FreeBindings,

    pub fn value(self: UseVisitor, value_id: ir.ValueId) void {
        self.context.recordValue(self.function, self.captures, self.free, value_id);
    }

    pub fn pack(_: UseVisitor, _: ir.ValuePackId) void {}

    pub fn place(self: UseVisitor, place_id: ir.PlaceId) void {
        self.context.recordPlace(self.function, self.captures, self.free, place_id);
    }
};

pub fn validate(
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
    stable_values: []const bool,
) std.mem.Allocator.Error!void {
    const reported = try allocator.alloc(bool, program.functions.len);
    defer allocator.free(reported);
    @memset(reported, false);
    var context: Context = .{
        .allocator = allocator,
        .report = report,
        .program = program,
        .readable = readable,
        .emission = emission,
        .stable_values = stable_values,
        .reported = reported,
    };

    var entry_captures: CaptureMap = .{};
    defer entry_captures.deinit(allocator);
    const entry = program.functions[program.entry_function.index()];
    try entry_captures.values.ensureUnusedCapacity(allocator, entry.captures.len);
    try entry_captures.places.ensureUnusedCapacity(allocator, entry.captures.len);
    for (entry.captures, program.entry_bindings) |capture_id, binding_id| {
        const capture = program.captures[capture_id.index()];
        switch (capture.kind) {
            .immutable_value => |captured| entry_captures.values.appendAssumeCapacity(.{
                .captured = captured,
                .source = .{ .value = .{ .id = captured, .owner = entry.id } },
            }),
            .shared_place => |captured| entry_captures.places.appendAssumeCapacity(.{
                .captured = captured,
                .source = .{ .external_binding = binding_id },
            }),
        }
    }
    var entry_free = try context.collectFunction(entry, &entry_captures, 0);
    entry_free.deinit(allocator);

    for (program.functions) |function| {
        if (function.id == program.entry_function or function.lexical_parent != null) continue;
        var no_captures: CaptureMap = .{};
        defer no_captures.deinit(allocator);
        var root_free = try context.collectFunction(function, &no_captures, 0);
        root_free.deinit(allocator);
    }
}

fn instructionSurvives(emission: *const emission_planning.Plan, instruction_id: ir.InstructionId) bool {
    return !emission.dead.contains(instruction_id) or emission.dead.isInlined(instruction_id);
}

fn hasSnapshot(bindings: []const lexical.ValueBinding, captured: ir.ValueId) bool {
    for (bindings) |binding| if (binding.captured == captured) return true;
    return false;
}

fn sameBinding(left: BindingKey, right: BindingKey) bool {
    if (std.meta.activeTag(left) != std.meta.activeTag(right)) return false;
    return switch (left) {
        .value => |value| value.id == right.value.id and value.owner == right.value.owner,
        .place => |place| place.id == right.place.id and place.owner == right.place.owner,
        .external_binding => |binding| binding == right.external_binding,
        .runtime_capability => |capability| capability == right.runtime_capability,
        .root_function => |function| function == right.root_function,
    };
}
