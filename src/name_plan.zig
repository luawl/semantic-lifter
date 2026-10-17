const std = @import("std");
const ir = @import("ir.zig");
const luau_runtime = @import("luau_runtime.zig");
const luau_syntax = @import("luau_syntax.zig");
const readable_scope = @import("readable_scope.zig");
const runtime_uses = @import("runtime_uses.zig");
const structure = @import("structure.zig");
const iteration_protocol = @import("iteration_protocol.zig");

pub const Plan = struct {
    allocator: std.mem.Allocator,
    values: [][]const u8,
    value_storage: []bool,
    value_packs: [][]const u8,
    places: [][]const u8,
    storage_places: []bool,
    storage_name: []const u8,
    value_storage_name: []const u8,
    functions: [][]const u8,
    external_bindings: [][]const u8,
    runtime_capabilities: [][]const u8,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program) !Plan {
        var scope = try readable_scope.Scope.init(allocator, program);
        defer scope.deinit();
        const runtime_plan = luau_runtime.Plan.init(.standard_luau, program, &scope);
        return initWithRuntime(allocator, program, &scope, runtime_plan);
    }

    pub fn initWithRuntime(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        scope: *const readable_scope.Scope,
        runtime_plan: luau_runtime.Plan,
    ) !Plan {
        const values = try allocator.alloc([]const u8, program.values.len);
        errdefer allocator.free(values);
        @memset(values, "");
        const value_storage = try allocator.alloc(bool, program.values.len);
        errdefer allocator.free(value_storage);
        @memset(value_storage, false);
        const value_packs = try allocator.alloc([]const u8, program.value_packs.len);
        errdefer allocator.free(value_packs);
        @memset(value_packs, "");
        const places = try allocator.alloc([]const u8, program.places.len);
        errdefer allocator.free(places);
        @memset(places, "");
        const storage_places = try allocator.alloc(bool, program.places.len);
        errdefer allocator.free(storage_places);
        @memset(storage_places, false);
        const functions = try allocator.alloc([]const u8, program.functions.len);
        errdefer allocator.free(functions);
        @memset(functions, "");
        const external_bindings = try allocator.alloc([]const u8, program.external_bindings.len);
        errdefer allocator.free(external_bindings);
        @memset(external_bindings, "");
        const runtime_capabilities = try allocator.alloc([]const u8, luau_runtime.capabilities.len);
        errdefer allocator.free(runtime_capabilities);
        @memset(runtime_capabilities, "");

        var plan: Plan = .{
            .allocator = allocator,
            .values = values,
            .value_storage = value_storage,
            .value_packs = value_packs,
            .places = places,
            .storage_places = storage_places,
            .storage_name = "",
            .value_storage_name = "",
            .functions = functions,
            .external_bindings = external_bindings,
            .runtime_capabilities = runtime_capabilities,
        };
        errdefer plan.freeNames();

        var used: std.StringHashMapUnmanaged(void) = .empty;
        defer used.deinit(allocator);
        const runtime_places = try allocator.alloc(bool, program.places.len);
        defer allocator.free(runtime_places);
        @memset(runtime_places, false);
        const native_iteration_body_parameters = try allocator.alloc(bool, program.values.len);
        defer allocator.free(native_iteration_body_parameters);
        @memset(native_iteration_body_parameters, false);
        markNativeIterationBodyParameters(program, native_iteration_body_parameters);

        for (luau_syntax.always_reserved_runtime_globals) |global| try used.put(allocator, global.name(), {});
        for (program.instructions) |instruction| {
            if (!scope.instruction(instruction.id)) continue;
            switch (instruction.operation) {
                .environment_get => |operation| {
                    if (operation.target == .ambient and luau_syntax.isIdentifier(operation.name)) try used.put(allocator, operation.name, {});
                },
                .environment_set => |operation| {
                    if (operation.target == .ambient and luau_syntax.isIdentifier(operation.name)) try used.put(allocator, operation.name, {});
                },
                else => {},
            }
            runtime_uses.visitOperationUses(instruction.operation, PlaceCollector{ .places = runtime_places });
        }
        for (luau_runtime.capabilities) |capability| {
            if (!runtime_plan.requires(capability)) continue;
            const source = capability.source();
            if (source.method != null) try used.put(allocator, source.global.name(), {});
            plan.runtime_capabilities[@intFromEnum(capability)] = try uniqueName(allocator, &used, capability.captureHint());
        }
        for (program.external_bindings) |binding| {
            const kind = switch (binding.kind) {
                .immutable_value => "value",
                .shared_place => "place",
            };
            const hint = try std.fmt.allocPrint(allocator, "__lifter_external_{s}_{d}", .{ kind, binding.id.index() });
            defer allocator.free(hint);
            plan.external_bindings[binding.id.index()] = try uniqueName(allocator, &used, hint);
        }
        for (program.places) |place_item| switch (place_item.origin) {
            .instruction => |instruction_id| if (place_item.id.index() < runtime_places.len and scope.instruction(instruction_id)) {
                runtime_places[place_item.id.index()] = true;
            },
            .local, .capture => {},
        };
        try markPrivatePlaceStorage(allocator, program, plan.storage_places, runtime_plan.target);
        if (runtime_plan.target == .standard_luau) {
            var has_value_storage = false;
            for (program.functions) |function_item| {
                var candidate_values: usize = 0;
                for (program.values) |value_item| {
                    if (value_item.function == function_item.id) {
                        switch (value_item.origin) {
                            .parameter, .capture => {},
                            .block_parameter, .instruction_result => candidate_values += 1,
                        }
                    }
                }
                const needs_value_storage = structure.Plan.shouldUseArbitraryFallbackForFunction(program, function_item) or candidate_values > 120 or function_item.blocks.len > 150;
                if (!needs_value_storage) continue;
                for (program.values) |value_item| {
                    if (value_item.function != function_item.id) continue;
                    switch (value_item.origin) {
                        .parameter, .capture => {},
                        .block_parameter, .instruction_result => {
                            if (native_iteration_body_parameters[value_item.id.index()]) continue;
                            plan.value_storage[value_item.id.index()] = true;
                            has_value_storage = true;
                        },
                    }
                }
            }
            if (has_value_storage) {
                plan.value_storage_name = try uniqueName(allocator, &used, "__lifter_value_storage");
            }
        }
        for (program.functions) |function_item| {
            const fallback = try std.fmt.allocPrint(allocator, "fn_{d}", .{function_item.id.index()});
            defer allocator.free(fallback);
            const hint = if (function_item.name_hint) |name| try prefixedHint(allocator, "fn_", name) else fallback;
            defer if (function_item.name_hint != null) allocator.free(hint);
            plan.functions[function_item.id.index()] = try uniqueName(allocator, &used, hint);
        }

        const assigned_functions = try allocator.alloc(bool, program.functions.len);
        defer allocator.free(assigned_functions);
        @memset(assigned_functions, false);
        var remaining = program.functions.len;
        while (remaining != 0) {
            var made_progress = false;
            for (program.functions) |function_item| {
                if (assigned_functions[function_item.id.index()]) continue;
                if (function_item.lexical_parent) |parent| {
                    if (parent.index() >= assigned_functions.len or !assigned_functions[parent.index()]) continue;
                }
                try plan.assignFunction(program, scope, runtime_places, &used, function_item);
                assigned_functions[function_item.id.index()] = true;
                remaining -= 1;
                made_progress = true;
            }
            if (!made_progress) unreachable;
        }
        plan.storage_name = try uniqueName(allocator, &used, "__lifter_place_storage");
        // A boxed per-execution cell is captured by snapshot — the child reads its own
        // `local <cell> = <holder>` through `[1]`. Name each shared_place capture's captured place (capture
        // origin, otherwise unnamed) so the snapshot binding and the terminal boxed-place alias resolve it.
        // Assigned last, so no earlier name moves; a non-boxed shared_place capture keeps the plain `.place`
        // alias and never reads this name, so no existing output changes.
        for (program.captures) |capture_item| switch (capture_item.kind) {
            .shared_place => |captured| {
                if (captured.index() >= plan.places.len or plan.places[captured.index()].len != 0) continue;
                const hint = try std.fmt.allocPrint(allocator, "cell_{d}", .{captured.index()});
                defer allocator.free(hint);
                plan.places[captured.index()] = try uniqueName(allocator, &used, hint);
            },
            .immutable_value => {},
        };
        return plan;
    }

    pub fn deinit(self: *Plan) void {
        self.freeNames();
        self.allocator.free(self.functions);
        self.allocator.free(self.value_storage);
        self.allocator.free(self.storage_places);
        self.allocator.free(self.places);
        self.allocator.free(self.value_packs);
        self.allocator.free(self.values);
        self.allocator.free(self.external_bindings);
        self.allocator.free(self.runtime_capabilities);
        self.* = undefined;
    }

    pub fn value(self: *const Plan, value_id: ir.ValueId) ?[]const u8 {
        if (value_id.index() >= self.values.len or self.values[value_id.index()].len == 0) return null;
        return self.values[value_id.index()];
    }

    pub fn valueUsesStorage(self: *const Plan, value_id: ir.ValueId) bool {
        return value_id.index() < self.value_storage.len and self.value_storage[value_id.index()];
    }

    pub fn functionUsesValueStorage(self: *const Plan, program: *const ir.Program, function_item: ir.Function) bool {
        for (program.values) |value_item| {
            if (value_item.function == function_item.id and self.valueUsesStorage(value_item.id)) return true;
        }
        return false;
    }

    pub fn valueStorageName(self: *const Plan) ?[]const u8 {
        return if (self.value_storage_name.len == 0) null else self.value_storage_name;
    }

    pub fn valuePack(self: *const Plan, pack_id: ir.ValuePackId) ?[]const u8 {
        if (pack_id.index() >= self.value_packs.len or self.value_packs[pack_id.index()].len == 0) return null;
        return self.value_packs[pack_id.index()];
    }

    pub fn function(self: *const Plan, function_id: ir.FunctionId) ?[]const u8 {
        if (function_id.index() >= self.functions.len or self.functions[function_id.index()].len == 0) return null;
        return self.functions[function_id.index()];
    }

    pub fn place(self: *const Plan, place_id: ir.PlaceId) ?[]const u8 {
        if (place_id.index() >= self.places.len or self.places[place_id.index()].len == 0) return null;
        return self.places[place_id.index()];
    }

    pub fn placeUsesStorage(self: *const Plan, place_id: ir.PlaceId) bool {
        return place_id.index() < self.storage_places.len and self.storage_places[place_id.index()];
    }

    pub fn functionUsesStorage(self: *const Plan, function_item: ir.Function) bool {
        for (function_item.local_places) |place_id| {
            if (self.placeUsesStorage(place_id)) return true;
        }
        return false;
    }

    pub fn placeStorageName(self: *const Plan) ?[]const u8 {
        return if (self.storage_name.len == 0) null else self.storage_name;
    }

    pub fn runtimeCapability(self: *const Plan, capability: luau_runtime.Capability) ?[]const u8 {
        const name = self.runtime_capabilities[@intFromEnum(capability)];
        return if (name.len == 0) null else name;
    }

    pub fn externalBinding(self: *const Plan, binding_id: ir.ExternalBindingId) ?[]const u8 {
        if (binding_id.index() >= self.external_bindings.len or self.external_bindings[binding_id.index()].len == 0) return null;
        return self.external_bindings[binding_id.index()];
    }

    pub fn internalNameAlloc(
        self: *const Plan,
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        raw_base: []const u8,
    ) std.mem.Allocator.Error![]const u8 {
        var used: std.StringHashMapUnmanaged(void) = .empty;
        defer used.deinit(allocator);
        inline for (.{ self.values, self.value_packs, self.places, self.functions, self.external_bindings, self.runtime_capabilities }) |names| {
            for (names) |name| if (name.len != 0) try used.put(allocator, name, {});
        }
        if (self.storage_name.len != 0) try used.put(allocator, self.storage_name, {});
        if (self.value_storage_name.len != 0) try used.put(allocator, self.value_storage_name, {});
        for (luau_syntax.always_reserved_runtime_globals) |global| try used.put(allocator, global.name(), {});
        for (program.instructions) |instruction| switch (instruction.operation) {
            .environment_get => |operation| {
                if (operation.target == .ambient and luau_syntax.isIdentifier(operation.name)) {
                    try used.put(allocator, operation.name, {});
                }
            },
            .environment_set => |operation| {
                if (operation.target == .ambient and luau_syntax.isIdentifier(operation.name)) {
                    try used.put(allocator, operation.name, {});
                }
            },
            else => {},
        };
        return uniqueName(allocator, &used, raw_base);
    }

    fn assignFunction(
        self: *Plan,
        program: *const ir.Program,
        scope: *const readable_scope.Scope,
        runtime_places: []const bool,
        global_symbols: *const std.StringHashMapUnmanaged(void),
        function_item: ir.Function,
    ) !void {
        var used: std.StringHashMapUnmanaged(void) = .empty;
        defer used.deinit(self.allocator);
        var global_iterator = global_symbols.keyIterator();
        while (global_iterator.next()) |name| try used.put(self.allocator, name.*, {});
        if (function_item.id == program.entry_function and entryNeedsShiftedVarargs(program)) {
            try used.put(self.allocator, luau_syntax.RuntimeGlobal.select.name(), {});
        }

        try self.reserveClosureSources(program, scope, &used, function_item.id);
        for (function_item.parameters) |value_id| if (scope.value(value_id)) try self.assignValue(program, &used, value_id);
        for (program.places) |place_item| {
            if (place_item.function == function_item.id and place_item.id.index() < runtime_places.len and runtime_places[place_item.id.index()]) {
                try self.assignPlace(program, &used, place_item.id);
            }
        }
        for (program.values) |value_item| {
            if (value_item.function == function_item.id and scope.value(value_item.id) and self.values[value_item.id.index()].len == 0) {
                try self.assignValue(program, &used, value_item.id);
            }
        }
        for (program.value_packs) |pack| {
            if (pack.function == function_item.id and self.value_packs[pack.id.index()].len == 0) {
                try self.assignValuePack(&used, pack.id);
            }
        }
    }

    fn assignValue(self: *Plan, program: *const ir.Program, used: *std.StringHashMapUnmanaged(void), value_id: ir.ValueId) !void {
        if (value_id.index() >= program.values.len or self.values[value_id.index()].len != 0) return;
        if (self.valueUsesStorage(value_id)) {
            const storage_name = self.valueStorageName() orelse return error.OutOfMemory;
            self.values[value_id.index()] = try std.fmt.allocPrint(self.allocator, "{s}[{d}]", .{ storage_name, value_id.index() });
            return;
        }
        const value_item = program.values[value_id.index()];
        const fallback = try std.fmt.allocPrint(self.allocator, "value_{d}", .{value_id.index()});
        defer self.allocator.free(fallback);
        const base = if (value_item.name_hint) |hint| try sanitized(self.allocator, hint) else fallback;
        defer if (value_item.name_hint != null) self.allocator.free(base);
        self.values[value_id.index()] = try uniqueName(self.allocator, used, base);
    }

    fn assignPlace(self: *Plan, program: *const ir.Program, used: *std.StringHashMapUnmanaged(void), place_id: ir.PlaceId) !void {
        if (place_id.index() >= program.places.len or self.places[place_id.index()].len != 0) return;
        const place_item = program.places[place_id.index()];
        const fallback = try std.fmt.allocPrint(self.allocator, "place_{d}", .{place_id.index()});
        defer self.allocator.free(fallback);
        const base = if (place_item.name_hint) |hint| try sanitized(self.allocator, hint) else fallback;
        defer if (place_item.name_hint != null) self.allocator.free(base);
        self.places[place_id.index()] = try uniqueName(self.allocator, used, base);
    }

    fn assignValuePack(self: *Plan, used: *std.StringHashMapUnmanaged(void), pack_id: ir.ValuePackId) !void {
        if (pack_id.index() >= self.value_packs.len or self.value_packs[pack_id.index()].len != 0) return;
        const hint = try std.fmt.allocPrint(self.allocator, "__lifter_pack_{d}", .{pack_id.index()});
        defer self.allocator.free(hint);
        self.value_packs[pack_id.index()] = try uniqueName(self.allocator, used, hint);
    }

    fn reserveClosureSources(
        self: *const Plan,
        program: *const ir.Program,
        scope: *const readable_scope.Scope,
        used: *std.StringHashMapUnmanaged(void),
        target: ir.FunctionId,
    ) !void {
        const remaining = program.values.len + program.places.len + program.functions.len + 1;
        for (program.instructions) |instruction| {
            if (!scope.instruction(instruction.id)) continue;
            switch (instruction.operation) {
                .make_closure => |closure| {
                    if (closure.function != target) continue;
                    for (closure.bindings) |binding| switch (binding) {
                        .value => |value_id| try self.reserveValueSource(program, scope, used, value_id, remaining),
                        .place => |place_id| try self.reservePlaceSource(program, scope, used, place_id, remaining),
                    };
                },
                else => {},
            }
        }
    }

    fn reserveValueSource(
        self: *const Plan,
        program: *const ir.Program,
        scope: *const readable_scope.Scope,
        used: *std.StringHashMapUnmanaged(void),
        value_id: ir.ValueId,
        remaining: usize,
    ) std.mem.Allocator.Error!void {
        if (remaining == 0 or value_id.index() >= program.values.len) return;
        if (self.value(value_id)) |name| try used.put(self.allocator, name, {});
        const capture_id = switch (program.values[value_id.index()].origin) {
            .capture => |id| id,
            else => return,
        };
        try self.reserveIncomingCaptureSources(program, scope, used, program.values[value_id.index()].function, capture_id, remaining - 1);
    }

    fn reservePlaceSource(
        self: *const Plan,
        program: *const ir.Program,
        scope: *const readable_scope.Scope,
        used: *std.StringHashMapUnmanaged(void),
        place_id: ir.PlaceId,
        remaining: usize,
    ) std.mem.Allocator.Error!void {
        if (remaining == 0 or place_id.index() >= program.places.len) return;
        if (self.place(place_id)) |name| try used.put(self.allocator, name, {});
        const capture_id = switch (program.places[place_id.index()].origin) {
            .capture => |id| id,
            else => return,
        };
        try self.reserveIncomingCaptureSources(program, scope, used, program.places[place_id.index()].function, capture_id, remaining - 1);
    }

    fn reserveIncomingCaptureSources(
        self: *const Plan,
        program: *const ir.Program,
        scope: *const readable_scope.Scope,
        used: *std.StringHashMapUnmanaged(void),
        target: ir.FunctionId,
        capture_id: ir.CaptureId,
        remaining: usize,
    ) std.mem.Allocator.Error!void {
        if (target.index() >= program.functions.len) return;
        const capture_index = findCaptureIndex(program.functions[target.index()].captures, capture_id) orelse return;
        for (program.instructions) |instruction| {
            if (!scope.instruction(instruction.id)) continue;
            switch (instruction.operation) {
                .make_closure => |closure| {
                    if (closure.function != target or capture_index >= closure.bindings.len) continue;
                    switch (closure.bindings[capture_index]) {
                        .value => |value_id| try self.reserveValueSource(program, scope, used, value_id, remaining),
                        .place => |place_id| try self.reservePlaceSource(program, scope, used, place_id, remaining),
                    }
                },
                else => {},
            }
        }
    }

    fn freeNames(self: *Plan) void {
        for (self.values) |name| if (name.len != 0) self.allocator.free(name);
        for (self.value_packs) |name| if (name.len != 0) self.allocator.free(name);
        for (self.places) |name| if (name.len != 0) self.allocator.free(name);
        for (self.functions) |name| if (name.len != 0) self.allocator.free(name);
        for (self.external_bindings) |name| if (name.len != 0) self.allocator.free(name);
        for (self.runtime_capabilities) |name| if (name.len != 0) self.allocator.free(name);
        if (self.storage_name.len != 0) self.allocator.free(self.storage_name);
        if (self.value_storage_name.len != 0) self.allocator.free(self.value_storage_name);
    }
};

fn markNativeIterationBodyParameters(program: *const ir.Program, marked: []bool) void {
    for (program.blocks) |header| {
        const transition = iteration_protocol.transitionForHeader(program, header) orelse continue;
        const iteration_values = switch (transition.operation) {
            .numeric_for_next => if (transition.results.len == 4) transition.results[3..4] else continue,
            .generic_for_next => |operation| if (operation.variable_count != 0 and
                transition.results.len == @as(usize, operation.variable_count) + 3)
                transition.results[3..]
            else
                continue,
            else => continue,
        };
        const branch = switch (header.terminator) {
            .branch => |value| value,
            else => continue,
        };
        const edges = [_]ir.Edge{ branch.then_edge, branch.else_edge };
        for (edges) |edge| {
            if (edge.target.index() >= program.blocks.len or
                edge.arguments.len != iteration_values.len or
                !std.mem.eql(ir.ValueId, edge.arguments, iteration_values))
            {
                continue;
            }
            const body = program.blocks[edge.target.index()];
            if (body.parameters.len != iteration_values.len) continue;
            for (body.parameters) |parameter| {
                if (parameter.index() < marked.len) marked[parameter.index()] = true;
            }
        }
    }
}

fn markPrivatePlaceStorage(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    storage_places: []bool,
    target: luau_runtime.Target,
) !void {
    const protected_places = try allocator.alloc(bool, program.places.len);
    defer allocator.free(protected_places);
    @memset(protected_places, false);
    @memset(storage_places, false);

    for (program.instructions) |instruction| switch (instruction.operation) {
        .call_repeated_table_get => |operation| if (operation.counter) |place_id| markPlace(protected_places, place_id),
        .make_closure => |closure| for (closure.bindings) |binding| switch (binding) {
            .value => {},
            .place => |place_id| markPlace(protected_places, place_id),
        },
        else => {},
    };
    for (program.captures) |capture| switch (capture.kind) {
        .immutable_value => {},
        .shared_place => |place_id| markPlace(protected_places, place_id),
    };
    for (program.functions) |function_item| {
        if (!functionNeedsPrivateStorage(program, function_item, target)) continue;
        for (program.places) |place| {
            if (place.id.index() >= storage_places.len or place.function != function_item.id) continue;
            storage_places[place.id.index()] = place.origin == .local and !protected_places[place.id.index()];
        }
    }
}

fn functionNeedsPrivateStorage(
    program: *const ir.Program,
    function_item: ir.Function,
    target: luau_runtime.Target,
) bool {
    switch (target) {
        .direct_locals_luau => return false,
        .standard_luau => {},
    }

    // The standard target retains the conservative fallback used before
    // target-specific pressure evidence was available. Count every binding
    // class that can occupy a lexical register, not only mutable places. A
    // function with many SSA values or packs can exceed the local-register
    // ceiling even when its place count alone does not.
    var potential_locals = function_item.parameters.len;
    for (program.values) |value| {
        if (value.function != function_item.id) continue;
        switch (value.origin) {
            .parameter => {},
            else => potential_locals = std.math.add(usize, potential_locals, 1) catch return true,
        }
    }
    for (program.value_packs) |pack| {
        if (pack.function == function_item.id) {
            potential_locals = std.math.add(usize, potential_locals, 1) catch return true;
        }
    }
    for (function_item.local_places) |place_id| {
        if (place_id.index() >= program.places.len) continue;
        const place = program.places[place_id.index()];
        if (place.function == function_item.id and place.origin == .local) {
            potential_locals = std.math.add(usize, potential_locals, 1) catch return true;
        }
    }
    return potential_locals > luau_runtime.max_local_registers;
}

fn markPlace(marks: []bool, place_id: ir.PlaceId) void {
    if (place_id.index() < marks.len) marks[place_id.index()] = true;
}

const PlaceCollector = struct {
    places: []bool,

    pub fn value(_: PlaceCollector, _: ir.ValueId) void {}
    pub fn pack(_: PlaceCollector, _: ir.ValuePackId) void {}

    pub fn place(self: PlaceCollector, place_id: ir.PlaceId) void {
        if (place_id.index() < self.places.len) self.places[place_id.index()] = true;
    }
};

fn findCaptureIndex(captures: []const ir.CaptureId, target: ir.CaptureId) ?usize {
    for (captures, 0..) |capture_id, index| if (capture_id == target) return index;
    return null;
}

fn entryNeedsShiftedVarargs(program: *const ir.Program) bool {
    if (program.entry_function.index() >= program.functions.len) return false;
    const entry = program.functions[program.entry_function.index()];
    return entry.is_variadic and entry.vararg_pack != null and
        (entry.parameters.len != 0 or program.external_bindings.len != 0);
}

fn uniqueName(allocator: std.mem.Allocator, used: *std.StringHashMapUnmanaged(void), raw_base: []const u8) ![]const u8 {
    const base = if (luau_syntax.isIdentifier(raw_base)) try allocator.dupe(u8, raw_base) else try sanitized(allocator, raw_base);
    errdefer allocator.free(base);
    if (!used.contains(base)) {
        try used.put(allocator, base, {});
        return base;
    }
    var suffix: usize = 2;
    while (true) : (suffix += 1) {
        const candidate = try std.fmt.allocPrint(allocator, "{s}_{d}", .{ base, suffix });
        if (!used.contains(candidate)) {
            allocator.free(base);
            try used.put(allocator, candidate, {});
            return candidate;
        }
        allocator.free(candidate);
    }
}

fn sanitized(allocator: std.mem.Allocator, hint: []const u8) ![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    if (hint.len == 0 or !isIdentifierStart(hint[0])) try output.appendSlice(allocator, "value_");
    for (hint) |byte| try output.append(allocator, if (isIdentifierContinue(byte)) byte else '_');
    if (output.items.len == 0) try output.appendSlice(allocator, "value");
    if (!luau_syntax.isIdentifier(output.items)) try output.appendSlice(allocator, "_value");
    return output.toOwnedSlice(allocator);
}

fn prefixedHint(allocator: std.mem.Allocator, prefix: []const u8, hint: []const u8) ![]u8 {
    const clean = try sanitized(allocator, hint);
    defer allocator.free(clean);
    return std.fmt.allocPrint(allocator, "{s}{s}", .{ prefix, clean });
}

fn isIdentifierStart(byte: u8) bool {
    return byte == '_' or (byte >= 'a' and byte <= 'z') or (byte >= 'A' and byte <= 'Z');
}

fn isIdentifierContinue(byte: u8) bool {
    return isIdentifierStart(byte) or (byte >= '0' and byte <= '9');
}

test "standard storage fallback counts values and packs" {
    const function_id = ir.FunctionId.fromIndex(0);
    const value_count = 67;
    const pack_count = 2;
    const place_count = 150;
    var values: [value_count]ir.Value = undefined;
    var packs: [pack_count]ir.ValuePack = undefined;
    var places: [place_count]ir.Place = undefined;
    var local_place_ids: [place_count]ir.PlaceId = undefined;

    for (&values, 0..) |*value, index| {
        value.* = .{
            .id = ir.ValueId.fromIndex(index),
            .function = function_id,
            .origin = if (index == 0)
                .{ .parameter = 0 }
            else
                .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(index), .index = 0 } },
        };
    }
    for (&packs, 0..) |*pack, index| {
        pack.* = .{
            .id = ir.ValuePackId.fromIndex(index),
            .function = function_id,
            .origin = .{ .instruction_result = ir.InstructionId.fromIndex(index) },
        };
    }
    for (&places, 0..) |*place, index| {
        const place_id = ir.PlaceId.fromIndex(index);
        local_place_ids[index] = place_id;
        place.* = .{
            .id = place_id,
            .function = function_id,
            .origin = .{ .local = @intCast(index) },
        };
    }

    const function_item: ir.Function = .{
        .id = function_id,
        .parameters = &.{ir.ValueId.fromIndex(0)},
        .local_places = &local_place_ids,
        .blocks = &.{},
        .entry_block = ir.BlockId.fromIndex(0),
    };
    const program: ir.Program = .{
        .program_id = "storage-pressure",
        .entry_function = function_id,
        .functions = &.{function_item},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .value_packs = &packs,
        .places = &places,
    };

    try std.testing.expect(functionNeedsPrivateStorage(&program, function_item, .standard_luau));
    try std.testing.expect(!functionNeedsPrivateStorage(&program, function_item, .direct_locals_luau));
}

test "names are sanitized and deterministically disambiguated" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = ir.ValueId.fromIndex(0), .function = function_id, .name_hint = "result", .origin = .{ .parameter = 0 } },
        .{ .id = ir.ValueId.fromIndex(1), .function = function_id, .name_hint = "result", .origin = .{ .parameter = 1 } },
        .{ .id = ir.ValueId.fromIndex(2), .function = function_id, .name_hint = "return", .origin = .{ .parameter = 2 } },
        .{ .id = ir.ValueId.fromIndex(3), .function = function_id, .name_hint = "pcall", .origin = .{ .parameter = 3 } },
        .{ .id = ir.ValueId.fromIndex(4), .function = function_id, .name_hint = "xpcall", .origin = .{ .parameter = 4 } },
    };
    const blocks = [_]ir.Block{.{ .id = block_id, .function = function_id, .terminator = .{ .return_values = &.{} } }};
    const functions = [_]ir.Function{.{ .id = function_id, .name_hint = "entry-point", .parameters = &.{ ir.ValueId.fromIndex(0), ir.ValueId.fromIndex(1), ir.ValueId.fromIndex(2), ir.ValueId.fromIndex(3), ir.ValueId.fromIndex(4) }, .blocks = &.{block_id}, .entry_block = block_id }};
    const program: ir.Program = .{ .program_id = "name-plan", .entry_function = function_id, .functions = &functions, .blocks = &blocks, .instructions = &.{}, .values = &values };
    var plan = try Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqualStrings("result", plan.value(ir.ValueId.fromIndex(0)).?);
    try std.testing.expectEqualStrings("result_2", plan.value(ir.ValueId.fromIndex(1)).?);
    try std.testing.expectEqualStrings("return_value", plan.value(ir.ValueId.fromIndex(2)).?);
    try std.testing.expectEqualStrings("pcall_2", plan.value(ir.ValueId.fromIndex(3)).?);
    try std.testing.expectEqualStrings("xpcall_2", plan.value(ir.ValueId.fromIndex(4)).?);
    try std.testing.expectEqualStrings("fn_entry_point", plan.function(function_id).?);
}

test "runtime captures do not shadow admitted ambient names" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const ambient_id = ir.InstructionId.fromIndex(0);
    const protected_id = ir.InstructionId.fromIndex(1);
    const callee = ir.ValueId.fromIndex(0);
    const ambient_value = ir.ValueId.fromIndex(1);
    const protected_value = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .name_hint = "__lifter_pcall", .origin = .{ .parameter = 0 } },
        .{ .id = ambient_value, .function = function_id, .name_hint = "ambient_value", .origin = .{ .instruction_result = .{ .instruction = ambient_id, .index = 0 } } },
        .{ .id = protected_value, .function = function_id, .name_hint = "protected_value", .origin = .{ .instruction_result = .{ .instruction = protected_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = ambient_id,
            .block = block_id,
            .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "__lifter_pcall" } },
            .results = &.{ambient_value},
            .effects = .semantic_environment_read,
        },
        .{
            .id = protected_id,
            .block = block_id,
            .operation = .{ .protected_call = .{
                .callee = callee,
                .arguments = &.{},
                .result_arity = .{ .fixed = 1 },
            } },
            .results = &.{protected_value},
            .effects = .protected_invocation,
        },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ ambient_id, protected_id },
        .terminator = .{ .return_values = &.{ ambient_value, protected_value } },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{callee},
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "runtime-capture-name-collision",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var plan = try Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqualStrings("__lifter_pcall_2", plan.runtimeCapability(.pcall).?);
    try std.testing.expectEqualStrings("__lifter_pcall_3", plan.value(callee).?);
}

test "external binding locals do not shadow admitted or captured names" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const captured = ir.ValueId.fromIndex(0);
    const ambient = ir.ValueId.fromIndex(1);
    const capture_id = ir.CaptureId.fromIndex(0);
    const binding_id = ir.ExternalBindingId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = captured, .function = function_id, .name_hint = "__lifter_external_value_0", .origin = .{ .capture = capture_id } },
        .{ .id = ambient, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } } },
    };
    const captures = [_]ir.Capture{.{ .id = capture_id, .function = function_id, .kind = .{ .immutable_value = captured } }};
    const bindings = [_]ir.ExternalBinding{.{ .id = binding_id, .kind = .immutable_value }};
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = block_id,
        .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "__lifter_external_value_0" } },
        .results = &.{ambient},
        .effects = .semantic_environment_read,
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{instruction_id},
        .terminator = .{ .return_values = &.{ captured, ambient } },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .captures = &.{capture_id},
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "external-binding-name-collision",
        .entry_function = function_id,
        .entry_bindings = &.{binding_id},
        .external_bindings = &bindings,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .captures = &captures,
    };

    var plan = try Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqualStrings("__lifter_external_value_0_2", plan.externalBinding(binding_id).?);
    try std.testing.expectEqualStrings("__lifter_external_value_0_3", plan.value(captured).?);
}

test "lexical namespaces protect global symbols while allowing unrelated ancestor names" {
    const f_first = ir.FunctionId.fromIndex(0);
    const f_second = ir.FunctionId.fromIndex(1);
    const b_first = ir.BlockId.fromIndex(0);
    const b_second = ir.BlockId.fromIndex(1);
    const i_global = ir.InstructionId.fromIndex(0);
    const i_place = ir.InstructionId.fromIndex(1);
    const v_function = ir.ValueId.fromIndex(0);
    const v_global = ir.ValueId.fromIndex(1);
    const v_place = ir.ValueId.fromIndex(2);
    const v_first_result = ir.ValueId.fromIndex(3);
    const v_second_result = ir.ValueId.fromIndex(4);
    const values = [_]ir.Value{
        .{ .id = v_function, .function = f_first, .name_hint = "fn_worker", .origin = .{ .parameter = 0 } },
        .{ .id = v_global, .function = f_first, .name_hint = "print", .origin = .{ .parameter = 1 } },
        .{ .id = v_place, .function = f_first, .name_hint = "state", .origin = .{ .parameter = 2 } },
        .{ .id = v_first_result, .function = f_first, .name_hint = "result", .origin = .{ .parameter = 3 } },
        .{ .id = v_second_result, .function = f_second, .name_hint = "result", .origin = .{ .parameter = 0 } },
    };
    const places = [_]ir.Place{.{ .id = ir.PlaceId.fromIndex(0), .function = f_first, .name_hint = "state", .origin = .{ .local = 0 } }};
    const instructions = [_]ir.Instruction{
        .{
            .id = i_global,
            .block = b_first,
            .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "print" } },
            .results = &.{},
            .effects = .semantic_environment_read,
        },
        .{
            .id = i_place,
            .block = b_first,
            .operation = .{ .place_write = .{ .place = ir.PlaceId.fromIndex(0), .value = v_place } },
            .results = &.{},
            .effects = .place_write,
        },
    };
    const blocks = [_]ir.Block{
        .{ .id = b_first, .function = f_first, .instructions = &.{ i_global, i_place }, .terminator = .{ .return_values = &.{} } },
        .{ .id = b_second, .function = f_second, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{
        .{ .id = f_first, .name_hint = "worker", .parameters = &.{ v_function, v_global, v_place, v_first_result }, .local_places = &.{ir.PlaceId.fromIndex(0)}, .blocks = &.{b_first}, .entry_block = b_first },
        .{ .id = f_second, .name_hint = "worker", .lexical_parent = f_first, .parameters = &.{v_second_result}, .blocks = &.{b_second}, .entry_block = b_second },
    };
    const program: ir.Program = .{
        .program_id = "shared-name-plan",
        .entry_function = f_first,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };
    var plan = try Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqualStrings("fn_worker", plan.function(f_first).?);
    try std.testing.expectEqualStrings("fn_worker_2", plan.function(f_second).?);
    try std.testing.expectEqualStrings("fn_worker_3", plan.value(v_function).?);
    try std.testing.expectEqualStrings("print_2", plan.value(v_global).?);
    try std.testing.expectEqualStrings("state", plan.value(v_place).?);
    try std.testing.expectEqualStrings("state_2", plan.place(ir.PlaceId.fromIndex(0)).?);
    try std.testing.expectEqualStrings("result", plan.value(v_first_result).?);
    try std.testing.expectEqualStrings("result", plan.value(v_second_result).?);
}

test "closure namespaces reserve the exact captured source names" {
    const fixture = @import("fixtures.zig").immutable_closure_module;
    var values = fixture.values;
    values[fixture.v_base.index()].name_hint = "shared";
    values[fixture.v_delta.index()].name_hint = "shared";
    var program = fixture.program;
    program.values = &values;

    var plan = try Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqualStrings("shared", plan.value(fixture.v_base).?);
    try std.testing.expectEqualStrings("shared_2", plan.value(fixture.v_delta).?);
}

test "unreachable entities do not reserve runtime names" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const dead_id = ir.BlockId.fromIndex(1);
    const dead_global_id = ir.InstructionId.fromIndex(0);
    const dead_shared_id = ir.InstructionId.fromIndex(1);
    const dead_write_id = ir.InstructionId.fromIndex(2);
    const live_name_id = ir.InstructionId.fromIndex(3);
    const live_shared_id = ir.InstructionId.fromIndex(4);
    const live_write_id = ir.InstructionId.fromIndex(5);
    const dead_global_value = ir.ValueId.fromIndex(0);
    const dead_shared_value = ir.ValueId.fromIndex(1);
    const live_name_value = ir.ValueId.fromIndex(2);
    const live_shared_value = ir.ValueId.fromIndex(3);
    const dead_place = ir.PlaceId.fromIndex(0);
    const live_place = ir.PlaceId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = dead_global_value, .function = function_id, .name_hint = "dead_global", .origin = .{ .instruction_result = .{ .instruction = dead_global_id, .index = 0 } } },
        .{ .id = dead_shared_value, .function = function_id, .type = .integer, .name_hint = "shared", .origin = .{ .instruction_result = .{ .instruction = dead_shared_id, .index = 0 } } },
        .{ .id = live_name_value, .function = function_id, .type = .integer, .name_hint = "live_name", .origin = .{ .instruction_result = .{ .instruction = live_name_id, .index = 0 } } },
        .{ .id = live_shared_value, .function = function_id, .type = .integer, .name_hint = "shared", .origin = .{ .instruction_result = .{ .instruction = live_shared_id, .index = 0 } } },
    };
    const places = [_]ir.Place{
        .{ .id = dead_place, .function = function_id, .type = .integer, .name_hint = "state", .origin = .{ .local = 0 } },
        .{ .id = live_place, .function = function_id, .type = .integer, .name_hint = "state", .origin = .{ .local = 1 } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = dead_global_id, .block = dead_id, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "live_name" } }, .results = &.{dead_global_value}, .effects = .semantic_environment_read },
        .{ .id = dead_shared_id, .block = dead_id, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{dead_shared_value}, .effects = .pure },
        .{ .id = dead_write_id, .block = dead_id, .operation = .{ .place_write = .{ .place = dead_place, .value = dead_shared_value } }, .results = &.{}, .effects = .place_write },
        .{ .id = live_name_id, .block = entry_id, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{live_name_value}, .effects = .pure },
        .{ .id = live_shared_id, .block = entry_id, .operation = .{ .constant = .{ .integer = "2" } }, .results = &.{live_shared_value}, .effects = .pure },
        .{ .id = live_write_id, .block = entry_id, .operation = .{ .place_write = .{ .place = live_place, .value = live_shared_value } }, .results = &.{}, .effects = .place_write },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .instructions = &.{ live_name_id, live_shared_id, live_write_id }, .terminator = .{ .return_values = &.{ live_name_value, live_shared_value } } },
        .{ .id = dead_id, .function = function_id, .instructions = &.{ dead_global_id, dead_shared_id, dead_write_id }, .terminator = .{ .return_values = &.{ dead_global_value, dead_shared_value } } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .entry_block = entry_id,
        .blocks = &.{ entry_id, dead_id },
        .local_places = &.{ dead_place, live_place },
    };
    const program: ir.Program = .{
        .program_id = "reachable-runtime-names",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };

    var plan = try Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqualStrings("live_name", plan.value(live_name_value).?);
    try std.testing.expectEqualStrings("shared", plan.value(live_shared_value).?);
    try std.testing.expectEqualStrings("state", plan.place(live_place).?);
    try std.testing.expect(plan.value(dead_global_value) == null);
    try std.testing.expect(plan.value(dead_shared_value) == null);
    try std.testing.expect(plan.place(dead_place) == null);
}

test "unreachable closure sites do not reserve child source names" {
    const fixture = @import("fixtures.zig").immutable_closure_module;
    const dead_block = ir.BlockId.fromIndex(fixture.blocks.len);
    const dead_source_instruction = ir.InstructionId.fromIndex(fixture.instructions.len);
    const dead_closure_instruction = ir.InstructionId.fromIndex(fixture.instructions.len + 1);
    const dead_source = ir.ValueId.fromIndex(fixture.values.len);
    const dead_closure = ir.ValueId.fromIndex(fixture.values.len + 1);
    var base_values = fixture.values;
    base_values[fixture.v_delta.index()].name_hint = "shared";
    const values = base_values ++ [_]ir.Value{
        .{ .id = dead_source, .function = fixture.f_factory, .type = .integer, .name_hint = "shared", .origin = .{ .instruction_result = .{ .instruction = dead_source_instruction, .index = 0 } } },
        .{ .id = dead_closure, .function = fixture.f_factory, .type = .function, .name_hint = "dead_adder", .origin = .{ .instruction_result = .{ .instruction = dead_closure_instruction, .index = 0 } } },
    };
    const instructions = fixture.instructions ++ [_]ir.Instruction{
        .{ .id = dead_source_instruction, .block = dead_block, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{dead_source}, .effects = .pure },
        .{ .id = dead_closure_instruction, .block = dead_block, .operation = .{ .make_closure = .{ .function = fixture.f_adder, .bindings = &.{.{ .value = dead_source }} } }, .results = &.{dead_closure}, .effects = .pure },
    };
    const blocks = fixture.blocks ++ [_]ir.Block{.{
        .id = dead_block,
        .function = fixture.f_factory,
        .instructions = &.{ dead_source_instruction, dead_closure_instruction },
        .terminator = .{ .return_values = &.{dead_closure} },
    }};
    var functions = fixture.functions;
    functions[fixture.f_factory.index()].blocks = &.{ fixture.b_factory, dead_block };
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;

    var plan = try Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqualStrings("shared", plan.value(fixture.v_delta).?);
    try std.testing.expect(plan.value(dead_source) == null);
    try std.testing.expect(plan.value(dead_closure) == null);
}
