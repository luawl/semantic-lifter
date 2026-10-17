const std = @import("std");
const ir = @import("ir.zig");
const render = @import("emit_luau_expr.zig");
const place_render = @import("emit_luau_place.zig");
const name_plan = @import("name_plan.zig");

pub const PlaceAlias = place_render.Alias;

pub const ValueBinding = struct {
    captured: ir.ValueId,
    source: ir.ValueId,
};

// A per-creation snapshot of a boxed per-execution cell (T7-BOXED-CELL): the creating leaf emits
// `local <captured> = <source holder>` so the child captures the box reference of this execution.
pub const SnapshotBinding = struct {
    captured: ir.PlaceId,
    source: ir.PlaceId,
};

fn sourceIsBoxedCell(source: ir.PlaceId, parent_place_aliases: []const PlaceAlias, stable_values: anytype) bool {
    const resolved = place_render.resolve(source, parent_place_aliases) orelse return false;
    return switch (resolved) {
        .boxed_cell => true,
        // The owning function's terminal self-alias is present in the emitter's aliases (so `.boxed_cell`
        // above covers it and grandchildren), but not in a validator's `&.{}` aliases; there a direct boxed
        // source is recognised through the scope plan when the stable-values provider exposes `isBoxedPlace`.
        .place => |place_id| if (@hasDecl(@TypeOf(stable_values), "isBoxedPlace")) stable_values.isBoxedPlace(place_id) else false,
        .external_binding => false,
    };
}

pub const EntryValueBinding = struct {
    captured: ir.ValueId,
    source: ir.ExternalBindingId,
};

pub const EntryPlan = struct {
    allocator: std.mem.Allocator,
    value_bindings: []EntryValueBinding,
    place_aliases: []PlaceAlias,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program) (std.mem.Allocator.Error || error{InvalidEntryBinding})!EntryPlan {
        if (program.entry_function.index() >= program.functions.len) return error.InvalidEntryBinding;
        const entry = program.functions[program.entry_function.index()];
        if (entry.captures.len != program.entry_bindings.len) return error.InvalidEntryBinding;

        var value_count: usize = 0;
        var place_count: usize = 0;
        for (entry.captures, program.entry_bindings) |capture_id, binding_id| {
            if (capture_id.index() >= program.captures.len or binding_id.index() >= program.external_bindings.len) return error.InvalidEntryBinding;
            const binding = program.external_bindings[binding_id.index()];
            switch (program.captures[capture_id.index()].kind) {
                .immutable_value => {
                    if (binding.kind != .immutable_value) return error.InvalidEntryBinding;
                    value_count += 1;
                },
                .shared_place => {
                    if (binding.kind != .shared_place) return error.InvalidEntryBinding;
                    place_count += 1;
                },
            }
        }

        const value_bindings = try allocator.alloc(EntryValueBinding, value_count);
        errdefer allocator.free(value_bindings);
        const place_aliases = try allocator.alloc(PlaceAlias, place_count);
        errdefer allocator.free(place_aliases);
        var next_value: usize = 0;
        var next_place: usize = 0;
        for (entry.captures, program.entry_bindings) |capture_id, binding_id| switch (program.captures[capture_id.index()].kind) {
            .immutable_value => |captured| {
                value_bindings[next_value] = .{ .captured = captured, .source = binding_id };
                next_value += 1;
            },
            .shared_place => |captured| {
                place_aliases[next_place] = .{ .external_place = .{ .captured = captured, .binding = binding_id } };
                next_place += 1;
            },
        };
        return .{ .allocator = allocator, .value_bindings = value_bindings, .place_aliases = place_aliases };
    }

    pub fn deinit(self: *EntryPlan) void {
        self.allocator.free(self.value_bindings);
        self.allocator.free(self.place_aliases);
        self.* = undefined;
    }
};

pub const ClosurePlan = struct {
    allocator: std.mem.Allocator,
    value_bindings: []ValueBinding,
    place_aliases: []PlaceAlias,
    snapshot_bindings: []SnapshotBinding,

    pub fn init(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        target: ir.Function,
        closure: ir.Closure,
        parent_place_aliases: []const PlaceAlias,
    ) (std.mem.Allocator.Error || error{InvalidClosureBinding})!ClosurePlan {
        return initWithStableValues(allocator, program, target, closure, parent_place_aliases, NoStableValues{});
    }

    pub fn initWithStableValues(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        target: ir.Function,
        closure: ir.Closure,
        parent_place_aliases: []const PlaceAlias,
        stable_values: anytype,
    ) (std.mem.Allocator.Error || error{InvalidClosureBinding})!ClosurePlan {
        var value_count: usize = 0;
        var alias_count: usize = parent_place_aliases.len;
        var snapshot_count: usize = 0;
        for (target.captures, closure.bindings) |capture_id, binding| switch (program.captures[capture_id.index()].kind) {
            .immutable_value => {
                const source = switch (binding) {
                    .value => |value_id| value_id,
                    .place => return error.InvalidClosureBinding,
                };
                if (canAliasImmutableSource(program, source, stable_values)) alias_count += 1 else value_count += 1;
            },
            .shared_place => switch (binding) {
                .place => |place_id| {
                    alias_count += 1;
                    if (sourceIsBoxedCell(place_id, parent_place_aliases, stable_values)) snapshot_count += 1;
                },
                .value => return error.InvalidClosureBinding,
            },
        };

        const value_bindings = try allocator.alloc(ValueBinding, value_count);
        errdefer allocator.free(value_bindings);
        const place_aliases = try allocator.alloc(PlaceAlias, alias_count);
        errdefer allocator.free(place_aliases);
        @memcpy(place_aliases[0..parent_place_aliases.len], parent_place_aliases);
        const snapshot_bindings = try allocator.alloc(SnapshotBinding, snapshot_count);
        errdefer allocator.free(snapshot_bindings);

        var next_value: usize = 0;
        var next_alias = parent_place_aliases.len;
        var next_snapshot: usize = 0;
        for (target.captures, closure.bindings) |capture_id, binding| {
            switch (program.captures[capture_id.index()].kind) {
                .immutable_value => |captured| {
                    const source = switch (binding) {
                        .value => |value_id| value_id,
                        .place => return error.InvalidClosureBinding,
                    };
                    if (canAliasImmutableSource(program, source, stable_values)) {
                        place_aliases[next_alias] = .{ .value = .{ .captured = captured, .source = source } };
                        next_alias += 1;
                    } else {
                        value_bindings[next_value] = .{ .captured = captured, .source = source };
                        next_value += 1;
                    }
                },
                .shared_place => |captured| {
                    const source = switch (binding) {
                        .place => |place_id| place_id,
                        .value => return error.InvalidClosureBinding,
                    };
                    if (sourceIsBoxedCell(source, parent_place_aliases, stable_values)) {
                        place_aliases[next_alias] = .{ .boxed_place = .{ .captured = captured, .holder = captured } };
                        next_alias += 1;
                        snapshot_bindings[next_snapshot] = .{ .captured = captured, .source = source };
                        next_snapshot += 1;
                    } else {
                        place_aliases[next_alias] = .{ .place = .{ .captured = captured, .source = source } };
                        next_alias += 1;
                    }
                },
            }
        }

        return .{
            .allocator = allocator,
            .value_bindings = value_bindings,
            .place_aliases = place_aliases,
            .snapshot_bindings = snapshot_bindings,
        };
    }

    pub fn deinit(self: *ClosurePlan) void {
        self.allocator.free(self.value_bindings);
        self.allocator.free(self.place_aliases);
        self.allocator.free(self.snapshot_bindings);
    }
};

const NoStableValues = struct {
    pub fn contains(_: NoStableValues, _: ir.ValueId) bool {
        return false;
    }
    pub fn isBoxedPlace(_: NoStableValues, _: ir.PlaceId) bool {
        return false;
    }
};

fn canAliasImmutableSource(program: *const ir.Program, source: ir.ValueId, stable_values: anytype) bool {
    if (source.index() >= program.values.len) return false;
    return switch (program.values[source.index()].origin) {
        .parameter, .capture => true,
        .instruction_result, .block_parameter => stable_values.contains(source),
    };
}

pub fn emitRead(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    value_plan: render.ValuePlan,
    instruction: ir.Instruction,
    place_id: ir.PlaceId,
    indent: []const u8,
    declare_result: bool,
    place_aliases: []const PlaceAlias,
) !void {
    try output.appendSlice(allocator, indent);
    if (declare_result and !value_plan.names.valueUsesStorage(instruction.results[0])) try output.appendSlice(allocator, "local ");
    try render.valueName(output, allocator, value_plan.names, instruction.results[0]);
    try output.appendSlice(allocator, " = ");
    try place_render.emitRead(output, allocator, value_plan.names, program, place_id, place_aliases);
    try output.append(allocator, '\n');
}

pub fn emitWrite(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    value_plan: render.ValuePlan,
    instruction: ir.Instruction,
    operation: ir.PlaceWrite,
    indent: []const u8,
    declare_place: bool,
    place_aliases: []const PlaceAlias,
) !void {
    try output.appendSlice(allocator, indent);
    const resolved = place_render.resolve(operation.place, place_aliases) orelse return error.UnsupportedOperation;
    switch (resolved) {
        .place => {
            if (declare_place and !value_plan.names.placeUsesStorage(resolved.place)) {
                try output.appendSlice(allocator, "local ");
            }
            try emitPlaceName(output, allocator, value_plan.names, program, operation.place, place_aliases);
            try output.appendSlice(allocator, " = ");
            try render.valueUseScalar(output, allocator, program, value_plan, operation.value);
            try output.append(allocator, '\n');
        },
        .external_binding => |binding_id| {
            if (declare_place) return error.UnsupportedOperation;
            try render.runtimeCallStart(output, allocator, value_plan, .rawset);
            try place_render.emitExternalBindingName(output, allocator, value_plan.names, binding_id);
            try output.appendSlice(allocator, ", 1, ");
            try render.valueUseScalar(output, allocator, program, value_plan, operation.value);
            try output.appendSlice(allocator, ")\n");
        },
        .boxed_cell => {
            // A boxed per-execution cell (T7-BOXED-CELL): the allocating origin write makes a fresh box
            // `<holder> = { value }`; every other write stores through the slot `<holder>[1] = value`.
            if (declare_place) return error.UnsupportedOperation;
            if (placeWriteIsBoxAllocation(program, operation.place, instruction)) {
                try place_render.emitBoxHolderName(output, allocator, value_plan.names, program, operation.place, place_aliases);
                try output.appendSlice(allocator, " = { ");
                try render.valueUseScalar(output, allocator, program, value_plan, operation.value);
                try output.appendSlice(allocator, " }\n");
            } else {
                try emitPlaceName(output, allocator, value_plan.names, program, operation.place, place_aliases);
                try output.appendSlice(allocator, " = ");
                try render.valueUseScalar(output, allocator, program, value_plan, operation.value);
                try output.append(allocator, '\n');
            }
        },
    }
}

// The place_write at a boxed cell's origin instruction is the allocation (`<holder> = { value }`);
// any other write of the same place stores through the box slot (T7-BOXED-CELL).
pub fn placeWriteIsBoxAllocation(program: *const ir.Program, place_id: ir.PlaceId, instruction: ir.Instruction) bool {
    if (place_id.index() >= program.places.len) return false;
    return switch (program.places[place_id.index()].origin) {
        .instruction => |allocation| allocation == instruction.id,
        else => false,
    };
}

pub fn emitPlaceName(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    names: *const name_plan.Plan,
    program: *const ir.Program,
    place_id: ir.PlaceId,
    place_aliases: []const PlaceAlias,
) !void {
    try place_render.emitName(output, allocator, names, program, place_id, place_aliases);
}

test "immutable lexical aliases require a stable emitted binding" {
    const fixture = @import("fixtures.zig").immutable_closure_module;
    const closure = fixture.instructions[fixture.i_make_adder.index()].operation.make_closure;

    var parameter_plan = try ClosurePlan.init(std.testing.allocator, &fixture.program, fixture.functions[fixture.f_adder.index()], closure, &.{});
    defer parameter_plan.deinit();
    try std.testing.expectEqual(@as(usize, 0), parameter_plan.value_bindings.len);
    try std.testing.expectEqual(@as(usize, 1), parameter_plan.place_aliases.len);
    try std.testing.expectEqual(
        place_render.ValueAlias{ .captured = fixture.v_captured_base, .source = fixture.v_base },
        parameter_plan.place_aliases[0].value,
    );

    var values = fixture.values;
    values[fixture.v_base.index()].origin = .{ .block_parameter = .{ .block = ir.BlockId.fromIndex(0), .index = 0 } };
    var program = fixture.program;
    program.values = &values;
    const StableValue = struct {
        id: ir.ValueId,

        pub fn contains(self: @This(), value_id: ir.ValueId) bool {
            return self.id == value_id;
        }
        pub fn isBoxedPlace(_: @This(), _: ir.PlaceId) bool {
            return false;
        }
    };
    var block_parameter_plan = try ClosurePlan.initWithStableValues(
        std.testing.allocator,
        &program,
        fixture.functions[fixture.f_adder.index()],
        closure,
        &.{},
        StableValue{ .id = fixture.v_base },
    );
    defer block_parameter_plan.deinit();
    try std.testing.expectEqual(@as(usize, 0), block_parameter_plan.value_bindings.len);
    try std.testing.expectEqual(@as(usize, 1), block_parameter_plan.place_aliases.len);

    values[fixture.v_base.index()].origin = .{ .instruction_result = .{ .instruction = fixture.i_make_adder, .index = 0 } };
    var instruction_plan = try ClosurePlan.init(std.testing.allocator, &program, fixture.functions[fixture.f_adder.index()], closure, &.{});
    defer instruction_plan.deinit();
    try std.testing.expectEqual(@as(usize, 1), instruction_plan.value_bindings.len);
    try std.testing.expectEqual(@as(usize, 0), instruction_plan.place_aliases.len);
}
