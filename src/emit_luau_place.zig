const std = @import("std");
const ir = @import("ir.zig");
const luau_runtime = @import("luau_runtime.zig");
const name_plan = @import("name_plan.zig");

pub const PlaceAlias = struct {
    captured: ir.PlaceId,
    source: ir.PlaceId,
};

pub const ValueAlias = struct {
    captured: ir.ValueId,
    source: ir.ValueId,
};

pub const ExternalPlaceAlias = struct {
    captured: ir.PlaceId,
    binding: ir.ExternalBindingId,
};

pub const Alias = union(enum) {
    place: PlaceAlias,
    value: ValueAlias,
    external_place: ExternalPlaceAlias,
};

pub const ResolvedPlace = union(enum) {
    place: ir.PlaceId,
    external_binding: ir.ExternalBindingId,
};

pub fn emitName(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    names: *const name_plan.Plan,
    program: *const ir.Program,
    place_id: ir.PlaceId,
    aliases: []const Alias,
) !void {
    const resolved = resolve(place_id, aliases) orelse return error.UnsupportedOperation;
    const direct = switch (resolved) {
        .place => |value| value,
        .external_binding => return error.UnsupportedOperation,
    };
    if (direct.index() >= program.places.len) return error.UnsupportedOperation;
    if (program.places[direct.index()].origin == .capture) return error.UnsupportedOperation;
    try emitResolvedName(output, allocator, names, direct);
}

pub fn emitRead(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    names: *const name_plan.Plan,
    program: *const ir.Program,
    place_id: ir.PlaceId,
    aliases: []const Alias,
) !void {
    const resolved = resolve(place_id, aliases) orelse return error.UnsupportedOperation;
    switch (resolved) {
        .place => try emitName(output, allocator, names, program, place_id, aliases),
        .external_binding => |binding_id| {
            try output.appendSlice(allocator, names.runtimeCapability(.rawget) orelse return error.UnsupportedOperation);
            try output.append(allocator, '(');
            try emitExternalBindingName(output, allocator, names, binding_id);
            try output.appendSlice(allocator, ", 1)");
        },
    }
}

pub fn emitDirectName(output: *std.ArrayList(u8), allocator: std.mem.Allocator, names: *const name_plan.Plan, place_id: ir.PlaceId) !void {
    try output.appendSlice(allocator, names.place(place_id) orelse return error.UnsupportedOperation);
}

fn emitResolvedName(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    names: *const name_plan.Plan,
    place_id: ir.PlaceId,
) !void {
    if (!names.placeUsesStorage(place_id)) return emitDirectName(output, allocator, names, place_id);
    try output.appendSlice(allocator, names.placeStorageName() orelse return error.UnsupportedOperation);
    const key = try std.fmt.allocPrint(allocator, "[{d}]", .{place_id.index()});
    defer allocator.free(key);
    try output.appendSlice(allocator, key);
}

pub fn emitExternalBindingName(output: *std.ArrayList(u8), allocator: std.mem.Allocator, names: *const name_plan.Plan, binding_id: ir.ExternalBindingId) !void {
    try output.appendSlice(allocator, names.externalBinding(binding_id) orelse return error.UnsupportedOperation);
}

pub fn resolve(place_id: ir.PlaceId, aliases: []const Alias) ?ResolvedPlace {
    var current = place_id;
    var remaining = aliases.len + 1;
    while (remaining != 0) : (remaining -= 1) {
        var found = false;
        var index = aliases.len;
        while (index != 0) {
            index -= 1;
            const alias = aliases[index];
            switch (alias) {
                .place => |place_alias| if (place_alias.captured == current) {
                    current = place_alias.source;
                    found = true;
                    break;
                },
                .external_place => |external_alias| if (external_alias.captured == current) {
                    return .{ .external_binding = external_alias.binding };
                },
                .value => {},
            }
        }
        if (!found) return .{ .place = current };
    }
    return null;
}

pub fn resolveValue(value_id: ir.ValueId, aliases: []const Alias) ?ir.ValueId {
    var current = value_id;
    var remaining = aliases.len + 1;
    while (remaining != 0) : (remaining -= 1) {
        var found = false;
        var index = aliases.len;
        while (index != 0) {
            index -= 1;
            switch (aliases[index]) {
                .place, .external_place => {},
                .value => |value_alias| if (value_alias.captured == current) {
                    current = value_alias.source;
                    found = true;
                    break;
                },
            }
        }
        if (!found) return current;
    }
    return null;
}
