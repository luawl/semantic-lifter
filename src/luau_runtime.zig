const std = @import("std");
const dead_code = @import("dead_code.zig");
const ir = @import("ir.zig");
const luau_syntax = @import("luau_syntax.zig");
const readable_scope = @import("readable_scope.zig");
const runtime_uses = @import("runtime_uses.zig");

/// `standard_luau` assumes that every demanded builtin below has its standard
/// identity when the emitted chunk starts. External binding slots, in canonical
/// ID order, precede ordinary entry arguments. Immutable slots are direct
/// values; shared-place slots are table cells whose numeric key 1 is accessed
/// with captured `rawget`/`rawset`. Emission captures builtin identities before
/// executing admitted IR, so later global replacement, table aliasing, field
/// mutation, or unknown calls cannot redirect semantic lowerings.
pub const Target = enum {
    standard_luau,
    /// Prefer lexical locals even when the conservative whole-function
    /// fallback would place private locals in a table. The caller must pair
    /// this target with sample-specific register-pressure evidence.
    direct_locals_luau,
};

/// The pinned standard-Luau compiler rejects a function or chunk once more
/// than 200 lexical locals, including parameters, need registers at once.
pub const max_local_registers: usize = 200;

/// Expression evaluation and call frames share the bytecode VM's wider
/// register space after lexical-local allocation.
pub const max_registers: usize = 255;

/// A fixed-return bytecode operand stores the value count plus one. Open
/// returns use a separate sentinel and are not subject to this ceiling.
pub const max_fixed_return_values: usize = 254;

/// Parser recursion is shared by enclosing syntax and expression shape. Keep
/// fused expressions far below the pinned parser's exact 1000-level ceiling so
/// ordinary structured context retains deterministic headroom.
pub const max_parser_recursion: usize = 1000;
pub const max_fused_expression_operations: usize = 128;

/// Structured statements and lexical function bodies share recursion with
/// composed branch expressions and fused value expressions. The remainder of
/// the parser budget is reserved for those two 128-operation planners plus
/// ordinary expression, function, and physical-scope syntax.
pub const max_emitted_syntax_nesting: usize = 512;

/// Indentation is presentation only. Capping it prevents deeply structured,
/// still-admitted source from growing quadratically in leading whitespace.
pub const max_source_indent_spaces: usize = 64;

/// Nested functions have a separate bytecode operand space for captured
/// lexical bindings, independent of local and expression registers.
pub const max_upvalue_registers: usize = 200;

/// Child function prototype indices use a separate per-function table. The
/// compiler accepts indices 0 through 32767 and rejects the next child.
pub const max_child_prototypes: usize = 32768;

/// Patched D-encoded branches can use a JUMPX trampoline only while their
/// absolute pre-expansion offset is strictly below this boundary.
pub const max_long_jump_distance: usize = 1 << 23;

/// The pinned O1 compiler has a much larger terminal function-size guard.
/// Jump-bearing functions are constrained first by `max_long_jump_distance`.
pub const max_function_instructions: usize = 1_000_000_000;

/// Each counted emitted entity or value/place/pack use is assigned enough
/// room for its O1 lowering, including auxiliary words and jump trampolines.
pub const max_bytecode_words_per_emission_unit: usize = 8;
pub const max_jump_emission_units: usize = (max_long_jump_distance - 1) / max_bytecode_words_per_emission_unit;

pub const Source = struct {
    global: luau_syntax.RuntimeGlobal,
    method: ?[]const u8 = null,
};

pub const Capability = enum {
    bit32_bnot,
    bit32_band,
    bit32_bor,
    bit32_bxor,
    bit32_lshift,
    bit32_rshift,
    coroutine_create,
    coroutine_resume,
    coroutine_yield,
    error_builtin,
    getfenv,
    getmetatable,
    next,
    pcall,
    rawget,
    rawset,
    select,
    string_format,
    table_unpack,
    type,
    xpcall,

    pub fn source(self: Capability) Source {
        return switch (self) {
            .bit32_bnot => .{ .global = .bit32, .method = "bnot" },
            .bit32_band => .{ .global = .bit32, .method = "band" },
            .bit32_bor => .{ .global = .bit32, .method = "bor" },
            .bit32_bxor => .{ .global = .bit32, .method = "bxor" },
            .bit32_lshift => .{ .global = .bit32, .method = "lshift" },
            .bit32_rshift => .{ .global = .bit32, .method = "rshift" },
            .coroutine_create => .{ .global = .coroutine, .method = "create" },
            .coroutine_resume => .{ .global = .coroutine, .method = "resume" },
            .coroutine_yield => .{ .global = .coroutine, .method = "yield" },
            .error_builtin => .{ .global = .error_builtin },
            .getfenv => .{ .global = .getfenv },
            .getmetatable => .{ .global = .getmetatable },
            .next => .{ .global = .next },
            .pcall => .{ .global = .pcall },
            .rawget => .{ .global = .rawget },
            .rawset => .{ .global = .rawset },
            .select => .{ .global = .select },
            .string_format => .{ .global = .string, .method = "format" },
            .table_unpack => .{ .global = .table, .method = "unpack" },
            .type => .{ .global = .type },
            .xpcall => .{ .global = .xpcall },
        };
    }

    pub fn captureHint(self: Capability) []const u8 {
        return switch (self) {
            .bit32_bnot => "__lifter_bit32_bnot",
            .bit32_band => "__lifter_bit32_band",
            .bit32_bor => "__lifter_bit32_bor",
            .bit32_bxor => "__lifter_bit32_bxor",
            .bit32_lshift => "__lifter_bit32_lshift",
            .bit32_rshift => "__lifter_bit32_rshift",
            .coroutine_create => "__lifter_coroutine_create",
            .coroutine_resume => "__lifter_coroutine_resume",
            .coroutine_yield => "__lifter_coroutine_yield",
            .error_builtin => "__lifter_error",
            .getfenv => "__lifter_getfenv",
            .getmetatable => "__lifter_getmetatable",
            .next => "__lifter_next",
            .pcall => "__lifter_pcall",
            .rawget => "__lifter_rawget",
            .rawset => "__lifter_rawset",
            .select => "__lifter_select",
            .string_format => "__lifter_string_format",
            .table_unpack => "__lifter_table_unpack",
            .type => "__lifter_type",
            .xpcall => "__lifter_xpcall",
        };
    }
};

pub const capabilities = [_]Capability{
    .bit32_bnot,
    .bit32_band,
    .bit32_bor,
    .bit32_bxor,
    .bit32_lshift,
    .bit32_rshift,
    .coroutine_create,
    .coroutine_resume,
    .coroutine_yield,
    .error_builtin,
    .getfenv,
    .getmetatable,
    .next,
    .pcall,
    .rawget,
    .rawset,
    .select,
    .string_format,
    .table_unpack,
    .type,
    .xpcall,
};

pub fn bit32Capability(operator: ir.BinaryOperator) ?Capability {
    return switch (operator) {
        .bit_and => .bit32_band,
        .bit_or => .bit32_bor,
        .bit_xor => .bit32_bxor,
        .shift_left => .bit32_lshift,
        .shift_right => .bit32_rshift,
        else => null,
    };
}

pub const Set = struct {
    flags: [capabilities.len]bool = [_]bool{false} ** capabilities.len,

    pub fn mark(self: *Set, capability: Capability) void {
        self.flags[@intFromEnum(capability)] = true;
    }

    pub fn has(self: Set, capability: Capability) bool {
        return self.flags[@intFromEnum(capability)];
    }

    pub fn isEmpty(self: Set) bool {
        for (self.flags) |required| if (required) return false;
        return true;
    }

    pub fn markOperation(self: *Set, operation: ir.Operation) void {
        switch (operation) {
            .unary => |unary| if (unary.operator == .bit_not) self.mark(.bit32_bnot),
            .binary => |binary| if (bit32Capability(binary.operator)) |capability| self.mark(capability),
            .protected_call => |call| self.mark(if (call.error_handler == null) .pcall else .xpcall),
            .coroutine_create => self.mark(.coroutine_create),
            .coroutine_resume => self.mark(.coroutine_resume),
            .coroutine_yield => self.mark(.coroutine_yield),
            .environment_get => |get| switch (get.mode) {
                .raw => self.mark(.rawget),
                .semantic => if (get.target == .ambient and !luau_syntax.isIdentifier(get.name)) self.mark(.getfenv),
            },
            .environment_set => |set| switch (set.mode) {
                .raw => self.mark(.rawset),
                .semantic => if (set.target == .ambient and !luau_syntax.isIdentifier(set.name)) self.mark(.getfenv),
            },
            .table_get => |get| if (get.mode == .raw) self.mark(.rawget),
            .table_set => |set| if (set.mode == .raw) self.mark(.rawset),
            .table_set_pack => {
                self.mark(.rawset);
                self.mark(.select);
            },
            .call_repeated_table_get => |call| {
                self.mark(.table_unpack);
                // A counter may be a captured shared place, so retain the
                // cell access capabilities even when the current fixture uses
                // an ordinary local place.
                if (call.counter != null) {
                    self.mark(.rawget);
                    self.mark(.rawset);
                }
            },
            .string_interpolate => self.mark(.string_format),
            .generic_for_next => {
                // Arbitrary-CFG emission must reproduce Luau's generalized
                // iteration preparation before invoking the iterator.
                self.mark(.getmetatable);
                self.mark(.next);
                self.mark(.type);
            },
            else => {},
        }
    }

    pub fn markTerminator(self: *Set, terminator: ir.Terminator) void {
        switch (terminator) {
            .throw_error, .unreachable_block => self.mark(.error_builtin),
            else => {},
        }
    }
};

pub const Plan = struct {
    target: Target,
    required: Set,

    pub fn init(target: Target, program: *const ir.Program, scope: *const readable_scope.Scope) Plan {
        return initFiltered(target, program, scope, null);
    }

    pub fn initForEmission(
        target: Target,
        program: *const ir.Program,
        scope: *const readable_scope.Scope,
        dead: *const dead_code.Plan,
    ) Plan {
        return initFiltered(target, program, scope, dead);
    }

    fn initFiltered(
        target: Target,
        program: *const ir.Program,
        scope: *const readable_scope.Scope,
        dead: ?*const dead_code.Plan,
    ) Plan {
        var required: Set = .{};
        for (program.instructions) |instruction| {
            if (scope.instruction(instruction.id) and instructionSurvives(dead, instruction.id)) {
                required.markOperation(instruction.operation);
            }
        }
        for (program.blocks) |block| {
            if (scope.block(block.id)) required.markTerminator(block.terminator);
        }
        markExternalPlaceCapabilities(&required, program, scope, dead);
        markShiftedEntrySelect(&required, program, scope, dead);
        return .{ .target = target, .required = required };
    }

    pub fn requires(self: Plan, capability: Capability) bool {
        return self.required.has(capability);
    }

    pub fn require(self: *Plan, capability: Capability) void {
        self.required.mark(capability);
    }
};

const PackUseProbe = struct {
    target: ir.ValuePackId,
    found: *bool,

    pub fn value(_: PackUseProbe, _: ir.ValueId) void {}

    pub fn pack(self: PackUseProbe, pack_id: ir.ValuePackId) void {
        if (pack_id == self.target) self.found.* = true;
    }

    pub fn place(_: PackUseProbe, _: ir.PlaceId) void {}
};

fn instructionSurvives(dead: ?*const dead_code.Plan, instruction_id: ir.InstructionId) bool {
    const plan = dead orelse return true;
    return !plan.contains(instruction_id) or plan.isInlined(instruction_id);
}

fn markExternalPlaceCapabilities(
    required: *Set,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    dead: ?*const dead_code.Plan,
) void {
    for (program.instructions) |instruction| {
        if (!scope.instruction(instruction.id) or !instructionSurvives(dead, instruction.id)) continue;
        const access = switch (instruction.operation) {
            .place_read => |place_id| .{ place_id, Capability.rawget },
            .place_write => |write| .{ write.place, Capability.rawset },
            else => continue,
        };
        if (placeCanResolveToExternal(program, scope, dead, access[0], program.functions.len + 1)) {
            required.mark(access[1]);
        }
    }
}

fn placeCanResolveToExternal(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    dead: ?*const dead_code.Plan,
    place_id: ir.PlaceId,
    remaining: usize,
) bool {
    if (remaining == 0 or place_id.index() >= program.places.len) return false;
    const place = program.places[place_id.index()];
    const capture_id = switch (place.origin) {
        .capture => |value| value,
        .local, .instruction => return false,
    };
    if (capture_id.index() >= program.captures.len or place.function.index() >= program.functions.len) return false;
    const function = program.functions[place.function.index()];
    const capture_index = findCaptureIndex(function.captures, capture_id) orelse return false;
    if (function.id == program.entry_function) {
        if (capture_index >= program.entry_bindings.len) return false;
        const binding_id = program.entry_bindings[capture_index];
        return binding_id.index() < program.external_bindings.len and
            program.external_bindings[binding_id.index()].kind == .shared_place;
    }

    for (program.instructions) |instruction| {
        if (!scope.instruction(instruction.id) or !instructionSurvives(dead, instruction.id)) continue;
        const closure = switch (instruction.operation) {
            .make_closure => |value| value,
            else => continue,
        };
        if (closure.function != function.id or capture_index >= closure.bindings.len) continue;
        const source = switch (closure.bindings[capture_index]) {
            .place => |value| value,
            .value => continue,
        };
        if (placeCanResolveToExternal(program, scope, dead, source, remaining - 1)) return true;
    }
    return false;
}

fn findCaptureIndex(captures: []const ir.CaptureId, target: ir.CaptureId) ?usize {
    for (captures, 0..) |capture_id, index| if (capture_id == target) return index;
    return null;
}

fn markShiftedEntrySelect(
    required: *Set,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    dead: ?*const dead_code.Plan,
) void {
    if (program.entry_function.index() >= program.functions.len) return;
    const entry = program.functions[program.entry_function.index()];
    if (!entry.is_variadic or (entry.parameters.len == 0 and program.external_bindings.len == 0)) return;
    const pack_id = entry.vararg_pack orelse return;
    var found = false;
    const probe: PackUseProbe = .{ .target = pack_id, .found = &found };
    for (program.instructions) |instruction| {
        if (scope.instruction(instruction.id) and instructionSurvives(dead, instruction.id)) {
            runtime_uses.visitOperationUses(instruction.operation, probe);
        }
    }
    for (program.blocks) |block| {
        if (scope.block(block.id)) runtime_uses.visitTerminatorUses(block.terminator, probe);
    }
    if (found) required.mark(.select);
}

test "runtime capabilities have unique capture hints and valid source names" {
    for (capabilities, 0..) |capability, index| {
        const source = capability.source();
        try std.testing.expect(luau_syntax.isIdentifier(source.global.name()));
        if (source.method) |method| try std.testing.expect(luau_syntax.isIdentifier(method));
        try std.testing.expect(luau_syntax.isIdentifier(capability.captureHint()));
        for (capabilities[0..index]) |prior| {
            try std.testing.expect(!std.mem.eql(u8, prior.captureHint(), capability.captureHint()));
        }
    }
}

test "operation families demand exact runtime capabilities" {
    const value = ir.ValueId.fromIndex(0);
    var none: Set = .{};
    none.markOperation(.{ .binary = .{ .operator = .add, .left = value, .right = value } });
    none.markOperation(.{ .environment_get = .{
        .target = .{ .ambient = {} },
        .name = "ordinary_global",
    } });
    none.markOperation(.{ .environment_set = .{
        .target = .{ .ambient = {} },
        .name = "ordinary_global",
        .value = value,
    } });
    none.markOperation(.{ .table_get = .{ .table = value, .key = value } });
    try std.testing.expect(none.isEmpty());

    var required: Set = .{};
    required.markOperation(.{ .unary = .{ .operator = .bit_not, .operand = value } });
    inline for (.{ ir.BinaryOperator.bit_and, .bit_or, .bit_xor, .shift_left, .shift_right }) |operator| {
        required.markOperation(.{ .binary = .{
            .operator = operator,
            .left = value,
            .right = value,
            .shift_behavior = switch (operator) {
                .shift_left, .shift_right => .luau_bit32,
                else => null,
            },
        } });
    }
    required.markOperation(.{ .protected_call = .{
        .callee = value,
        .arguments = &.{},
        .result_arity = .{ .fixed = 1 },
    } });
    required.markOperation(.{ .protected_call = .{
        .callee = value,
        .error_handler = value,
        .arguments = &.{},
        .result_arity = .{ .fixed = 1 },
    } });
    required.markOperation(.{ .coroutine_create = .{ .callee = value } });
    required.markOperation(.{ .coroutine_resume = .{ .thread = value, .arguments = &.{}, .result_arity = .{ .fixed = 1 } } });
    required.markOperation(.{ .coroutine_yield = .{ .arguments = &.{}, .result_arity = .{ .fixed = 1 } } });
    required.markOperation(.{ .generic_for_next = .{
        .iterator = value,
        .state = value,
        .control = value,
        .initial = value,
        .variable_count = 1,
    } });
    required.markOperation(.{ .environment_get = .{
        .target = .{ .value = value },
        .name = "field",
        .mode = .raw,
    } });
    required.markOperation(.{ .environment_get = .{
        .target = .{ .ambient = {} },
        .name = "not a source identifier",
    } });
    required.markOperation(.{ .table_set = .{
        .table = value,
        .key = value,
        .value = value,
        .mode = .raw,
    } });
    required.markOperation(.{ .string_interpolate = .{ .segments = &.{ "", "" }, .values = &.{value} } });
    required.markTerminator(.{ .throw_error = .{ .value = value, .level = 0 } });
    required.mark(.select);
    required.mark(.table_unpack);

    for (capabilities) |capability| try std.testing.expect(required.has(capability));
}

test "shifted entry select demand requires a reachable vararg pack use" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const dead_id = ir.BlockId.fromIndex(1);
    const parameter = ir.ValueId.fromIndex(0);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = parameter,
        .function = function_id,
        .origin = .{ .parameter = 0 },
    }};
    const packs = [_]ir.ValuePack{.{
        .id = pack_id,
        .function = function_id,
        .origin = .{ .varargs = function_id },
    }};
    var blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .return_values = &.{parameter} } },
        .{ .id = dead_id, .function = function_id, .terminator = .{ .return_pack = pack_id } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{parameter},
        .is_variadic = true,
        .vararg_pack = pack_id,
        .blocks = &.{ entry_id, dead_id },
        .entry_block = entry_id,
    }};
    var program: ir.Program = .{
        .program_id = "runtime-select-demand",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .value_packs = &packs,
    };

    var dead_scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer dead_scope.deinit();
    const dead_plan = Plan.init(.standard_luau, &program, &dead_scope);
    try std.testing.expect(!dead_plan.requires(.select));

    blocks[entry_id.index()].terminator = .{ .return_pack = pack_id };
    var live_scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer live_scope.deinit();
    const live_plan = Plan.init(.standard_luau, &program, &live_scope);
    try std.testing.expect(live_plan.requires(.select));
}
