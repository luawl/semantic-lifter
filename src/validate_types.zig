const std = @import("std");
const ir = @import("ir.zig");
const diagnostics = @import("diagnostics.zig");
const numerals = @import("numerals.zig");

pub fn validateDescriptors(report: *diagnostics.Report, program: *const ir.Program) !void {
    for (program.values, 0..) |value, index| {
        if (!isCanonical(value.type)) try report.add(.invalid_value_type, index);
    }
    for (program.places, 0..) |place, index| {
        if (!isCanonical(place.type)) try report.add(.invalid_place_type, index);
    }
    for (program.external_bindings, 0..) |binding, index| {
        if (!isCanonical(binding.type)) try report.add(.invalid_external_binding_type, index);
    }
    for (program.value_packs, 0..) |pack, index| {
        for (pack.shape.prefix) |value_type| {
            if (!isCanonical(value_type)) {
                try report.add(.invalid_value_pack_shape, index);
                break;
            }
        }
    }
}

pub fn validateEntryBindings(report: *diagnostics.Report, program: *const ir.Program) !void {
    if (program.entry_function.index() >= program.functions.len) return;
    const entry = program.functions[program.entry_function.index()];
    const count = @min(entry.captures.len, program.entry_bindings.len);
    for (0..count) |index| {
        const capture_id = entry.captures[index];
        const binding_id = program.entry_bindings[index];
        if (capture_id.index() >= program.captures.len or binding_id.index() >= program.external_bindings.len) continue;
        const binding = program.external_bindings[binding_id.index()];
        const matches = switch (program.captures[capture_id.index()].kind) {
            .immutable_value => |slot_id| blk: {
                if (binding.kind != .immutable_value or slot_id.index() >= program.values.len) break :blk true;
                break :blk isAssignable(program.values[slot_id.index()].type, binding.type);
            },
            .shared_place => |slot_id| blk: {
                if (binding.kind != .shared_place or slot_id.index() >= program.places.len) break :blk true;
                break :blk sameType(program.places[slot_id.index()].type, binding.type);
            },
        };
        if (!matches) try report.add(.entry_capture_binding_type_mismatch, index);
    }
}

pub fn validateOperationResult(report: *diagnostics.Report, program: *const ir.Program, instruction: ir.Instruction) !void {
    switch (instruction.operation) {
        .place_write => |write| try validatePlaceWrite(report, program, instruction.id, write),
        .make_closure => |closure| try validateClosureBindings(report, program, instruction.id, closure),
        .numeric_for_next => return validateNumericForResults(report, program, instruction),
        .generic_for_next => return validateGenericForResults(report, program, instruction),
        else => {},
    }
    const result_type = singleResultType(program, instruction) orelse return;
    const matches = switch (instruction.operation) {
        .constant => |literal| constantResultMatches(result_type, literal),
        .copy => |source| copyResultMatches(program, result_type, source),
        .unary => |operation| unaryResultMatches(program, result_type, operation),
        .binary => |operation| binaryResultMatches(program, result_type, operation),
        .make_table, .make_table_literal => isKindOrDynamic(result_type, .table),
        .string_interpolate => isKindOrDynamic(result_type, .string),
        .make_closure, .function_ref => isKindOrDynamic(result_type, .function),
        .coroutine_create => isKindOrDynamic(result_type, .thread),
        .place_read => |place_id| placeReadResultMatches(program, result_type, place_id),
        .call,
        .call_repeated_table_get,
        .namecall,
        .protected_call,
        .coroutine_resume,
        .coroutine_yield,
        .environment_get,
        .environment_set,
        .table_get,
        .table_set,
        .table_set_pack,
        .place_write,
        .pack_values,
        .adjust_pack,
        .numeric_for_next,
        .generic_for_next,
        => true,
    };
    if (!matches) try report.add(.operation_result_type_mismatch, instruction.id.index());
}

fn validateNumericForResults(report: *diagnostics.Report, program: *const ir.Program, instruction: ir.Instruction) !void {
    if (instruction.results.len != 4) return;
    const operation = switch (instruction.operation) {
        .numeric_for_next => |value| value,
        else => return,
    };
    const expected = switch (operation.mode) {
        .luau_numeric => [_]ir.TypeKind{ .boolean, .number, .number, .number },
        .semantic_normalized => [_]ir.TypeKind{ .boolean, .dynamic, .dynamic, .dynamic },
    };
    for (instruction.results, expected) |result_id, kind| {
        if (result_id.index() >= program.values.len) continue;
        if (program.values[result_id.index()].type.kind != kind) {
            try report.add(.operation_result_type_mismatch, instruction.id.index());
            return;
        }
    }
}

fn validateGenericForResults(report: *diagnostics.Report, program: *const ir.Program, instruction: ir.Instruction) !void {
    if (instruction.results.len == 0 or instruction.results[0].index() >= program.values.len) return;
    if (program.values[instruction.results[0].index()].type.kind != .boolean) {
        try report.add(.operation_result_type_mismatch, instruction.id.index());
    }
}

pub fn supportsReadableBit32Unary(program: *const ir.Program, instruction: ir.Instruction, operation: ir.Unary) bool {
    return operation.mode == .primitive and
        isU32Value(program, operation.operand) and
        hasSingleU32Result(program, instruction) and
        isExactPure(instruction.effects);
}

pub fn supportsReadableBit32Binary(program: *const ir.Program, instruction: ir.Instruction, operation: ir.Binary) bool {
    return operation.mode == .primitive and
        isU32Value(program, operation.left) and
        isU32Value(program, operation.right) and
        hasSingleU32Result(program, instruction) and
        isExactPure(instruction.effects);
}

pub fn isAssignable(target: ir.ValueType, source: ir.ValueType) bool {
    if (target.kind == .dynamic) return true;
    if (source.kind == .dynamic) return false;
    if (sameType(target, source)) return true;
    if (target.kind == .integer and source.kind == .integer) return integerRangeContains(target, source);
    if (target.kind == .number and source.kind == .number) return target.bit_width >= source.bit_width;
    if (target.kind == .number and source.kind == .integer) return integerFitsSourceNumber(target, source);
    return false;
}

fn integerRangeContains(target: ir.ValueType, source: ir.ValueType) bool {
    if (target.signed == source.signed) return target.bit_width >= source.bit_width;
    return target.signed and !source.signed and target.bit_width > source.bit_width;
}

fn integerFitsSourceNumber(target: ir.ValueType, source: ir.ValueType) bool {
    if (target.bit_width == 64) return true;
    const significand_bits: u16 = 24;
    return if (source.signed)
        source.bit_width <= significand_bits + 1
    else
        source.bit_width <= significand_bits;
}

fn isCanonical(value_type: ir.ValueType) bool {
    return switch (value_type.kind) {
        .integer => value_type.bit_width != 0,
        .number => (value_type.bit_width == 32 or value_type.bit_width == 64) and !value_type.signed,
        .dynamic,
        .nil_value,
        .boolean,
        .string,
        .table,
        .function,
        .thread,
        .userdata,
        .tuple,
        => value_type.bit_width == 0 and !value_type.signed,
    };
}

fn singleResultType(program: *const ir.Program, instruction: ir.Instruction) ?ir.ValueType {
    if (instruction.results.len != 1 or instruction.results[0].index() >= program.values.len) return null;
    return program.values[instruction.results[0].index()].type;
}

fn constantResultMatches(result_type: ir.ValueType, literal: ir.Literal) bool {
    if (result_type.kind == .dynamic) return true;
    return switch (literal) {
        .nil_value => result_type.kind == .nil_value,
        .boolean => result_type.kind == .boolean,
        .integer => |decimal| result_type.kind == .number or
            (result_type.kind == .integer and integerLiteralFits(result_type, decimal)),
        .number, .special_number => result_type.kind == .number,
        .string => result_type.kind == .string,
    };
}

fn integerLiteralFits(result_type: ir.ValueType, decimal: []const u8) bool {
    return if (result_type.signed)
        numerals.signedFitsBits(decimal, result_type.bit_width)
    else
        numerals.unsignedFitsBits(decimal, result_type.bit_width);
}

fn copyResultMatches(program: *const ir.Program, result_type: ir.ValueType, source: ir.ValueId) bool {
    if (source.index() >= program.values.len) return true;
    const source_type = program.values[source.index()].type;
    return isAssignable(result_type, source_type);
}

fn unaryResultMatches(program: *const ir.Program, result_type: ir.ValueType, operation: ir.Unary) bool {
    if (result_type.kind == .dynamic) return true;
    const operand_type = valueType(program, operation.operand) orelse return true;
    return switch (operation.operator) {
        .logical_not => result_type.kind == .boolean,
        .length => result_type.kind == .integer,
        .negate => numericResultMatches(result_type, operand_type, operand_type),
        .bit_not => result_type.kind == .integer,
    };
}

fn binaryResultMatches(program: *const ir.Program, result_type: ir.ValueType, operation: ir.Binary) bool {
    if (result_type.kind == .dynamic) return true;
    const left_type = valueType(program, operation.left) orelse return true;
    const right_type = valueType(program, operation.right) orelse return true;
    return switch (operation.operator) {
        .equal, .not_equal, .less, .less_equal, .greater, .greater_equal => result_type.kind == .boolean,
        .concat => result_type.kind == .string,
        .logical_and, .logical_or => isAssignable(result_type, left_type) and isAssignable(result_type, right_type),
        .divide, .power => result_type.kind == .number,
        .add, .subtract, .multiply, .floor_divide, .modulo => numericResultMatches(result_type, left_type, right_type),
        .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => result_type.kind == .integer,
    };
}

fn numericResultMatches(result_type: ir.ValueType, left_type: ir.ValueType, right_type: ir.ValueType) bool {
    const left_numeric = left_type.kind == .integer or left_type.kind == .number;
    const right_numeric = right_type.kind == .integer or right_type.kind == .number;
    if (!left_numeric or !right_numeric) return result_type.kind == .integer or result_type.kind == .number;
    if (left_type.kind == .number or right_type.kind == .number) return result_type.kind == .number;
    return result_type.kind == .integer or result_type.kind == .number;
}

fn placeReadResultMatches(program: *const ir.Program, result_type: ir.ValueType, place_id: ir.PlaceId) bool {
    if (place_id.index() >= program.places.len) return true;
    return isAssignable(result_type, program.places[place_id.index()].type);
}

fn validatePlaceWrite(
    report: *diagnostics.Report,
    program: *const ir.Program,
    instruction_id: ir.InstructionId,
    write: ir.PlaceWrite,
) !void {
    if (write.place.index() >= program.places.len or write.value.index() >= program.values.len) return;
    if (!isAssignable(program.places[write.place.index()].type, program.values[write.value.index()].type)) {
        try report.add(.place_value_type_mismatch, instruction_id.index());
    }
}

fn validateClosureBindings(
    report: *diagnostics.Report,
    program: *const ir.Program,
    instruction_id: ir.InstructionId,
    closure: ir.Closure,
) !void {
    if (closure.function.index() >= program.functions.len) return;
    const target = program.functions[closure.function.index()];
    const count = @min(target.captures.len, closure.bindings.len);
    for (0..count) |index| {
        const capture_id = target.captures[index];
        if (capture_id.index() >= program.captures.len) continue;
        const matches = switch (program.captures[capture_id.index()].kind) {
            .immutable_value => |slot_id| blk: {
                if (slot_id.index() >= program.values.len or closure.bindings[index] != .value) break :blk true;
                const source_id = closure.bindings[index].value;
                if (source_id.index() >= program.values.len) break :blk true;
                break :blk isAssignable(program.values[slot_id.index()].type, program.values[source_id.index()].type);
            },
            .shared_place => |slot_id| blk: {
                if (slot_id.index() >= program.places.len or closure.bindings[index] != .place) break :blk true;
                const source_id = closure.bindings[index].place;
                if (source_id.index() >= program.places.len) break :blk true;
                break :blk sameType(program.places[slot_id.index()].type, program.places[source_id.index()].type);
            },
        };
        if (!matches) try report.add(.closure_binding_type_mismatch, instruction_id.index());
    }
}

fn isKindOrDynamic(value_type: ir.ValueType, kind: ir.TypeKind) bool {
    return value_type.kind == .dynamic or value_type.kind == kind;
}

fn sameType(left: ir.ValueType, right: ir.ValueType) bool {
    return left.kind == right.kind and left.bit_width == right.bit_width and left.signed == right.signed;
}

fn valueType(program: *const ir.Program, value_id: ir.ValueId) ?ir.ValueType {
    if (value_id.index() >= program.values.len) return null;
    return program.values[value_id.index()].type;
}

fn hasSingleU32Result(program: *const ir.Program, instruction: ir.Instruction) bool {
    return instruction.results.len == 1 and isU32Value(program, instruction.results[0]);
}

fn isU32Value(program: *const ir.Program, value_id: ir.ValueId) bool {
    const value_type = valueType(program, value_id) orelse return false;
    return value_type.kind == .integer and value_type.bit_width == 32 and !value_type.signed;
}

fn isExactPure(effects: ir.EffectSummary) bool {
    return effects.precision == .exact and
        !effects.reads_memory and
        !effects.writes_memory and
        !effects.may_throw and
        !effects.may_yield and
        !effects.invokes_unknown_code;
}

test "value type assignability follows numeric refinement containment" {
    const unsigned8: ir.ValueType = .{ .kind = .integer, .bit_width = 8 };
    const unsigned16: ir.ValueType = .{ .kind = .integer, .bit_width = 16 };
    const signed8: ir.ValueType = .{ .kind = .integer, .bit_width = 8, .signed = true };
    const signed9: ir.ValueType = .{ .kind = .integer, .bit_width = 9, .signed = true };
    const signed25: ir.ValueType = .{ .kind = .integer, .bit_width = 25, .signed = true };
    const unsigned24: ir.ValueType = .{ .kind = .integer, .bit_width = 24 };
    const unsigned25: ir.ValueType = .{ .kind = .integer, .bit_width = 25 };
    const float32: ir.ValueType = .{ .kind = .number, .bit_width = 32 };
    const float64: ir.ValueType = .number;

    try std.testing.expect(isAssignable(unsigned16, unsigned8));
    try std.testing.expect(isAssignable(signed9, unsigned8));
    try std.testing.expect(!isAssignable(signed8, unsigned8));
    try std.testing.expect(!isAssignable(unsigned8, signed8));
    try std.testing.expect(isAssignable(float64, float32));
    try std.testing.expect(!isAssignable(float32, float64));
    try std.testing.expect(isAssignable(float32, unsigned24));
    try std.testing.expect(isAssignable(float32, signed25));
    try std.testing.expect(!isAssignable(float32, unsigned25));
    try std.testing.expect(isAssignable(float64, .integer));
}
