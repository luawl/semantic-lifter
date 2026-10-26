const std = @import("std");
const ir = @import("ir.zig");

pub const Source = union(enum) {
    constant: struct {
        instruction: ir.InstructionId,
        literal: ir.Literal,
    },
    copy: struct {
        instruction: ir.InstructionId,
        source: ir.ValueId,
    },
    unary: struct {
        instruction: ir.InstructionId,
        operator: ir.UnaryOperator,
        operand: ir.ValueId,
    },
    binary: struct {
        instruction: ir.InstructionId,
        operator: ir.BinaryOperator,
        left: ir.ValueId,
        right: ir.ValueId,
    },
};

pub fn source(program: *const ir.Program, value_id: ir.ValueId) ?Source {
    if (value_id.index() >= program.values.len) return null;
    const value = program.values[value_id.index()];
    if (value.id != value_id) return null;
    const result = switch (value.origin) {
        .instruction_result => |origin| origin,
        else => return null,
    };
    if (result.instruction.index() >= program.instructions.len) return null;
    const instruction = program.instructions[result.instruction.index()];
    if (instruction.id != result.instruction or
        result.index != 0 or
        instruction.results.len != 1 or
        instruction.results[0] != value_id or
        !isExactPure(instruction.effects))
    {
        return null;
    }

    return switch (instruction.operation) {
        .constant => |literal| switch (literal) {
            .boolean => |constant| if (value.type.kind == .boolean or value.type.kind == .dynamic)
                .{ .constant = .{ .instruction = instruction.id, .literal = .{ .boolean = constant } } }
            else
                null,
            .integer => |constant| if (value.type.kind == .integer or value.type.kind == .number or value.type.kind == .dynamic)
                .{ .constant = .{ .instruction = instruction.id, .literal = .{ .integer = constant } } }
            else
                null,
            .nil_value => if (value.type.kind == .nil_value or value.type.kind == .dynamic)
                .{ .constant = .{ .instruction = instruction.id, .literal = .{ .nil_value = {} } } }
            else
                null,
            .string => |constant| if (value.type.kind == .string or value.type.kind == .dynamic)
                .{ .constant = .{ .instruction = instruction.id, .literal = .{ .string = constant } } }
            else
                null,
            .number => |constant| if (std.math.isFinite(constant) and
                (value.type.kind == .number or value.type.kind == .dynamic))
                .{ .constant = .{ .instruction = instruction.id, .literal = .{ .number = constant } } }
            else
                null,
            .special_number => |constant| if (value.type.kind == .number or value.type.kind == .dynamic)
                .{ .constant = .{ .instruction = instruction.id, .literal = .{ .special_number = constant } } }
            else
                null,
        },
        .copy => |copy_source| .{ .copy = .{ .instruction = instruction.id, .source = copy_source } },
        .unary => |unary| if (canNormalizeUnary(program, value.type.kind, unary))
            .{ .unary = .{ .instruction = instruction.id, .operator = unary.operator, .operand = unary.operand } }
        else
            null,
        .binary => |binary| if (canNormalizeBinary(program.values, value.type.kind, binary))
            .{ .binary = .{ .instruction = instruction.id, .operator = binary.operator, .left = binary.left, .right = binary.right } }
        else
            null,
        else => null,
    };
}

pub fn isExactPure(effects: ir.EffectSummary) bool {
    return effects.precision == .exact and
        !effects.reads_memory and
        !effects.writes_memory and
        !effects.may_throw and
        !effects.may_yield and
        !effects.invokes_unknown_code;
}

fn canNormalizeUnary(program: *const ir.Program, result_kind: ir.TypeKind, unary: ir.Unary) bool {
    if (unary.operand.index() >= program.values.len) return false;
    const operand_kind = program.values[unary.operand.index()].type.kind;
    return switch (unary.operator) {
        .logical_not => result_kind == .boolean or result_kind == .dynamic,
        .negate => switch (result_kind) {
            .integer => operand_kind == .integer,
            .number => operand_kind == .integer or operand_kind == .number,
            .dynamic => operand_kind == .integer or operand_kind == .number or operand_kind == .dynamic,
            else => false,
        },
        .length => result_kind == .integer and operand_kind == .string,
        .bit_not => false,
    };
}

test "special constants and static number negation retain exact normalized provenance" {
    const positive = ir.ValueId.fromIndex(0);
    const negative = ir.ValueId.fromIndex(1);
    const effectful = ir.ValueId.fromIndex(2);
    const unknown = ir.ValueId.fromIndex(3);
    const values = [_]ir.Value{
        .{ .id = positive, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = negative, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = effectful, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = unknown, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .parameter = 0 } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .special_number = .positive_infinity } }, .results = &.{positive}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .negate, .operand = positive } }, .results = &.{negative}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .negate, .operand = unknown } }, .results = &.{effectful}, .effects = .dynamic_call },
    };
    const program: ir.Program = .{
        .program_id = "normalized-special-negation",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };

    try std.testing.expectEqual(ir.SpecialNumber.positive_infinity, source(&program, positive).?.constant.literal.special_number);
    try std.testing.expectEqual(positive, source(&program, negative).?.unary.operand);
    try std.testing.expectEqual(@as(?Source, null), source(&program, effectful));
}

fn canNormalizeBinary(values: []const ir.Value, result_kind: ir.TypeKind, binary: ir.Binary) bool {
    const static_numeric = binary.left.index() < values.len and
        binary.right.index() < values.len and
        isNumeric(values[binary.left.index()].type.kind) and
        isNumeric(values[binary.right.index()].type.kind);
    const static_strings = binary.left.index() < values.len and
        binary.right.index() < values.len and
        values[binary.left.index()].type.kind == .string and
        values[binary.right.index()].type.kind == .string;
    const static_booleans = binary.left.index() < values.len and
        binary.right.index() < values.len and
        values[binary.left.index()].type.kind == .boolean and
        values[binary.right.index()].type.kind == .boolean;
    return switch (binary.operator) {
        .add, .subtract, .multiply => result_kind == .integer or result_kind == .dynamic or
            (result_kind == .number and static_numeric),
        .divide, .floor_divide, .modulo, .power => result_kind == .number and static_numeric,
        .concat => result_kind == .string and static_strings,
        .equal, .not_equal, .less, .less_equal, .greater, .greater_equal => result_kind == .boolean or result_kind == .dynamic,
        .logical_and, .logical_or => (result_kind == .boolean or result_kind == .dynamic) and static_booleans,
        .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => false,
    };
}

pub fn exactStringLength(program: *const ir.Program, value_id: ir.ValueId) ?usize {
    return exactStringLengthDepth(program, value_id, 0);
}

pub const ExactStringSource = struct {
    program: *const ir.Program,
    value: ir.ValueId,
};

pub const ExactString = union(enum) {
    bytes: []const u8,
    source: ExactStringSource,
};

pub const ExactStringRelation = enum {
    equivalent,
    distinct,
    unresolved,
};

pub const ExactStringOrder = enum {
    less,
    equal,
    greater,
    unresolved,
};

pub const ExactStringLimits = struct {
    max_bytes: usize = 1024 * 1024,
    max_sources: usize = 4096,
};

pub fn exactStringOrder(left: ExactString, right: ExactString) ExactStringOrder {
    return exactStringOrderWithLimits(left, right, .{});
}

pub fn exactStringOrderWithLimits(left: ExactString, right: ExactString, limits: ExactStringLimits) ExactStringOrder {
    var left_cursor = ExactStringCursor.init(left, limits.max_sources);
    var right_cursor = ExactStringCursor.init(right, limits.max_sources);
    var left_segment = left_cursor.next();
    var right_segment = right_cursor.next();
    var left_offset: usize = 0;
    var right_offset: usize = 0;
    var compared: usize = 0;
    while (true) {
        if (left_cursor.unresolved or right_cursor.unresolved) return .unresolved;
        if (left_segment == null or right_segment == null) {
            if (left_segment == null and right_segment == null) return .equal;
            return if (left_segment == null) .less else .greater;
        }
        const count = @min(left_segment.?.len - left_offset, right_segment.?.len - right_offset);
        if (compared > limits.max_bytes or count > limits.max_bytes - compared) return .unresolved;
        switch (std.mem.order(
            u8,
            left_segment.?[left_offset .. left_offset + count],
            right_segment.?[right_offset .. right_offset + count],
        )) {
            .lt => return .less,
            .gt => return .greater,
            .eq => {},
        }
        compared += count;
        left_offset += count;
        right_offset += count;
        if (left_offset == left_segment.?.len) {
            left_segment = left_cursor.next();
            left_offset = 0;
        }
        if (right_offset == right_segment.?.len) {
            right_segment = right_cursor.next();
            right_offset = 0;
        }
    }
}

pub fn exactStringRelation(left: ExactString, right: ExactString) ExactStringRelation {
    return exactStringRelationWithLimits(left, right, .{});
}

pub fn exactStringRelationWithLimits(left: ExactString, right: ExactString, limits: ExactStringLimits) ExactStringRelation {
    switch (left) {
        .bytes => |left_bytes| switch (right) {
            .bytes => |right_bytes| return if (std.mem.eql(u8, left_bytes, right_bytes)) .equivalent else .distinct,
            .source => {},
        },
        .source => |left_source| switch (right) {
            .source => |right_source| if (left_source.program == right_source.program and left_source.value == right_source.value) return .equivalent,
            .bytes => {},
        },
    }

    var left_cursor = ExactStringCursor.init(left, limits.max_sources);
    var right_cursor = ExactStringCursor.init(right, limits.max_sources);
    var left_segment = left_cursor.next();
    var right_segment = right_cursor.next();
    var left_offset: usize = 0;
    var right_offset: usize = 0;
    var compared: usize = 0;
    while (true) {
        if (left_cursor.unresolved or right_cursor.unresolved) return .unresolved;
        if (left_segment == null or right_segment == null) {
            return if (left_segment == null and right_segment == null) .equivalent else .distinct;
        }
        const count = @min(left_segment.?.len - left_offset, right_segment.?.len - right_offset);
        if (compared > limits.max_bytes or count > limits.max_bytes - compared) return .unresolved;
        if (!std.mem.eql(
            u8,
            left_segment.?[left_offset .. left_offset + count],
            right_segment.?[right_offset .. right_offset + count],
        )) return .distinct;
        compared += count;
        left_offset += count;
        right_offset += count;
        if (left_offset == left_segment.?.len) {
            left_segment = left_cursor.next();
            left_offset = 0;
        }
        if (right_offset == right_segment.?.len) {
            right_segment = right_cursor.next();
            right_offset = 0;
        }
    }
}

const max_exact_string_pending_sources = 256;

const ExactStringCursor = struct {
    direct: ?[]const u8 = null,
    direct_pending: bool = false,
    pending: [max_exact_string_pending_sources]ExactStringSource = undefined,
    pending_len: usize = 0,
    remaining_sources: usize,
    unresolved: bool = false,

    fn init(value: ExactString, max_sources: usize) ExactStringCursor {
        var cursor: ExactStringCursor = .{ .remaining_sources = max_sources };
        switch (value) {
            .bytes => |bytes| {
                cursor.direct = bytes;
                cursor.direct_pending = true;
            },
            .source => |source_value| cursor.push(source_value),
        }
        return cursor;
    }

    fn next(self: *ExactStringCursor) ?[]const u8 {
        if (self.direct_pending) {
            self.direct_pending = false;
            if (self.direct.?.len != 0) return self.direct.?;
        }
        while (self.pending_len != 0) {
            if (self.remaining_sources == 0) {
                self.unresolved = true;
                return null;
            }
            self.remaining_sources -= 1;
            self.pending_len -= 1;
            const current = self.pending[self.pending_len];
            const normalized = source(current.program, current.value) orelse {
                self.unresolved = true;
                return null;
            };
            switch (normalized) {
                .constant => |constant| switch (constant.literal) {
                    .string => |bytes| if (bytes.len != 0) return bytes,
                    else => {
                        self.unresolved = true;
                        return null;
                    },
                },
                .copy => |copy| self.push(.{ .program = current.program, .value = copy.source }),
                .binary => |binary| {
                    if (binary.operator != .concat) {
                        self.unresolved = true;
                        return null;
                    }
                    self.push(.{ .program = current.program, .value = binary.right });
                    self.push(.{ .program = current.program, .value = binary.left });
                },
                .unary => {
                    self.unresolved = true;
                    return null;
                },
            }
            if (self.unresolved) return null;
        }
        return null;
    }

    fn push(self: *ExactStringCursor, value: ExactStringSource) void {
        if (self.pending_len == self.pending.len) {
            self.unresolved = true;
            return;
        }
        self.pending[self.pending_len] = value;
        self.pending_len += 1;
    }
};

fn exactStringLengthDepth(program: *const ir.Program, value_id: ir.ValueId, depth: usize) ?usize {
    if (depth > program.values.len + program.instructions.len) return null;
    const normalized = source(program, value_id) orelse return null;
    return switch (normalized) {
        .constant => |constant| switch (constant.literal) {
            .string => |value| value.len,
            else => null,
        },
        .copy => |copy| exactStringLengthDepth(program, copy.source, depth + 1),
        .binary => |binary| if (binary.operator == .concat)
            std.math.add(
                usize,
                exactStringLengthDepth(program, binary.left, depth + 1) orelse return null,
                exactStringLengthDepth(program, binary.right, depth + 1) orelse return null,
            ) catch null
        else
            null,
        .unary => null,
    };
}

pub fn solverBinaryOperator(operator: ir.BinaryOperator) ?ir.SolverBinaryOperator {
    return switch (operator) {
        .add => .add,
        .subtract => .subtract,
        .multiply => .multiply,
        .equal => .equal,
        .not_equal => .not_equal,
        .less => .less,
        .less_equal => .less_equal,
        .greater => .greater,
        .greater_equal => .greater_equal,
        .logical_and => .logical_and,
        .logical_or => .logical_or,
        .bit_and => .bit_and,
        .bit_or => .bit_or,
        .bit_xor => .bit_xor,
        .shift_left => .shift_left,
        .shift_right => .shift_right,
        .divide, .floor_divide, .modulo, .power, .concat => null,
    };
}

fn isNumeric(kind: ir.TypeKind) bool {
    return kind == .integer or kind == .number;
}

test "static runtime arithmetic normalizes without borrowing solver vocabulary" {
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const sum = ir.ValueId.fromIndex(2);
    const quotient = ir.ValueId.fromIndex(3);
    const effectful = ir.ValueId.fromIndex(4);
    const unknown = ir.ValueId.fromIndex(5);
    const dynamic_quotient = ir.ValueId.fromIndex(6);
    const floor_quotient = ir.ValueId.fromIndex(7);
    const effectful_floor_quotient = ir.ValueId.fromIndex(8);
    const dynamic_floor_quotient = ir.ValueId.fromIndex(9);
    const values = [_]ir.Value{
        .{ .id = left, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = right, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = sum, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = quotient, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = effectful, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = unknown, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = dynamic_quotient, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
        .{ .id = floor_quotient, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(6), .index = 0 } } },
        .{ .id = effectful_floor_quotient, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(7), .index = 0 } } },
        .{ .id = dynamic_floor_quotient, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(8), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 1.5 } }, .results = &.{left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 2.25 } }, .results = &.{right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .add, .left = left, .right = right } }, .results = &.{sum}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .divide, .left = left, .right = right } }, .results = &.{quotient}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .divide, .left = left, .right = right } }, .results = &.{effectful}, .effects = .dynamic_call },
        .{ .id = ir.InstructionId.fromIndex(5), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .divide, .left = unknown, .right = right } }, .results = &.{dynamic_quotient}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(6), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .floor_divide, .left = left, .right = right } }, .results = &.{floor_quotient}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(7), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .floor_divide, .left = left, .right = right } }, .results = &.{effectful_floor_quotient}, .effects = .dynamic_call },
        .{ .id = ir.InstructionId.fromIndex(8), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .floor_divide, .left = unknown, .right = right } }, .results = &.{dynamic_floor_quotient}, .effects = .pure },
    };
    const program: ir.Program = .{
        .program_id = "normalized-static-number-arithmetic",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };

    const normalized_sum = source(&program, sum).?.binary;
    try std.testing.expectEqual(ir.BinaryOperator.add, normalized_sum.operator);
    try std.testing.expectEqual(left, normalized_sum.left);
    try std.testing.expectEqual(right, normalized_sum.right);
    try std.testing.expectEqual(ir.BinaryOperator.divide, source(&program, quotient).?.binary.operator);
    try std.testing.expectEqual(ir.BinaryOperator.floor_divide, source(&program, floor_quotient).?.binary.operator);
    try std.testing.expectEqual(@as(?ir.SolverBinaryOperator, null), solverBinaryOperator(.divide));
    try std.testing.expectEqual(@as(?ir.SolverBinaryOperator, null), solverBinaryOperator(.floor_divide));
    try std.testing.expectEqual(@as(?Source, null), source(&program, effectful));
    try std.testing.expectEqual(@as(?Source, null), source(&program, dynamic_quotient));
    try std.testing.expectEqual(@as(?Source, null), source(&program, effectful_floor_quotient));
    try std.testing.expectEqual(@as(?Source, null), source(&program, dynamic_floor_quotient));
    try std.testing.expect(!canNormalizeBinary(&values, .integer, .{
        .operator = .floor_divide,
        .left = left,
        .right = right,
    }));

    var modulo_instructions = instructions;
    modulo_instructions[6].operation.binary.operator = .modulo;
    modulo_instructions[7].operation.binary.operator = .modulo;
    modulo_instructions[8].operation.binary.operator = .modulo;
    var modulo_program = program;
    modulo_program.instructions = &modulo_instructions;
    try std.testing.expectEqual(ir.BinaryOperator.modulo, source(&modulo_program, floor_quotient).?.binary.operator);
    try std.testing.expectEqual(@as(?ir.SolverBinaryOperator, null), solverBinaryOperator(.modulo));
    try std.testing.expectEqual(@as(?Source, null), source(&modulo_program, effectful_floor_quotient));
    try std.testing.expectEqual(@as(?Source, null), source(&modulo_program, dynamic_floor_quotient));
    try std.testing.expect(!canNormalizeBinary(&values, .integer, .{
        .operator = .modulo,
        .left = left,
        .right = right,
    }));

    var power_instructions = instructions;
    power_instructions[6].operation.binary.operator = .power;
    power_instructions[7].operation.binary.operator = .power;
    power_instructions[8].operation.binary.operator = .power;
    var power_program = program;
    power_program.instructions = &power_instructions;
    try std.testing.expectEqual(ir.BinaryOperator.power, source(&power_program, floor_quotient).?.binary.operator);
    try std.testing.expectEqual(@as(?ir.SolverBinaryOperator, null), solverBinaryOperator(.power));
    try std.testing.expectEqual(@as(?Source, null), source(&power_program, effectful_floor_quotient));
    try std.testing.expectEqual(@as(?Source, null), source(&power_program, dynamic_floor_quotient));
    try std.testing.expect(!canNormalizeBinary(&values, .integer, .{
        .operator = .power,
        .left = left,
        .right = right,
    }));
}

test "exact string length follows pure string concatenation only" {
    const left = ir.ValueId.fromIndex(0);
    const copied_left = ir.ValueId.fromIndex(1);
    const right = ir.ValueId.fromIndex(2);
    const concatenated = ir.ValueId.fromIndex(3);
    const length = ir.ValueId.fromIndex(4);
    const effectful = ir.ValueId.fromIndex(5);
    const unknown = ir.ValueId.fromIndex(6);
    const dynamic_concat = ir.ValueId.fromIndex(7);
    const integer = ir.ValueId.fromIndex(8);
    const coerced_concat = ir.ValueId.fromIndex(9);
    const values = [_]ir.Value{
        .{ .id = left, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = copied_left, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = right, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = concatenated, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = length, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = effectful, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
        .{ .id = unknown, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = dynamic_concat, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(6), .index = 0 } } },
        .{ .id = integer, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(7), .index = 0 } } },
        .{ .id = coerced_concat, .function = ir.FunctionId.fromIndex(0), .type = .string, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(8), .index = 0 } } },
    };
    var instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "\xc3\xa9" } }, .results = &.{left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .copy = left }, .results = &.{copied_left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .string = "c\x00" } }, .results = &.{right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .concat, .left = copied_left, .right = right } }, .results = &.{concatenated}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .length, .operand = concatenated } }, .results = &.{length}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(5), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .concat, .left = left, .right = right } }, .results = &.{effectful}, .effects = .dynamic_call },
        .{ .id = ir.InstructionId.fromIndex(6), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .concat, .left = unknown, .right = right } }, .results = &.{dynamic_concat}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(7), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "7" } }, .results = &.{integer}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(8), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .concat, .left = left, .right = integer } }, .results = &.{coerced_concat}, .effects = .pure },
    };
    const program: ir.Program = .{
        .program_id = "normalized-exact-string-length",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };

    try std.testing.expectEqual(ir.BinaryOperator.concat, source(&program, concatenated).?.binary.operator);
    try std.testing.expectEqual(ir.UnaryOperator.length, source(&program, length).?.unary.operator);
    try std.testing.expectEqual(@as(?usize, 4), exactStringLength(&program, concatenated));
    try std.testing.expectEqual(@as(?Source, null), source(&program, effectful));
    try std.testing.expectEqual(@as(?Source, null), source(&program, dynamic_concat));
    try std.testing.expectEqual(@as(?Source, null), source(&program, coerced_concat));
    const exact_source: ExactString = .{ .source = .{ .program = &program, .value = concatenated } };
    try std.testing.expectEqual(ExactStringRelation.equivalent, exactStringRelation(exact_source, .{ .bytes = "\xc3\xa9c\x00" }));
    try std.testing.expectEqual(ExactStringRelation.distinct, exactStringRelation(exact_source, .{ .bytes = "\xc3\xa9c!" }));
    try std.testing.expectEqual(ExactStringRelation.unresolved, exactStringRelationWithLimits(
        exact_source,
        .{ .bytes = "\xc3\xa9c\x00" },
        .{ .max_bytes = 3 },
    ));
    try std.testing.expectEqual(ExactStringOrder.equal, exactStringOrder(exact_source, .{ .bytes = "\xc3\xa9c\x00" }));
    try std.testing.expectEqual(ExactStringOrder.less, exactStringOrder(exact_source, .{ .bytes = "\xc3\xa9c!" }));
    try std.testing.expectEqual(ExactStringOrder.greater, exactStringOrder(exact_source, .{ .bytes = "z" }));
    try std.testing.expectEqual(ExactStringOrder.less, exactStringOrder(.{ .bytes = "ab" }, .{ .bytes = "aba" }));
    try std.testing.expectEqual(ExactStringOrder.less, exactStringOrder(.{ .bytes = "a\x00" }, .{ .bytes = "a\x01" }));
    try std.testing.expectEqual(ExactStringOrder.unresolved, exactStringOrderWithLimits(
        exact_source,
        .{ .bytes = "\xc3\xa9c\x00" },
        .{ .max_bytes = 3 },
    ));

    instructions[1].operation = .{ .copy = copied_left };
    try std.testing.expectEqual(@as(?usize, null), exactStringLength(&program, concatenated));
    try std.testing.expectEqual(ExactStringRelation.unresolved, exactStringRelation(exact_source, .{ .bytes = "\xc3\xa9c\x00" }));
    try std.testing.expectEqual(ExactStringOrder.unresolved, exactStringOrder(exact_source, .{ .bytes = "\xc3\xa9c\x00" }));
}
