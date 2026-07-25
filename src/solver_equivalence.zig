const std = @import("std");
const ir = @import("ir.zig");
const numerals = @import("numerals.zig");
const normalized_value = @import("normalized_value.zig");
const solver_term = @import("solver_term.zig");

pub fn termsEquivalent(program: *const ir.Program, left: ir.SolverTermId, right: ir.SolverTermId) bool {
    return termsEquivalentDepth(program, left, right, 0);
}

pub fn termsDistinct(program: *const ir.Program, left: ir.SolverTermId, right: ir.SolverTermId) bool {
    return termsDistinctDepth(program, left, right, 0);
}

pub fn termRepresentsValue(program: *const ir.Program, term: ir.SolverTermId, value: ir.ValueId) bool {
    return termMatchesValue(program, term, value, 0);
}

pub const DynamicCategory = enum {
    nil_value,
    boolean,
    number,
    string,
    table,
    function_value,
    thread,
    userdata,
    tuple,
};

pub const DynamicNumber = union(enum) {
    integer: []const u8,
    number: f64,
};

pub const DynamicDescriptor = struct {
    category: DynamicCategory,
    exact_boolean: ?bool = null,
    exact_number: ?DynamicNumber = null,
    number_excludes_nan: bool = false,
    exact_string: ?[]const u8 = null,
    exact_string_source: ?normalized_value.ExactStringSource = null,
    allocation_site: ?ir.InstructionId = null,
    function_reference: ?ir.FunctionId = null,
};

pub const DynamicRelation = enum {
    equivalent,
    distinct,
    unresolved,
};

pub const PrimitiveBooleanOperation = union(enum) {
    unary: ir.Unary,
    binary: ir.Binary,
};

pub fn dynamicValueDescriptor(program: *const ir.Program, value: ir.ValueId) ?DynamicDescriptor {
    return dynamicDescriptorDepth(program, value, 0);
}

pub fn exactFiniteNumberResult(program: *const ir.Program, value: ir.ValueId) ?f64 {
    if (value.index() >= program.values.len or program.values[value.index()].type.kind != .number) return null;
    const descriptor = dynamicValueDescriptor(program, value) orelse return null;
    if (descriptor.category != .number) return null;
    const result = dynamicNumberAsF64(descriptor.exact_number orelse return null) orelse return null;
    return if (std.math.isFinite(result)) result else null;
}

pub fn dynamicTermDescriptor(program: *const ir.Program, term: ir.SolverTermId) ?DynamicDescriptor {
    return dynamicTermDescriptorDepth(program, term, 0);
}

pub fn dynamicDescriptorTruthiness(descriptor: DynamicDescriptor) ?bool {
    return switch (descriptor.category) {
        .nil_value => false,
        .boolean => descriptor.exact_boolean,
        .number, .string, .table, .function_value, .thread, .userdata, .tuple => true,
    };
}

pub fn dynamicTermTruthiness(program: *const ir.Program, term: ir.SolverTermId) ?bool {
    const descriptor = dynamicTermDescriptor(program, term) orelse return null;
    return dynamicDescriptorTruthiness(descriptor);
}

pub fn dynamicDescriptorIsNaN(descriptor: DynamicDescriptor) ?bool {
    if (descriptor.category != .number) return false;
    const number = descriptor.exact_number orelse return if (descriptor.number_excludes_nan) false else null;
    return switch (number) {
        .integer => false,
        .number => |value| std.math.isNan(value),
    };
}

pub fn dynamicTermIsNaN(program: *const ir.Program, term: ir.SolverTermId) ?bool {
    const descriptor = dynamicTermDescriptor(program, term) orelse return null;
    return dynamicDescriptorIsNaN(descriptor);
}

pub fn dynamicDescriptorExactString(descriptor: DynamicDescriptor) ?normalized_value.ExactString {
    if (descriptor.category != .string or
        (descriptor.exact_string != null and descriptor.exact_string_source != null)) return null;
    if (descriptor.exact_string) |bytes| return .{ .bytes = bytes };
    if (descriptor.exact_string_source) |source_value| return .{ .source = source_value };
    return null;
}

pub fn dynamicDescriptorRelation(left: DynamicDescriptor, right: DynamicDescriptor) DynamicRelation {
    if (left.category != right.category) return .distinct;
    return switch (left.category) {
        .nil_value => .equivalent,
        .boolean => blk: {
            const left_boolean = left.exact_boolean orelse break :blk .unresolved;
            const right_boolean = right.exact_boolean orelse break :blk .unresolved;
            break :blk if (left_boolean == right_boolean) .equivalent else .distinct;
        },
        .number => blk: {
            const left_number = left.exact_number orelse break :blk .unresolved;
            const right_number = right.exact_number orelse break :blk .unresolved;
            break :blk exactNumberRelation(left_number, right_number);
        },
        .string => blk: {
            const left_string = dynamicDescriptorExactString(left) orelse break :blk .unresolved;
            const right_string = dynamicDescriptorExactString(right) orelse break :blk .unresolved;
            break :blk switch (normalized_value.exactStringRelation(left_string, right_string)) {
                .equivalent => .equivalent,
                .distinct => .distinct,
                .unresolved => .unresolved,
            };
        },
        .table, .thread => freshAllocationRelation(left, right),
        .function_value => functionReferenceRelation(left, right),
        .userdata, .tuple => .unresolved,
    };
}

pub fn dynamicValuesHavePrimitiveEquality(program: *const ir.Program, left: ir.ValueId, right: ir.ValueId) bool {
    const left_descriptor = dynamicValueDescriptor(program, left) orelse return false;
    const right_descriptor = dynamicValueDescriptor(program, right) orelse return false;
    return dynamicDescriptorsHavePrimitiveEquality(left_descriptor, right_descriptor);
}

pub fn dynamicValuesHaveUnguardedPrimitiveEquality(program: *const ir.Program, left: ir.ValueId, right: ir.ValueId) bool {
    const left_descriptor = dynamicValueDescriptor(program, left) orelse return false;
    const right_descriptor = dynamicValueDescriptor(program, right) orelse return false;
    if (!dynamicDescriptorsHavePrimitiveEquality(left_descriptor, right_descriptor)) return false;
    if (left_descriptor.category != .number or right_descriptor.category != .number) return true;
    return dynamicNumberValueExcludesNaN(program, left, 0) and dynamicNumberValueExcludesNaN(program, right, 0);
}

pub fn dynamicDescriptorsHavePrimitiveEquality(left: DynamicDescriptor, right: DynamicDescriptor) bool {
    return dynamicCategoryHasPrimitiveEquality(left.category) and dynamicCategoryHasPrimitiveEquality(right.category);
}

fn dynamicCategoryHasPrimitiveEquality(category: DynamicCategory) bool {
    return switch (category) {
        .nil_value, .boolean, .number, .string, .function_value, .thread => true,
        .table, .userdata, .tuple => false,
    };
}

fn dynamicNumberValueExcludesNaN(program: *const ir.Program, value_id: ir.ValueId, depth: usize) bool {
    if (value_id.index() >= program.values.len or depth > limit(program)) return false;
    if (program.values[value_id.index()].type.kind == .integer) return true;
    const source = normalized_value.source(program, value_id) orelse return false;
    return switch (source) {
        .constant => |constant| switch (constant.literal) {
            .integer => true,
            .number => |value| !std.math.isNan(value),
            .special_number => |value| value != .nan,
            .nil_value, .boolean, .string => false,
        },
        .copy => |copy| dynamicNumberValueExcludesNaN(program, copy.source, depth + 1),
        .unary => |unary| unary.operator == .negate and dynamicNumberValueExcludesNaN(program, unary.operand, depth + 1),
        .binary => |binary| if (exactPrimitiveBinaryNumber(
            binary.operator,
            dynamicDescriptorDepth(program, binary.left, depth + 1),
            dynamicDescriptorDepth(program, binary.right, depth + 1),
        )) |number| !dynamicNumberIsNaN(number) else false,
    };
}

pub fn dynamicDescriptorsEquivalent(left: DynamicDescriptor, right: DynamicDescriptor) bool {
    return dynamicDescriptorRelation(left, right) == .equivalent;
}

pub fn dynamicDescriptorsDistinct(left: DynamicDescriptor, right: DynamicDescriptor) bool {
    return dynamicDescriptorRelation(left, right) == .distinct;
}

fn exactNumberRelation(left: DynamicNumber, right: DynamicNumber) DynamicRelation {
    return switch (left) {
        .integer => |left_integer| switch (right) {
            .integer => |right_integer| integerIntegerRelation(left_integer, right_integer),
            .number => |right_number| integerNumberRelation(left_integer, right_number),
        },
        .number => |left_number| switch (right) {
            .integer => |right_integer| integerNumberRelation(right_integer, left_number),
            .number => |right_number| if (std.math.isNan(left_number) or std.math.isNan(right_number))
                .unresolved
            else if (left_number == right_number)
                .equivalent
            else
                .distinct,
        },
    };
}

fn freshAllocationRelation(left: DynamicDescriptor, right: DynamicDescriptor) DynamicRelation {
    const left_site = left.allocation_site orelse return .unresolved;
    const right_site = right.allocation_site orelse return .unresolved;
    return if (left_site == right_site) .equivalent else .distinct;
}

fn functionReferenceRelation(left: DynamicDescriptor, right: DynamicDescriptor) DynamicRelation {
    const left_target = left.function_reference orelse return .unresolved;
    const right_target = right.function_reference orelse return .unresolved;
    return if (left_target == right_target) .equivalent else .distinct;
}

fn integerIntegerRelation(left: []const u8, right: []const u8) DynamicRelation {
    if (!numerals.isCanonicalSignedDecimal(left) or !numerals.isCanonicalSignedDecimal(right)) return .unresolved;
    if (std.mem.eql(u8, left, right)) return .equivalent;
    const left_value = exactLuauInteger(left) orelse return .unresolved;
    const right_value = exactLuauInteger(right) orelse return .unresolved;
    return if (left_value == right_value) .equivalent else .distinct;
}

fn integerNumberRelation(integer: []const u8, number: f64) DynamicRelation {
    if (!numerals.isCanonicalSignedDecimal(integer) or std.math.isNan(number)) return .unresolved;
    if (!std.math.isFinite(number)) return .distinct;
    const parsed = exactLuauInteger(integer) orelse return .unresolved;
    const float_limit: f64 = @floatFromInt(@as(i64, 1 << 53));
    if (number < -float_limit or number > float_limit) return .unresolved;
    if (@trunc(number) != number) return .distinct;
    return if (@as(f64, @floatFromInt(parsed)) == number) .equivalent else .distinct;
}

pub fn negateExactNumber(number: DynamicNumber) ?DynamicNumber {
    return switch (number) {
        .integer => |integer| blk: {
            const value = exactLuauInteger(integer) orelse break :blk null;
            const as_number: f64 = @floatFromInt(value);
            break :blk .{ .number = -as_number };
        },
        .number => |value| .{ .number = -value },
    };
}

pub fn exactPrimitiveBinaryNumber(
    operator: ir.BinaryOperator,
    left_descriptor: ?DynamicDescriptor,
    right_descriptor: ?DynamicDescriptor,
) ?DynamicNumber {
    const left = left_descriptor orelse return null;
    const right = right_descriptor orelse return null;
    if (left.category != .number or right.category != .number) return null;
    const left_value = dynamicNumberAsF64(left.exact_number orelse return null) orelse return null;
    const right_value = dynamicNumberAsF64(right.exact_number orelse return null) orelse return null;
    return .{ .number = switch (operator) {
        .add => left_value + right_value,
        .subtract => left_value - right_value,
        .multiply => left_value * right_value,
        .divide => left_value / right_value,
        .floor_divide => @floor(left_value / right_value),
        .modulo => left_value - @floor(left_value / right_value) * right_value,
        .power => exactPrimitivePower(left_value, right_value) orelse return null,
        else => return null,
    } };
}

fn exactPrimitivePower(base: f64, exponent: f64) ?f64 {
    if (exponent == 0.0 or base == 1.0) return 1.0;
    if (std.math.isNan(base) or std.math.isNan(exponent)) return std.math.nan(f64);
    if (exponent == 1.0) return base;

    const exponent_is_odd = exactPowerIntegerIsOdd(exponent);
    if (base == 0.0) {
        if (exponent < 0.0) {
            return if (exponent_is_odd == true and std.math.signbit(base))
                -std.math.inf(f64)
            else
                std.math.inf(f64);
        }
        return if (exponent_is_odd == true) base else 0.0;
    }

    if (std.math.isInf(exponent)) {
        if (base == -1.0) return 1.0;
        return if ((@abs(base) < 1.0) == (exponent > 0.0)) 0.0 else std.math.inf(f64);
    }

    if (std.math.isInf(base)) {
        if (base < 0.0 and exponent_is_odd == true) {
            return if (exponent < 0.0) -0.0 else -std.math.inf(f64);
        }
        return if (exponent < 0.0) 0.0 else std.math.inf(f64);
    }

    if (base == -1.0) {
        const is_odd = exponent_is_odd orelse return std.math.nan(f64);
        return if (is_odd) -1.0 else 1.0;
    }
    if (base < 0.0 and exponent_is_odd == null) return std.math.nan(f64);
    return exactBoundedIntegerPower(base, exponent);
}

fn exactPowerIntegerIsOdd(value: f64) ?bool {
    if (!std.math.isFinite(value) or @trunc(value) != value) return null;
    const exact_integer_limit: f64 = @floatFromInt(@as(i64, 1 << 53));
    if (@abs(value) >= exact_integer_limit) return false;
    return @as(i64, @intFromFloat(value)) & 1 != 0;
}

fn exactBoundedIntegerPower(base: f64, exponent: f64) ?f64 {
    const exact_integer_limit: i128 = 1 << 53;
    if (!std.math.isFinite(base) or @trunc(base) != base or
        base < -@as(f64, @floatFromInt(exact_integer_limit)) or
        base > @as(f64, @floatFromInt(exact_integer_limit)) or
        !std.math.isFinite(exponent) or @trunc(exponent) != exponent or
        exponent < 0.0 or exponent > 64.0)
    {
        return null;
    }

    const base_integer: i64 = @intFromFloat(base);
    const exponent_integer: u32 = @intFromFloat(exponent);
    var result: i128 = 1;
    var index: u32 = 0;
    while (index < exponent_integer) : (index += 1) {
        result *= base_integer;
        if (result < -exact_integer_limit or result > exact_integer_limit) return null;
    }
    return @floatFromInt(result);
}

pub fn exactPrimitiveNumberComparison(
    operator: ir.BinaryOperator,
    left_descriptor: ?DynamicDescriptor,
    right_descriptor: ?DynamicDescriptor,
) ?bool {
    const left = left_descriptor orelse return null;
    const right = right_descriptor orelse return null;
    if (left.category != .number or right.category != .number) return null;
    const left_value = dynamicNumberAsF64(left.exact_number orelse return null) orelse return null;
    const right_value = dynamicNumberAsF64(right.exact_number orelse return null) orelse return null;
    return switch (operator) {
        .less => left_value < right_value,
        .less_equal => left_value <= right_value,
        .greater => left_value > right_value,
        .greater_equal => left_value >= right_value,
        else => null,
    };
}

pub fn exactPrimitiveStringComparison(
    operator: ir.BinaryOperator,
    left_descriptor: ?DynamicDescriptor,
    right_descriptor: ?DynamicDescriptor,
) ?bool {
    const left = dynamicDescriptorExactString(left_descriptor orelse return null) orelse return null;
    const right = dynamicDescriptorExactString(right_descriptor orelse return null) orelse return null;
    const order = normalized_value.exactStringOrder(left, right);
    if (order == .unresolved) return null;
    return switch (operator) {
        .less => order == .less,
        .less_equal => order == .less or order == .equal,
        .greater => order == .greater,
        .greater_equal => order == .greater or order == .equal,
        else => null,
    };
}

pub fn exactPrimitiveRelationalComparison(
    program: *const ir.Program,
    operator: ir.BinaryOperator,
    left: ir.ValueId,
    right: ir.ValueId,
) ?bool {
    if (left.index() >= program.values.len or right.index() >= program.values.len) return null;
    const left_kind = program.values[left.index()].type.kind;
    const right_kind = program.values[right.index()].type.kind;
    if (left_kind == .string and right_kind == .string) {
        return exactPrimitiveStringComparison(
            operator,
            dynamicDescriptorDepth(program, left, 1),
            dynamicDescriptorDepth(program, right, 1),
        );
    }
    return exactPrimitiveNumericComparison(program, operator, left, right);
}

pub fn exactPrimitiveNumericComparison(
    program: *const ir.Program,
    operator: ir.BinaryOperator,
    left: ir.ValueId,
    right: ir.ValueId,
) ?bool {
    if (left.index() >= program.values.len or right.index() >= program.values.len) return null;
    const left_kind = program.values[left.index()].type.kind;
    const right_kind = program.values[right.index()].type.kind;
    if (!runtimeNumericKind(left_kind) or !runtimeNumericKind(right_kind) or
        (left_kind == .integer and right_kind == .integer)) return null;
    return exactPrimitiveNumberComparison(
        operator,
        dynamicDescriptorDepth(program, left, 1),
        dynamicDescriptorDepth(program, right, 1),
    );
}

pub fn exactPrimitiveLogicalNot(descriptor: ?DynamicDescriptor) ?bool {
    return !(dynamicDescriptorTruthiness(descriptor orelse return null) orelse return null);
}

pub fn exactPrimitiveBooleanLogic(
    operator: ir.BinaryOperator,
    left_descriptor: ?DynamicDescriptor,
    right_descriptor: ?DynamicDescriptor,
) ?bool {
    const left = left_descriptor orelse return null;
    const right = right_descriptor orelse return null;
    if (left.category != .boolean or right.category != .boolean) return null;
    return switch (operator) {
        .logical_and => blk: {
            if (left.exact_boolean) |value| if (!value) break :blk false;
            if (right.exact_boolean) |value| if (!value) break :blk false;
            if (left.exact_boolean != null and right.exact_boolean != null) break :blk true;
            break :blk null;
        },
        .logical_or => blk: {
            if (left.exact_boolean) |value| if (value) break :blk true;
            if (right.exact_boolean) |value| if (value) break :blk true;
            if (left.exact_boolean != null and right.exact_boolean != null) break :blk false;
            break :blk null;
        },
        else => null,
    };
}

pub fn exactPrimitiveBit32Result(program: *const ir.Program, value: ir.ValueId) ?u32 {
    return exactPrimitiveBit32ResultDepth(program, value, 0);
}

pub fn exactPrimitiveEqualityResult(
    program: *const ir.Program,
    operator: ir.BinaryOperator,
    left: ir.ValueId,
    right: ir.ValueId,
) ?bool {
    if ((operator != .equal and operator != .not_equal) or
        left.index() >= program.values.len or right.index() >= program.values.len) return null;
    const left_descriptor = dynamicDescriptorDepth(program, left, 1) orelse return null;
    const right_descriptor = dynamicDescriptorDepth(program, right, 1) orelse return null;
    if (!dynamicDescriptorsHavePrimitiveEquality(left_descriptor, right_descriptor)) return null;

    const equal: bool = blk: {
        if (left_descriptor.category != right_descriptor.category) break :blk false;
        if (left_descriptor.category == .number) {
            if ((dynamicDescriptorIsNaN(left_descriptor) orelse false) or
                (dynamicDescriptorIsNaN(right_descriptor) orelse false)) break :blk false;
        }
        switch (dynamicDescriptorRelation(left_descriptor, right_descriptor)) {
            .equivalent => break :blk true,
            .distinct => break :blk false,
            .unresolved => {},
        }
        if (valuesEquivalent(program, left, right, true, 1) and
            (left_descriptor.category != .number or
                (dynamicDescriptorIsNaN(left_descriptor) == false and
                    dynamicDescriptorIsNaN(right_descriptor) == false))) break :blk true;
        return null;
    };
    return if (operator == .equal) equal else !equal;
}

pub fn exactPrimitiveBooleanResult(program: *const ir.Program, operation: PrimitiveBooleanOperation) ?bool {
    return switch (operation) {
        .unary => |unary| blk: {
            if (unary.operator != .logical_not or unary.operand.index() >= program.values.len or
                program.values[unary.operand.index()].type.kind == .dynamic) break :blk null;
            break :blk exactPrimitiveLogicalNot(dynamicDescriptorDepth(program, unary.operand, 1));
        },
        .binary => |binary| switch (binary.operator) {
            .equal, .not_equal => exactPrimitiveEqualityResult(
                program,
                binary.operator,
                binary.left,
                binary.right,
            ),
            .less, .less_equal, .greater, .greater_equal => exactPrimitiveRelationalComparison(
                program,
                binary.operator,
                binary.left,
                binary.right,
            ),
            .logical_and, .logical_or => blk: {
                if (binary.left.index() >= program.values.len or binary.right.index() >= program.values.len or
                    program.values[binary.left.index()].type.kind != .boolean or
                    program.values[binary.right.index()].type.kind != .boolean) break :blk null;
                break :blk exactPrimitiveBooleanLogic(
                    binary.operator,
                    dynamicDescriptorDepth(program, binary.left, 1),
                    dynamicDescriptorDepth(program, binary.right, 1),
                );
            },
            else => null,
        },
    };
}

fn dynamicNumberAsF64(number: DynamicNumber) ?f64 {
    return switch (number) {
        .integer => |integer| @floatFromInt(exactLuauInteger(integer) orelse return null),
        .number => |value| value,
    };
}

fn runtimeNumericKind(kind: ir.TypeKind) bool {
    return kind == .integer or kind == .number or kind == .dynamic;
}

fn dynamicNumberIsNaN(number: DynamicNumber) bool {
    return switch (number) {
        .integer => false,
        .number => |value| std.math.isNan(value),
    };
}

fn exactLuauInteger(integer: []const u8) ?i64 {
    const value = numerals.parseCanonicalSigned(i64, integer) orelse return null;
    const exact_luau_limit: i64 = 1 << 53;
    if (value < -exact_luau_limit or value > exact_luau_limit) return null;
    return value;
}

fn termsEquivalentDepth(program: *const ir.Program, left_id: ir.SolverTermId, right_id: ir.SolverTermId, depth: usize) bool {
    if (left_id.index() >= program.solver_terms.len or right_id.index() >= program.solver_terms.len or depth > limit(program)) return false;
    if (left_id == right_id) return true;
    const left = program.solver_terms[left_id.index()];
    const right = program.solver_terms[right_id.index()];
    if (!sameSort(left.sort, right.sort)) return false;

    if (left.operation == .value_definition) {
        return termsEquivalentDepth(program, left.operation.value_definition.expression, right_id, depth + 1);
    }
    if (right.operation == .value_definition) {
        return termsEquivalentDepth(program, left_id, right.operation.value_definition.expression, depth + 1);
    }
    if (left.operation == .value) return termMatchesValue(program, right_id, left.operation.value, depth + 1);
    if (right.operation == .value) return termMatchesValue(program, left_id, right.operation.value, depth + 1);
    if (!solver_term.sameOperationHead(left.operation, right.operation)) return false;
    var left_dependencies = solver_term.dependencies(left.operation);
    var right_dependencies = solver_term.dependencies(right.operation);
    while (left_dependencies.next()) |left_dependency| {
        const right_dependency = right_dependencies.next() orelse return false;
        if (!termsEquivalentDepth(program, left_dependency, right_dependency, depth + 1)) return false;
    }
    return right_dependencies.next() == null;
}

fn termsDistinctDepth(program: *const ir.Program, left_id: ir.SolverTermId, right_id: ir.SolverTermId, depth: usize) bool {
    if (left_id.index() >= program.solver_terms.len or right_id.index() >= program.solver_terms.len or depth > limit(program)) return false;
    if (left_id == right_id) return false;
    const left = program.solver_terms[left_id.index()];
    const right = program.solver_terms[right_id.index()];
    if (!sameSort(left.sort, right.sort)) return false;
    if (left.sort.kind != .dynamic_value) return false;
    if (left.operation == .value_definition) {
        return termsDistinctDepth(program, left.operation.value_definition.expression, right_id, depth + 1);
    }
    if (right.operation == .value_definition) {
        return termsDistinctDepth(program, left_id, right.operation.value_definition.expression, depth + 1);
    }
    if (left.operation != .value or right.operation != .value) return false;
    return valuesDistinct(program, left.operation.value, right.operation.value, depth + 1);
}

fn termMatchesValue(program: *const ir.Program, term_id: ir.SolverTermId, value_id: ir.ValueId, depth: usize) bool {
    if (term_id.index() >= program.solver_terms.len or value_id.index() >= program.values.len or depth > limit(program)) return false;
    const term = program.solver_terms[term_id.index()];
    if (!sortAcceptsValue(term.sort, program.values[value_id.index()].type)) return false;
    if (term.operation == .value) {
        const candidate = term.operation.value;
        return candidate == value_id or valuesEquivalent(program, candidate, value_id, term.sort.kind == .dynamic_value, depth + 1);
    }
    if (term.operation == .value_definition) {
        const definition = term.operation.value_definition;
        return definition.value == value_id or
            termMatchesValue(program, definition.expression, value_id, depth + 1);
    }
    if (exactBit32LiteralMatchesValue(program, term, value_id)) return true;

    const source = normalized_value.source(program, value_id) orelse return false;
    return switch (source) {
        .constant => |constant| literalMatchesTerm(term, constant.literal),
        .copy => |copy| termMatchesValue(program, term_id, copy.source, depth + 1),
        .unary => |unary| switch (unary.operator) {
            .logical_not => blk: {
                if (exactPrimitiveBooleanResult(program, .{ .unary = .{
                    .operator = unary.operator,
                    .operand = unary.operand,
                } })) |expected| {
                    switch (term.operation) {
                        .boolean_literal => break :blk literalMatchesTerm(term, .{ .boolean = expected }),
                        else => {},
                    }
                }
                break :blk switch (term.operation) {
                    .logical_not => |operand| logicalNotOperandMatchesValue(program, operand, unary.operand, depth + 1),
                    else => false,
                };
            },
            .negate => switch (term.operation) {
                .real_literal => negatedNumberLiteralMatchesTerm(program, term, unary.operand, depth + 1),
                .arithmetic_negate => |operand| termMatchesValue(program, operand, unary.operand, depth + 1),
                else => false,
            },
            .length => switch (term.operation) {
                .integer_literal => |literal| blk: {
                    const expected = normalized_value.exactStringLength(program, unary.operand) orelse break :blk false;
                    const actual = std.fmt.parseUnsigned(usize, literal, 10) catch break :blk false;
                    break :blk actual == expected;
                },
                else => false,
            },
            .bit_not => false,
        },
        .binary => |binary| blk: {
            if (term.operation == .real_literal) {
                const expected = exactFiniteNumberResult(program, value_id) orelse break :blk false;
                break :blk numerals.rationalExactlyRepresentsF64(term.operation.real_literal, expected);
            }
            if (exactPrimitiveBooleanResult(program, .{ .binary = .{
                .operator = binary.operator,
                .left = binary.left,
                .right = binary.right,
            } })) |expected| {
                switch (term.operation) {
                    .boolean_literal => break :blk literalMatchesTerm(term, .{ .boolean = expected }),
                    else => {},
                }
            }
            break :blk switch (term.operation) {
                .binary => |candidate| inner: {
                    const expected_operator = normalized_value.solverBinaryOperator(binary.operator) orelse break :inner false;
                    break :inner candidate.operator == expected_operator and
                        termMatchesValue(program, candidate.left, binary.left, depth + 1) and
                        termMatchesValue(program, candidate.right, binary.right, depth + 1);
                },
                else => false,
            };
        },
    };
}

fn negatedNumberLiteralMatchesTerm(
    program: *const ir.Program,
    term: ir.SolverTerm,
    operand: ir.ValueId,
    depth: usize,
) bool {
    const descriptor = dynamicDescriptorDepth(program, operand, depth) orelse return false;
    if (descriptor.category != .number) return false;
    const negated = negateExactNumber(descriptor.exact_number orelse return false) orelse return false;
    return switch (negated) {
        .number => |value| literalMatchesTerm(term, .{ .number = value }),
        .integer => false,
    };
}

fn exactBit32LiteralMatchesValue(program: *const ir.Program, term: ir.SolverTerm, value_id: ir.ValueId) bool {
    if (term.sort.kind != .bit_vector or term.sort.bit_width != 32 or term.sort.signed) return false;
    const literal = switch (term.operation) {
        .bit_vector_literal => |literal| literal,
        else => return false,
    };
    if (literal.bit_width != 32) return false;
    const actual = numerals.parseCanonicalUnsigned(u32, literal.value) orelse return false;
    const expected = exactPrimitiveBit32Result(program, value_id) orelse return false;
    return actual == expected;
}

fn logicalNotOperandMatchesValue(program: *const ir.Program, term_id: ir.SolverTermId, value_id: ir.ValueId, depth: usize) bool {
    if (value_id.index() >= program.values.len or term_id.index() >= program.solver_terms.len or depth > limit(program)) return false;
    if (program.values[value_id.index()].type.kind == .boolean) {
        return termMatchesValue(program, term_id, value_id, depth + 1);
    }

    const truthiness = program.solver_terms[term_id.index()];
    if (truthiness.sort.kind != .boolean) return false;
    const dynamic_operand = switch (truthiness.operation) {
        .dynamic_truthiness => |operand| operand,
        else => return false,
    };
    if (dynamic_operand.index() >= program.solver_terms.len) return false;
    const dynamic_term = program.solver_terms[dynamic_operand.index()];
    if (dynamic_term.sort.kind != .dynamic_value or dynamic_term.operation != .value) return false;
    return termMatchesValue(program, dynamic_operand, value_id, depth + 1);
}

fn valuesEquivalent(program: *const ir.Program, left: ir.ValueId, right: ir.ValueId, dynamic_domain: bool, depth: usize) bool {
    if (left.index() >= program.values.len or right.index() >= program.values.len or depth > limit(program)) return false;
    if (left == right) return true;
    if (dynamic_domain) {
        const left_dynamic = dynamicDescriptorDepth(program, left, depth + 1);
        const right_dynamic = dynamicDescriptorDepth(program, right, depth + 1);
        if (left_dynamic != null and right_dynamic != null and dynamicDescriptorsEquivalent(left_dynamic.?, right_dynamic.?)) return true;
    }
    const left_source = normalized_value.source(program, left) orelse return false;
    const right_source = normalized_value.source(program, right) orelse return false;
    if (left_source == .copy) return valuesEquivalent(program, left_source.copy.source, right, dynamic_domain, depth + 1);
    if (right_source == .copy) return valuesEquivalent(program, left, right_source.copy.source, dynamic_domain, depth + 1);
    return switch (left_source) {
        .constant => |left_constant| switch (right_source) {
            .constant => |right_constant| sameLiteral(left_constant.literal, right_constant.literal),
            else => false,
        },
        .unary => |left_unary| switch (right_source) {
            .unary => |right_unary| left_unary.operator == right_unary.operator and
                valuesEquivalent(program, left_unary.operand, right_unary.operand, dynamic_domain, depth + 1),
            else => false,
        },
        .binary => |left_binary| switch (right_source) {
            .binary => |right_binary| left_binary.operator == right_binary.operator and
                valuesEquivalent(program, left_binary.left, right_binary.left, dynamic_domain, depth + 1) and
                valuesEquivalent(program, left_binary.right, right_binary.right, dynamic_domain, depth + 1),
            else => false,
        },
        .copy => unreachable,
    };
}

fn valuesDistinct(program: *const ir.Program, left: ir.ValueId, right: ir.ValueId, depth: usize) bool {
    if (left.index() >= program.values.len or right.index() >= program.values.len or depth > limit(program)) return false;
    const left_descriptor = dynamicDescriptorDepth(program, left, depth + 1) orelse return false;
    const right_descriptor = dynamicDescriptorDepth(program, right, depth + 1) orelse return false;
    return dynamicDescriptorsDistinct(left_descriptor, right_descriptor);
}

fn dynamicDescriptorDepth(program: *const ir.Program, value_id: ir.ValueId, depth: usize) ?DynamicDescriptor {
    if (value_id.index() >= program.values.len or depth > limit(program)) return null;
    if (program.values[value_id.index()].id != value_id) return null;
    if (directConstantDescriptor(program, value_id)) |descriptor| return descriptor;
    if (normalized_value.source(program, value_id)) |source| switch (source) {
        .constant => |constant| switch (constant.literal) {
            .nil_value => return .{ .category = .nil_value },
            .boolean => |value| return .{ .category = .boolean, .exact_boolean = value },
            .integer => |value| return .{ .category = .number, .exact_number = .{ .integer = value }, .number_excludes_nan = true },
            .number => |value| return .{ .category = .number, .exact_number = .{ .number = value }, .number_excludes_nan = !std.math.isNan(value) },
            .special_number => |value| return .{ .category = .number, .exact_number = .{ .number = value.asF64() }, .number_excludes_nan = value != .nan },
            .string => |value| return .{ .category = .string, .exact_string = value },
        },
        .copy => |copy| if (dynamicDescriptorDepth(program, copy.source, depth + 1)) |descriptor| return descriptor,
        .unary => |unary| switch (unary.operator) {
            .logical_not => return .{
                .category = .boolean,
                .exact_boolean = exactPrimitiveBooleanResult(program, .{ .unary = .{
                    .operator = unary.operator,
                    .operand = unary.operand,
                } }),
            },
            .negate => {
                const operand = dynamicDescriptorDepth(program, unary.operand, depth + 1);
                const exact_number: ?DynamicNumber = if (operand) |descriptor|
                    if (descriptor.category == .number)
                        if (descriptor.exact_number) |number| negateExactNumber(number) else null
                    else
                        null
                else
                    null;
                return .{
                    .category = .number,
                    .exact_number = exact_number,
                    .number_excludes_nan = program.values[value_id.index()].type.kind == .integer or
                        (operand != null and dynamicDescriptorExcludesNaN(operand.?)),
                };
            },
            .length => {
                const exact_length = normalized_value.exactStringLength(program, unary.operand);
                return .{
                    .category = .number,
                    .exact_number = if (exact_length) |length| .{ .number = @floatFromInt(length) } else null,
                    .number_excludes_nan = true,
                };
            },
            .bit_not => {},
        },
        .binary => |binary| switch (binary.operator) {
            .equal, .not_equal, .less, .less_equal, .greater, .greater_equal, .logical_and, .logical_or => return .{
                .category = .boolean,
                .exact_boolean = exactPrimitiveBooleanResult(program, .{ .binary = .{
                    .operator = binary.operator,
                    .left = binary.left,
                    .right = binary.right,
                } }),
            },
            .add, .subtract, .multiply, .divide, .floor_divide, .modulo, .power => {
                const result_kind = program.values[value_id.index()].type.kind;
                const exact_number = if (result_kind == .integer)
                    null
                else
                    exactPrimitiveBinaryNumber(
                        binary.operator,
                        dynamicDescriptorDepth(program, binary.left, depth + 1),
                        dynamicDescriptorDepth(program, binary.right, depth + 1),
                    );
                return .{
                    .category = .number,
                    .exact_number = exact_number,
                    .number_excludes_nan = result_kind == .integer or
                        (exact_number != null and !dynamicNumberIsNaN(exact_number.?)),
                };
            },
            .concat => return if (normalized_value.exactStringLength(program, value_id) != null)
                .{
                    .category = .string,
                    .exact_string_source = .{ .program = program, .value = value_id },
                }
            else
                .{ .category = .string },
            .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => {},
        },
    };
    if (exactPrimitiveBit32ResultDepth(program, value_id, depth + 1)) |result| return .{
        .category = .number,
        .exact_number = .{ .number = @floatFromInt(result) },
        .number_excludes_nan = true,
    };
    if (freshAllocationDescriptor(program, value_id)) |descriptor| return descriptor;
    if (functionReferenceDescriptor(program, value_id)) |descriptor| return descriptor;
    return switch (program.values[value_id.index()].type.kind) {
        .nil_value => .{ .category = .nil_value },
        .boolean => .{ .category = .boolean },
        .integer => .{ .category = .number, .number_excludes_nan = true },
        .number => .{ .category = .number },
        .string => .{ .category = .string },
        .table => .{ .category = .table },
        .function => .{ .category = .function_value },
        .thread => .{ .category = .thread },
        .userdata => .{ .category = .userdata },
        .tuple => .{ .category = .tuple },
        .dynamic => null,
    };
}

fn exactPrimitiveBit32ResultDepth(program: *const ir.Program, value_id: ir.ValueId, depth: usize) ?u32 {
    if (value_id.index() >= program.values.len or depth > limit(program)) return null;
    const value = program.values[value_id.index()];
    if (value.id != value_id or !isUnsigned32Type(value.type)) return null;
    const instruction = canonicalSingleResultInstruction(program, value_id) orelse return null;
    if (!normalized_value.isExactPure(instruction.effects)) return null;
    return switch (instruction.operation) {
        .constant => |literal| switch (literal) {
            .integer => |integer| numerals.parseCanonicalUnsigned(u32, integer),
            else => null,
        },
        .copy => |source| exactPrimitiveBit32ResultDepth(program, source, depth + 1),
        .unary => |unary| if (unary.operator == .bit_not and unary.mode == .primitive and
            unsigned32Value(program, unary.operand))
            if (exactPrimitiveBit32ResultDepth(program, unary.operand, depth + 1)) |operand| ~operand else null
        else
            null,
        .binary => |binary| blk: {
            if (binary.mode != .primitive or
                !unsigned32Value(program, binary.left) or
                !unsigned32Value(program, binary.right)) break :blk null;
            const is_shift = binary.operator == .shift_left or binary.operator == .shift_right;
            if (is_shift != (binary.shift_behavior != null)) break :blk null;
            const left = exactPrimitiveBit32ResultDepth(program, binary.left, depth + 1) orelse break :blk null;
            const right = exactPrimitiveBit32ResultDepth(program, binary.right, depth + 1) orelse break :blk null;
            break :blk switch (binary.operator) {
                .bit_and => left & right,
                .bit_or => left | right,
                .bit_xor => left ^ right,
                .shift_left => switch (binary.shift_behavior.?) {
                    .luau_bit32 => if (right < 32) left << @as(u5, @intCast(right)) else null,
                    .zero_saturating => if (right < 32) left << @as(u5, @intCast(right)) else 0,
                },
                .shift_right => switch (binary.shift_behavior.?) {
                    .luau_bit32 => if (right < 32) left >> @as(u5, @intCast(right)) else null,
                    .zero_saturating => if (right < 32) left >> @as(u5, @intCast(right)) else 0,
                },
                else => null,
            };
        },
        else => null,
    };
}

fn unsigned32Value(program: *const ir.Program, value_id: ir.ValueId) bool {
    return value_id.index() < program.values.len and isUnsigned32Type(program.values[value_id.index()].type);
}

fn isUnsigned32Type(value_type: ir.ValueType) bool {
    return value_type.kind == .integer and value_type.bit_width == 32 and !value_type.signed;
}

fn directConstantDescriptor(program: *const ir.Program, value_id: ir.ValueId) ?DynamicDescriptor {
    const value = program.values[value_id.index()];
    const instruction = canonicalSingleResultInstruction(program, value_id) orelse return null;
    if (!normalized_value.isExactPure(instruction.effects)) return null;
    const literal = switch (instruction.operation) {
        .constant => |constant| constant,
        else => return null,
    };
    return switch (literal) {
        .nil_value => if (value.type.kind == .nil_value or value.type.kind == .dynamic)
            .{ .category = .nil_value }
        else
            null,
        .boolean => |constant| if (value.type.kind == .boolean or value.type.kind == .dynamic)
            .{ .category = .boolean, .exact_boolean = constant }
        else
            null,
        .integer => |constant| if (value.type.kind == .integer or value.type.kind == .number or value.type.kind == .dynamic)
            .{ .category = .number, .exact_number = .{ .integer = constant }, .number_excludes_nan = true }
        else
            null,
        .number => |constant| if (value.type.kind == .number or value.type.kind == .dynamic)
            .{ .category = .number, .exact_number = .{ .number = constant }, .number_excludes_nan = !std.math.isNan(constant) }
        else
            null,
        .special_number => |constant| if (value.type.kind == .number or value.type.kind == .dynamic)
            .{ .category = .number, .exact_number = .{ .number = constant.asF64() }, .number_excludes_nan = constant != .nan }
        else
            null,
        .string => |constant| if (value.type.kind == .string or value.type.kind == .dynamic)
            .{ .category = .string, .exact_string = constant }
        else
            null,
    };
}

fn freshAllocationDescriptor(program: *const ir.Program, value_id: ir.ValueId) ?DynamicDescriptor {
    const value = program.values[value_id.index()];
    const instruction = canonicalSingleResultInstruction(program, value_id) orelse return null;
    return switch (instruction.operation) {
        .make_table, .make_table_literal => if (value.type.kind == .table or value.type.kind == .dynamic)
            .{ .category = .table, .allocation_site = instruction.id }
        else
            null,
        .coroutine_create => if (value.type.kind == .thread or value.type.kind == .dynamic)
            .{ .category = .thread, .allocation_site = instruction.id }
        else
            null,
        else => null,
    };
}

fn functionReferenceDescriptor(program: *const ir.Program, value_id: ir.ValueId) ?DynamicDescriptor {
    const value = program.values[value_id.index()];
    if (value.type.kind != .function and value.type.kind != .dynamic) return null;
    const instruction = canonicalSingleResultInstruction(program, value_id) orelse return null;
    const target_id = switch (instruction.operation) {
        .function_ref => |target| target,
        else => return null,
    };
    if (target_id.index() >= program.functions.len) return null;
    const target = program.functions[target_id.index()];
    if (target.id != target_id or target.lexical_parent != null or target.captures.len != 0) return null;
    return .{ .category = .function_value, .function_reference = target_id };
}

fn canonicalSingleResultInstruction(program: *const ir.Program, value_id: ir.ValueId) ?ir.Instruction {
    const value = program.values[value_id.index()];
    const result = switch (value.origin) {
        .instruction_result => |result| result,
        else => return null,
    };
    if (result.index != 0 or result.instruction.index() >= program.instructions.len) return null;
    const instruction = program.instructions[result.instruction.index()];
    if (instruction.id != result.instruction or
        instruction.results.len != 1 or
        instruction.results[0] != value_id)
    {
        return null;
    }
    return instruction;
}

fn dynamicTermDescriptorDepth(program: *const ir.Program, term_id: ir.SolverTermId, depth: usize) ?DynamicDescriptor {
    if (term_id.index() >= program.solver_terms.len or depth > limit(program)) return null;
    const term = program.solver_terms[term_id.index()];
    if (term.sort.kind != .dynamic_value) return null;
    return switch (term.operation) {
        .value => |value| dynamicDescriptorDepth(program, value, depth + 1),
        .value_definition => |definition| dynamicTermDescriptorDepth(program, definition.expression, depth + 1),
        .if_then_else => |selection| blk: {
            const then_descriptor = dynamicTermDescriptorDepth(program, selection.then_term, depth + 1) orelse break :blk null;
            const else_descriptor = dynamicTermDescriptorDepth(program, selection.else_term, depth + 1) orelse break :blk null;
            if (then_descriptor.category != else_descriptor.category) break :blk null;
            break :blk if (dynamicDescriptorsEquivalent(then_descriptor, else_descriptor))
                then_descriptor
            else
                .{
                    .category = then_descriptor.category,
                    .number_excludes_nan = then_descriptor.category == .number and
                        dynamicDescriptorExcludesNaN(then_descriptor) and
                        dynamicDescriptorExcludesNaN(else_descriptor),
                };
        },
        else => null,
    };
}

fn dynamicDescriptorExcludesNaN(descriptor: DynamicDescriptor) bool {
    const is_nan = dynamicDescriptorIsNaN(descriptor) orelse return false;
    return !is_nan;
}

fn literalMatchesTerm(term: ir.SolverTerm, literal: ir.Literal) bool {
    return switch (literal) {
        .boolean => |value| term.sort.kind == .boolean and switch (term.operation) {
            .boolean_literal => |candidate| candidate == value,
            else => false,
        },
        .integer => |value| term.sort.kind == .integer and switch (term.operation) {
            .integer_literal => |candidate| std.mem.eql(u8, candidate, value),
            else => false,
        },
        .number => |value| term.sort.kind == .real and switch (term.operation) {
            .real_literal => |candidate| numerals.rationalExactlyRepresentsF64(candidate, value),
            else => false,
        },
        .nil_value, .special_number, .string => false,
    };
}

fn sameLiteral(left: ir.Literal, right: ir.Literal) bool {
    return switch (left) {
        .boolean => |value| switch (right) {
            .boolean => |candidate| candidate == value,
            else => false,
        },
        .integer => |value| switch (right) {
            .integer => |candidate| std.mem.eql(u8, candidate, value),
            else => false,
        },
        .nil_value => right == .nil_value,
        .string => |value| switch (right) {
            .string => |candidate| std.mem.eql(u8, value, candidate),
            else => false,
        },
        .number => false,
        .special_number => |value| switch (right) {
            .special_number => |candidate| candidate == value,
            else => false,
        },
    };
}

fn sortAcceptsValue(sort: ir.SolverSort, value_type: ir.ValueType) bool {
    return switch (value_type.kind) {
        .dynamic => true,
        .boolean => sort.kind == .boolean or sort.kind == .dynamic_value,
        .integer => sort.kind == .integer or
            (sort.kind == .bit_vector and sort.bit_width == value_type.bit_width and sort.signed == value_type.signed) or
            sort.kind == .dynamic_value,
        .number => sort.kind == .real or sort.kind == .dynamic_value,
        .nil_value, .string, .table, .function, .thread, .userdata, .tuple => sort.kind == .dynamic_value,
    };
}

fn sameSort(left: ir.SolverSort, right: ir.SolverSort) bool {
    return left.kind == right.kind and left.bit_width == right.bit_width and left.signed == right.signed;
}

fn limit(program: *const ir.Program) usize {
    return program.solver_terms.len + program.values.len + program.instructions.len;
}
