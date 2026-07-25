const std = @import("std");
const ir = @import("ir.zig");
const normalized_value = @import("normalized_value.zig");
const numerals = @import("numerals.zig");
const solver = @import("solver.zig");
const solver_equivalence = @import("solver_equivalence.zig");
const solver_preconditions = @import("solver_preconditions.zig");
const solver_term = @import("solver_term.zig");
const solver_value_definition = @import("solver_value_definition.zig");

const BuiltExpression = struct {
    term: ir.SolverTermId,
    valid_when: ?ir.SolverTermId = null,
};

const GuardedOperand = struct {
    operand: ir.SolverTermId,
    guard: ir.SolverTermId,
};

pub fn ensureDefinition(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    value_id: ir.ValueId,
) std.mem.Allocator.Error!?ir.SolverTermId {
    const initial_len = terms.items.len;
    const result = try ensureDefinitionDepth(allocator, program, terms, value_id, 0);
    if (result == null) terms.items = terms.items[0..initial_len];
    return result;
}

pub fn ensureCanonicalTerm(
    allocator: std.mem.Allocator,
    terms: *std.ArrayList(ir.SolverTerm),
    sort: ir.SolverSort,
    operation: ir.SolverTermOperation,
) std.mem.Allocator.Error!ir.SolverTermId {
    return ensureTerm(allocator, terms, sort, operation);
}

fn ensureDefinitionDepth(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    value_id: ir.ValueId,
    depth: usize,
) std.mem.Allocator.Error!?ir.SolverTermId {
    if (value_id.index() >= program.values.len or depth > recursionLimit(program)) return null;
    const result_sort = preferredSort(program, value_id, depth) orelse return null;
    if (findDefinition(program, terms.items, value_id, result_sort)) |existing| return existing;

    const initial_len = terms.items.len;
    const instruction = definingInstruction(program, value_id) orelse return null;
    const built = try buildExpression(allocator, program, terms, instruction, result_sort, depth + 1) orelse {
        terms.items = terms.items[0..initial_len];
        return null;
    };
    const definition: ir.SolverValueDefinition = .{
        .value = value_id,
        .expression = built.term,
        .valid_when = built.valid_when,
    };
    const definition_id = ir.SolverTermId.fromIndex(terms.items.len);
    try terms.append(allocator, .{
        .id = definition_id,
        .sort = result_sort,
        .operation = .{ .value_definition = definition },
    });

    var working = program.*;
    working.solver_terms = terms.items;
    if (!solver_value_definition.valid(&working, result_sort, definition)) {
        terms.items = terms.items[0..initial_len];
        return null;
    }
    return definition_id;
}

fn buildExpression(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    instruction: ir.Instruction,
    result_sort: ir.SolverSort,
    depth: usize,
) std.mem.Allocator.Error!?BuiltExpression {
    if (sameSort(result_sort, unsignedBit32Sort()) and instruction.results.len == 1) {
        if (solver_equivalence.exactPrimitiveBit32Result(program, instruction.results[0])) |value| {
            const literal = try std.fmt.allocPrint(allocator, "{d}", .{value});
            return .{ .term = try ensureTerm(allocator, terms, result_sort, .{ .bit_vector_literal = .{
                .value = literal,
                .bit_width = 32,
            } }) };
        }
    }
    if (result_sort.kind == .real and instruction.results.len == 1) switch (instruction.operation) {
        .binary => if (solver_equivalence.exactFiniteNumberResult(program, instruction.results[0])) |value| {
            return .{ .term = try ensureTerm(allocator, terms, result_sort, .{
                .real_literal = try numerals.exactF64RationalAlloc(allocator, value) orelse return null,
            }) };
        },
        else => {},
    };
    return switch (instruction.operation) {
        .constant => |literal| try buildConstant(allocator, terms, result_sort, literal),
        .copy => |source| if (try ensureValueTerm(allocator, program, terms, source, result_sort, depth)) |term|
            .{ .term = term }
        else
            null,
        .unary => |operation| try buildUnary(allocator, program, terms, operation, result_sort, depth),
        .binary => |operation| try buildBinary(allocator, program, terms, operation, result_sort, depth),
        else => null,
    };
}

fn buildConstant(
    allocator: std.mem.Allocator,
    terms: *std.ArrayList(ir.SolverTerm),
    result_sort: ir.SolverSort,
    literal: ir.Literal,
) std.mem.Allocator.Error!?BuiltExpression {
    const operation: ir.SolverTermOperation = switch (literal) {
        .boolean => |value| if (result_sort.kind == .boolean)
            .{ .boolean_literal = value }
        else
            return null,
        .integer => |value| if (result_sort.kind == .integer)
            .{ .integer_literal = value }
        else
            return null,
        .number => |value| if (result_sort.kind == .real)
            .{ .real_literal = try numerals.exactF64RationalAlloc(allocator, value) orelse return null }
        else
            return null,
        .nil_value, .special_number, .string => return null,
    };
    return .{ .term = try ensureTerm(allocator, terms, result_sort, operation) };
}

fn buildUnary(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    operation: ir.Unary,
    result_sort: ir.SolverSort,
    depth: usize,
) std.mem.Allocator.Error!?BuiltExpression {
    if (result_sort.kind == .boolean) {
        if (solver_equivalence.exactPrimitiveBooleanResult(program, .{ .unary = operation })) |value| {
            return .{ .term = try ensureTerm(allocator, terms, result_sort, .{ .boolean_literal = value }) };
        }
    }
    if (operation.operator == .length) {
        if (result_sort.kind != .integer) return null;
        const length = normalized_value.exactStringLength(program, operation.operand) orelse return null;
        const literal = try std.fmt.allocPrint(allocator, "{d}", .{length});
        return .{ .term = try ensureTerm(allocator, terms, result_sort, .{ .integer_literal = literal }) };
    }
    if (operation.operator == .logical_not) {
        return buildLogicalNot(allocator, program, terms, operation, result_sort, depth);
    }
    if (operation.operator == .negate and result_sort.kind == .real) {
        if (exactNegatedReal(program, operation.operand)) |value| {
            return .{ .term = try ensureTerm(allocator, terms, result_sort, .{
                .real_literal = try numerals.exactF64RationalAlloc(allocator, value) orelse return null,
            }) };
        }
        if (operation.operand.index() >= program.values.len or
            program.values[operation.operand.index()].type.kind != .number)
        {
            return null;
        }
        const operand = try ensureValueTerm(allocator, program, terms, operation.operand, result_sort, depth) orelse return null;
        return .{ .term = try ensureTerm(allocator, terms, result_sort, .{ .arithmetic_negate = operand }) };
    }
    const operand_sort: ir.SolverSort = switch (operation.operator) {
        .logical_not => unreachable,
        .negate => .{ .kind = .integer },
        .bit_not => unsignedBit32Sort(),
        .length => unreachable,
    };
    if (!sameSort(result_sort, operand_sort)) return null;
    const operand = try ensureValueTerm(allocator, program, terms, operation.operand, operand_sort, depth) orelse return null;
    const solver_operation: ir.SolverTermOperation = switch (operation.operator) {
        .logical_not => unreachable,
        .negate => .{ .arithmetic_negate = operand },
        .bit_not => .{ .bit_vector_not = operand },
        .length => unreachable,
    };
    return .{ .term = try ensureTerm(allocator, terms, result_sort, solver_operation) };
}

fn exactNegatedReal(program: *const ir.Program, operand: ir.ValueId) ?f64 {
    const descriptor = solver_equivalence.dynamicValueDescriptor(program, operand) orelse return null;
    if (descriptor.category != .number) return null;
    return switch (solver_equivalence.negateExactNumber(descriptor.exact_number orelse return null) orelse return null) {
        .number => |value| value,
        .integer => null,
    };
}

fn buildLogicalNot(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    operation: ir.Unary,
    result_sort: ir.SolverSort,
    depth: usize,
) std.mem.Allocator.Error!?BuiltExpression {
    const boolean_sort: ir.SolverSort = .{ .kind = .boolean };
    if (!sameSort(result_sort, boolean_sort) or operation.operand.index() >= program.values.len) return null;

    const operand_type = program.values[operation.operand.index()].type;
    const truth = if (operand_type.kind == .boolean)
        try ensureValueTerm(allocator, program, terms, operation.operand, boolean_sort, depth) orelse return null
    else blk: {
        const dynamic_sort: ir.SolverSort = .{ .kind = .dynamic_value };
        if (!sortAcceptsValue(dynamic_sort, operand_type)) return null;
        const dynamic_operand = try ensureValueLeaf(allocator, terms, operation.operand, dynamic_sort);
        break :blk try ensureTerm(allocator, terms, boolean_sort, .{ .dynamic_truthiness = dynamic_operand });
    };
    return .{ .term = try ensureTerm(allocator, terms, boolean_sort, .{ .logical_not = truth }) };
}

fn buildBinary(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    operation: ir.Binary,
    result_sort: ir.SolverSort,
    depth: usize,
) std.mem.Allocator.Error!?BuiltExpression {
    if (operation.operator == .floor_divide or operation.operator == .modulo) {
        return buildPartialIntegerBinary(allocator, program, terms, operation, result_sort, depth);
    }
    const is_shift = operation.operator == .shift_left or operation.operator == .shift_right;
    if (is_shift != (operation.shift_behavior != null)) return null;
    if (result_sort.kind == .boolean) {
        if (solver_equivalence.exactPrimitiveBooleanResult(program, .{ .binary = operation })) |value| {
            return .{ .term = try ensureTerm(allocator, terms, result_sort, .{ .boolean_literal = value }) };
        }
    }
    const solver_operator = normalized_value.solverBinaryOperator(operation.operator) orelse return null;
    const operand_sort: ir.SolverSort = switch (operation.operator) {
        .add, .subtract, .multiply => .{ .kind = .integer },
        .logical_and, .logical_or => .{ .kind = .boolean },
        .equal, .not_equal, .less, .less_equal, .greater, .greater_equal => comparisonSort(program, operation, depth) orelse return null,
        .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => unsignedBit32Sort(),
        else => unreachable,
    };
    const expected_result: ir.SolverSort = switch (operation.operator) {
        .equal, .not_equal, .less, .less_equal, .greater, .greater_equal => .{ .kind = .boolean },
        else => operand_sort,
    };
    if (!sameSort(result_sort, expected_result)) return null;
    const left = try ensureValueTerm(allocator, program, terms, operation.left, operand_sort, depth) orelse return null;
    const right = try ensureValueTerm(allocator, program, terms, operation.right, operand_sort, depth) orelse return null;
    if ((operation.operator == .equal or operation.operator == .not_equal) and
        operand_sort.kind == .dynamic_value and
        !solver_equivalence.dynamicValuesHaveUnguardedPrimitiveEquality(program, operation.left, operation.right))
    {
        return try buildTotalDynamicNumericEquality(allocator, terms, operation, left, right);
    }
    const valid_when: ?ir.SolverTermId = if (is_shift and
        operation.shift_behavior.? == .luau_bit32 and
        !hasBoundedBit32ShiftCount(program, operation.right))
        try ensureBit32ShiftGuard(allocator, program, terms, operation.right, depth)
    else
        null;
    return .{ .term = try ensureTerm(allocator, terms, result_sort, .{ .binary = .{
        .operator = solver_operator,
        .left = left,
        .right = right,
    } }), .valid_when = valid_when };
}

fn buildTotalDynamicNumericEquality(
    allocator: std.mem.Allocator,
    terms: *std.ArrayList(ir.SolverTerm),
    operation: ir.Binary,
    left: ir.SolverTermId,
    right: ir.SolverTermId,
) std.mem.Allocator.Error!BuiltExpression {
    const boolean_sort: ir.SolverSort = .{ .kind = .boolean };
    const guard = try ensureDynamicEqualityGuard(allocator, terms, operation.left, operation.right);
    const value_equal = try ensureTerm(allocator, terms, boolean_sort, .{ .binary = .{
        .operator = .equal,
        .left = left,
        .right = right,
    } });
    const total_equal = try ensureTerm(allocator, terms, boolean_sort, .{ .binary = .{
        .operator = .logical_and,
        .left = guard,
        .right = value_equal,
    } });
    return .{ .term = if (operation.operator == .equal)
        total_equal
    else
        try ensureTerm(allocator, terms, boolean_sort, .{ .logical_not = total_equal }) };
}

fn ensureDynamicEqualityGuard(
    allocator: std.mem.Allocator,
    terms: *std.ArrayList(ir.SolverTerm),
    left_value: ir.ValueId,
    right_value: ir.ValueId,
) std.mem.Allocator.Error!ir.SolverTermId {
    const dynamic_sort: ir.SolverSort = .{ .kind = .dynamic_value };
    const boolean_sort: ir.SolverSort = .{ .kind = .boolean };
    const left = try ensureValueLeaf(allocator, terms, left_value, dynamic_sort);
    const right = try ensureValueLeaf(allocator, terms, right_value, dynamic_sort);
    const left_is_nan = try ensureTerm(allocator, terms, boolean_sort, .{ .dynamic_number_is_nan = left });
    const right_is_nan = try ensureTerm(allocator, terms, boolean_sort, .{ .dynamic_number_is_nan = right });
    const left_valid = try ensureTerm(allocator, terms, boolean_sort, .{ .logical_not = left_is_nan });
    const right_valid = try ensureTerm(allocator, terms, boolean_sort, .{ .logical_not = right_is_nan });
    return ensureTerm(allocator, terms, boolean_sort, .{ .binary = .{
        .operator = .logical_and,
        .left = left_valid,
        .right = right_valid,
    } });
}

fn buildPartialIntegerBinary(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    operation: ir.Binary,
    result_sort: ir.SolverSort,
    depth: usize,
) std.mem.Allocator.Error!?BuiltExpression {
    const integer_sort: ir.SolverSort = .{ .kind = .integer };
    if (!sameSort(result_sort, integer_sort)) return null;
    const left = try ensureValueTerm(allocator, program, terms, operation.left, integer_sort, depth) orelse return null;
    const guarded = try ensureNonzeroOperand(allocator, program, terms, operation.right, integer_sort, depth) orelse return null;
    const expression: ir.SolverTermOperation = switch (operation.operator) {
        .floor_divide => .{ .division = .{
            .mode = .integer_floor,
            .left = left,
            .right = guarded.operand,
            .defined_by = guarded.guard,
        } },
        .modulo => .{ .remainder = .{
            .mode = .integer_floor,
            .left = left,
            .right = guarded.operand,
            .defined_by = guarded.guard,
        } },
        else => unreachable,
    };
    return .{ .term = try ensureTerm(allocator, terms, result_sort, expression) };
}

fn ensureNonzeroOperand(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    value_id: ir.ValueId,
    sort: ir.SolverSort,
    depth: usize,
) std.mem.Allocator.Error!?GuardedOperand {
    var working = program.*;
    working.solver_terms = terms.items;
    for (terms.items) |term| {
        if (term.sort.kind != .boolean) continue;
        const operand = switch (term.operation) {
            .is_nonzero => |candidate| candidate,
            else => continue,
        };
        if (operand.index() >= terms.items.len or !sameSort(terms.items[operand.index()].sort, sort)) continue;
        if (solver_equivalence.termRepresentsValue(&working, operand, value_id)) {
            return .{ .operand = operand, .guard = term.id };
        }
    }
    const operand = try ensureValueTerm(allocator, program, terms, value_id, sort, depth) orelse return null;
    return .{
        .operand = operand,
        .guard = try ensureTerm(allocator, terms, .{ .kind = .boolean }, .{ .is_nonzero = operand }),
    };
}

fn ensureBit32ShiftGuard(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    count: ir.ValueId,
    depth: usize,
) std.mem.Allocator.Error!ir.SolverTermId {
    var working = program.*;
    working.solver_terms = terms.items;
    for (terms.items) |term| {
        if (term.sort.kind != .boolean) continue;
        const binary = switch (term.operation) {
            .binary => |value| value,
            else => continue,
        };
        const threshold: []const u8 = switch (binary.operator) {
            .less => "32",
            .less_equal => "31",
            else => continue,
        };
        if (solver_equivalence.termRepresentsValue(&working, binary.left, count) and
            isUnsignedBitVectorLiteral(terms.items, binary.right, threshold)) return term.id;
    }

    const count_term = (try ensureValueTerm(allocator, program, terms, count, unsignedBit32Sort(), depth)) orelse unreachable;
    const limit = try ensureTerm(allocator, terms, unsignedBit32Sort(), .{ .bit_vector_literal = .{
        .value = "32",
        .bit_width = 32,
    } });
    return ensureTerm(allocator, terms, .{ .kind = .boolean }, .{ .binary = .{
        .operator = .less,
        .left = count_term,
        .right = limit,
    } });
}

fn isUnsignedBitVectorLiteral(terms: []const ir.SolverTerm, term_id: ir.SolverTermId, expected: []const u8) bool {
    if (term_id.index() >= terms.len) return false;
    const term = terms[term_id.index()];
    if (!sameSort(term.sort, unsignedBit32Sort())) return false;
    return switch (term.operation) {
        .bit_vector_literal => |literal| literal.bit_width == 32 and std.mem.eql(u8, literal.value, expected),
        else => false,
    };
}

fn ensureValueTerm(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    value_id: ir.ValueId,
    sort: ir.SolverSort,
    depth: usize,
) std.mem.Allocator.Error!?ir.SolverTermId {
    if (value_id.index() >= program.values.len or !sortAcceptsValue(sort, program.values[value_id.index()].type)) return null;
    if (findDefinition(program, terms.items, value_id, sort)) |definition| return definition;
    if (preferredSort(program, value_id, depth)) |preferred| {
        if (sameSort(preferred, sort)) {
            if (try ensureDefinitionDepth(allocator, program, terms, value_id, depth + 1)) |definition| return definition;
        }
    }
    return try ensureValueLeaf(allocator, terms, value_id, sort);
}

fn ensureValueLeaf(
    allocator: std.mem.Allocator,
    terms: *std.ArrayList(ir.SolverTerm),
    value_id: ir.ValueId,
    sort: ir.SolverSort,
) std.mem.Allocator.Error!ir.SolverTermId {
    for (terms.items) |term| {
        if (sameSort(term.sort, sort) and term.operation == .value and term.operation.value == value_id) return term.id;
    }
    return ensureTerm(allocator, terms, sort, .{ .value = value_id });
}

fn ensureTerm(
    allocator: std.mem.Allocator,
    terms: *std.ArrayList(ir.SolverTerm),
    sort: ir.SolverSort,
    operation: ir.SolverTermOperation,
) std.mem.Allocator.Error!ir.SolverTermId {
    for (terms.items) |term| {
        if (sameSort(term.sort, sort) and sameOperation(term.operation, operation)) return term.id;
    }
    const id = ir.SolverTermId.fromIndex(terms.items.len);
    try terms.append(allocator, .{ .id = id, .sort = sort, .operation = operation });
    return id;
}

fn findDefinition(
    program: *const ir.Program,
    terms: []const ir.SolverTerm,
    value_id: ir.ValueId,
    sort: ir.SolverSort,
) ?ir.SolverTermId {
    var working = program.*;
    working.solver_terms = terms;
    for (terms) |term| {
        if (!sameSort(term.sort, sort) or term.operation != .value_definition) continue;
        const definition = term.operation.value_definition;
        if (definition.value == value_id and solver_value_definition.valid(&working, sort, definition)) return term.id;
    }
    return null;
}

fn preferredSort(program: *const ir.Program, value_id: ir.ValueId, depth: usize) ?ir.SolverSort {
    if (value_id.index() >= program.values.len or depth > recursionLimit(program)) return null;
    const value = program.values[value_id.index()];
    return switch (value.type.kind) {
        .boolean => .{ .kind = .boolean },
        .integer => blk: {
            if (isUnsigned32(value.type) and solver_equivalence.exactPrimitiveBit32Result(program, value_id) != null) {
                break :blk unsignedBit32Sort();
            }
            if (definingInstruction(program, value_id)) |instruction| switch (instruction.operation) {
                .copy => |source| if (preferredSort(program, source, depth + 1)) |source_sort| {
                    if (sortAcceptsValue(source_sort, value.type)) break :blk source_sort;
                },
                .unary => |operation| if (operation.operator == .bit_not and isUnsigned32(value.type)) break :blk unsignedBit32Sort(),
                .binary => |operation| if ((operation.operator == .bit_and or
                    operation.operator == .bit_or or
                    operation.operator == .bit_xor or
                    operation.operator == .shift_left or
                    operation.operator == .shift_right) and isUnsigned32(value.type)) break :blk unsignedBit32Sort(),
                else => {},
            };
            break :blk .{ .kind = .integer };
        },
        .number => .{ .kind = .real },
        .dynamic, .nil_value, .string, .table, .function, .thread, .userdata, .tuple => null,
    };
}

fn comparisonSort(program: *const ir.Program, operation: ir.Binary, depth: usize) ?ir.SolverSort {
    if (operation.left.index() >= program.values.len or operation.right.index() >= program.values.len) return null;
    const left = program.values[operation.left.index()].type;
    const right = program.values[operation.right.index()].type;
    if (left.kind == .boolean and right.kind == .boolean) return .{ .kind = .boolean };
    if (left.kind == .integer and right.kind == .integer) {
        const left_sort = preferredSort(program, operation.left, depth + 1) orelse return null;
        const right_sort = preferredSort(program, operation.right, depth + 1) orelse return null;
        if (sameSort(left_sort, right_sort)) return left_sort;
        if (isUnsigned32(left) and isUnsigned32(right) and
            (left_sort.kind == .bit_vector or right_sort.kind == .bit_vector)) return unsignedBit32Sort();
        return .{ .kind = .integer };
    }
    if ((operation.operator == .equal or operation.operator == .not_equal) and
        solver_equivalence.dynamicValuesHavePrimitiveEquality(program, operation.left, operation.right))
    {
        return .{ .kind = .dynamic_value };
    }
    return null;
}

fn definingInstruction(program: *const ir.Program, value_id: ir.ValueId) ?ir.Instruction {
    if (value_id.index() >= program.values.len) return null;
    const origin = switch (program.values[value_id.index()].origin) {
        .instruction_result => |origin| origin,
        else => return null,
    };
    if (origin.instruction.index() >= program.instructions.len) return null;
    const instruction = program.instructions[origin.instruction.index()];
    if (instruction.id != origin.instruction or
        origin.index >= instruction.results.len or
        instruction.results[origin.index] != value_id) return null;
    return instruction;
}

fn sortAcceptsValue(sort: ir.SolverSort, value_type: ir.ValueType) bool {
    return switch (value_type.kind) {
        .dynamic => sort.kind == .dynamic_value,
        .boolean => sort.kind == .boolean or sort.kind == .dynamic_value,
        .integer => sort.kind == .integer or
            (sort.kind == .bit_vector and sort.bit_width == value_type.bit_width and sort.signed == value_type.signed) or
            sort.kind == .dynamic_value,
        .number => sort.kind == .real or sort.kind == .dynamic_value,
        .nil_value, .string, .table, .function, .thread, .userdata, .tuple => sort.kind == .dynamic_value,
    };
}

fn sameOperation(left: ir.SolverTermOperation, right: ir.SolverTermOperation) bool {
    if (!solver_term.sameOperationHead(left, right)) return false;
    var left_dependencies = solver_term.dependencies(left);
    var right_dependencies = solver_term.dependencies(right);
    while (left_dependencies.next()) |left_dependency| {
        const right_dependency = right_dependencies.next() orelse return false;
        if (right_dependency != left_dependency) return false;
    }
    return right_dependencies.next() == null;
}

fn sameSort(left: ir.SolverSort, right: ir.SolverSort) bool {
    return left.kind == right.kind and left.bit_width == right.bit_width and left.signed == right.signed;
}

fn unsignedBit32Sort() ir.SolverSort {
    return .{ .kind = .bit_vector, .bit_width = 32 };
}

fn isUnsigned32(value_type: ir.ValueType) bool {
    return value_type.kind == .integer and value_type.bit_width == 32 and !value_type.signed;
}

fn hasBoundedBit32ShiftCount(program: *const ir.Program, value_id: ir.ValueId) bool {
    return switch (solver.evaluateValue(program, value_id)) {
        .integer => |value| value >= 0 and value < 32,
        .bit_vector => |value| value.bit_width == 32 and value.value < 32,
        .boolean, .real, .unknown => false,
    };
}

fn recursionLimit(program: *const ir.Program) usize {
    return program.values.len + program.instructions.len + 1;
}

test "demand-driven promotion builds a nested u32 predicate once" {
    const fixture = @import("fixtures.zig").automatic_promotion_module;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var instructions = fixture.instructions;
    instructions[fixture.i_left.index()].operation = .{ .environment_get = .{
        .target = .{ .ambient = {} },
        .name = "unknown_u32",
    } };
    instructions[fixture.i_left.index()].effects = .semantic_environment_read;
    instructions[fixture.i_zero.index()].operation = .{ .binary = .{
        .operator = .bit_and,
        .left = fixture.v_left,
        .right = fixture.v_mask,
        .mode = .primitive,
    } };
    var program = fixture.program;
    program.instructions = &instructions;
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(allocator);

    const condition_term = (try ensureDefinition(allocator, &program, &terms, fixture.v_condition)).?;
    try std.testing.expectEqual(@as(usize, 8), terms.items.len);
    try std.testing.expect(terms.items[condition_term.index()].operation == .value_definition);
    try std.testing.expectEqual(fixture.v_condition, terms.items[condition_term.index()].operation.value_definition.value);
    try std.testing.expectEqual(fixture.v_masked, terms.items[4].operation.value_definition.value);
    const first_count = terms.items.len;
    try std.testing.expectEqual(condition_term, (try ensureDefinition(allocator, &program, &terms, fixture.v_condition)).?);
    try std.testing.expectEqual(first_count, terms.items.len);

    program.solver_terms = terms.items;
    var report = try @import("validate.zig").validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());

    instructions[fixture.i_masked.index()].operation.binary.operator = .bit_or;
    var tampered_report = try @import("validate.zig").validate(std.testing.allocator, &program, .core);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.invalid_solver_value_definition));
}

test "number negation promotion preserves exact frontend unary literals" {
    const operand = ir.ValueId.fromIndex(0);
    const result = ir.ValueId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = operand, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = result, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{operand}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .unary = .{ .operator = .negate, .operand = operand } }, .results = &.{result}, .effects = .pure },
    };
    var program: ir.Program = .{
        .program_id = "exact-number-negation-promotion",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(arena.allocator());

    const definition_id = (try ensureDefinition(arena.allocator(), &program, &terms, result)).?;
    program.solver_terms = terms.items;
    const definition = terms.items[definition_id.index()].operation.value_definition;
    const literal = terms.items[definition.expression.index()].operation.real_literal;
    try std.testing.expectEqualStrings("0", literal.numerator);
    try std.testing.expectEqualStrings("1", literal.denominator);
    try std.testing.expect(solver_value_definition.valid(&program, .{ .kind = .real }, definition));
}

test "finite binary number promotion preserves rounded results and rejects unsafe folds" {
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const result = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = left, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = right, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = result, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
    };
    var instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 0.1 } }, .results = &.{left}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .number = 0.2 } }, .results = &.{right}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .add, .left = left, .right = right } }, .results = &.{result}, .effects = .pure },
    };
    var program: ir.Program = .{
        .program_id = "finite-binary-number-promotion",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(arena.allocator());

    const definition_id = (try ensureDefinition(arena.allocator(), &program, &terms, result)).?;
    program.solver_terms = terms.items;
    const definition = terms.items[definition_id.index()].operation.value_definition;
    const literal_id = definition.expression;
    const literal = terms.items[literal_id.index()].operation.real_literal;
    const rounded_sum = @as(f64, 0.1) + @as(f64, 0.2);
    try std.testing.expect(numerals.rationalExactlyRepresentsF64(literal, rounded_sum));
    try std.testing.expect(!(std.mem.eql(u8, literal.numerator, "3") and std.mem.eql(u8, literal.denominator, "10")));
    try std.testing.expect(solver_value_definition.valid(&program, .{ .kind = .real }, definition));

    const tampered_terms = try std.testing.allocator.dupe(ir.SolverTerm, terms.items);
    defer std.testing.allocator.free(tampered_terms);
    tampered_terms[literal_id.index()].operation = .{ .real_literal = .{ .numerator = "3", .denominator = "10" } };
    var tampered = program;
    tampered.solver_terms = tampered_terms;
    try std.testing.expect(!solver_value_definition.valid(&tampered, .{ .kind = .real }, definition));

    terms.clearRetainingCapacity();
    program.solver_terms = &.{};
    instructions[2].effects = .dynamic_call;
    try std.testing.expect((try ensureDefinition(arena.allocator(), &program, &terms, result)) == null);

    terms.clearRetainingCapacity();
    instructions[0].operation.constant.number = @bitCast(@as(u64, 0x7fef_ffff_ffff_ffff));
    instructions[1].operation.constant.number = @bitCast(@as(u64, 0x7fef_ffff_ffff_ffff));
    instructions[2].effects = .pure;
    try std.testing.expect((try ensureDefinition(arena.allocator(), &program, &terms, result)) == null);
}

test "dynamic logical not promotion composes an explicit truthiness view" {
    const fixture = @import("fixtures.zig").dynamic_truthiness_module;
    var program = fixture.program;
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(std.testing.allocator);

    const truthy_not = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_truthy_not)).?;
    const falsy_not = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_falsy_not)).?;
    try std.testing.expectEqual(@as(usize, 8), terms.items.len);
    program.solver_terms = terms.items;

    const truthy_definition = terms.items[truthy_not.index()].operation.value_definition;
    const truthy_expression = terms.items[truthy_definition.expression.index()].operation.logical_not;
    const truthy_operand = terms.items[truthy_expression.index()].operation.dynamic_truthiness;
    try std.testing.expectEqual(fixture.v_truthy_condition, terms.items[truthy_operand.index()].operation.value);
    try std.testing.expectEqual(solver.Truth.false_value, solver.evaluateTruth(&program, truthy_not));

    const falsy_definition = terms.items[falsy_not.index()].operation.value_definition;
    const falsy_expression = terms.items[falsy_definition.expression.index()].operation.logical_not;
    const falsy_operand = terms.items[falsy_expression.index()].operation.dynamic_truthiness;
    try std.testing.expectEqual(fixture.v_falsy_condition, terms.items[falsy_operand.index()].operation.value);
    try std.testing.expectEqual(solver.Truth.true_value, solver.evaluateTruth(&program, falsy_not));

    const tampered_terms = try std.testing.allocator.dupe(ir.SolverTerm, terms.items);
    defer std.testing.allocator.free(tampered_terms);
    tampered_terms[truthy_expression.index()].operation = .{ .value = fixture.v_truthy_condition };
    var tampered = program;
    tampered.solver_terms = tampered_terms;
    try std.testing.expect(!solver_value_definition.valid(
        &tampered,
        tampered_terms[truthy_not.index()].sort,
        truthy_definition,
    ));

    var primitive_instructions = fixture.instructions;
    primitive_instructions[fixture.i_truthy_not.index()].operation.unary.mode = .primitive;
    var primitive = fixture.program;
    primitive.instructions = &primitive_instructions;
    var primitive_terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer primitive_terms.deinit(std.testing.allocator);
    const primitive_not = (try ensureDefinition(std.testing.allocator, &primitive, &primitive_terms, fixture.v_truthy_not)).?;
    primitive.solver_terms = primitive_terms.items;
    try std.testing.expectEqual(solver.Truth.false_value, solver.evaluateTruth(&primitive, primitive_not));
}

test "dynamic primitive equality promotion uses dynamic terms and rejects unsafe domains" {
    const fixture = @import("fixtures.zig").dynamic_truthiness_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_truthy_not.index()].operation = .{ .binary = .{
        .operator = .equal,
        .left = fixture.v_truthy_literal,
        .right = fixture.v_truthy_condition,
    } };
    var program = fixture.program;
    program.instructions = &instructions;
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(std.testing.allocator);

    const equal = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_truthy_not)).?;
    try std.testing.expectEqual(@as(usize, 2), terms.items.len);
    program.solver_terms = terms.items;
    const equal_definition = terms.items[equal.index()].operation.value_definition;
    try std.testing.expectEqual(true, terms.items[equal_definition.expression.index()].operation.boolean_literal);
    try std.testing.expectEqual(solver.Truth.true_value, solver.evaluateTruth(&program, equal));

    var table_values = fixture.values;
    table_values[fixture.v_truthy_literal.index()].type = .{ .kind = .table };
    table_values[fixture.v_truthy_condition.index()].type = .{ .kind = .table };
    var unsafe_definition = program;
    unsafe_definition.values = &table_values;
    try std.testing.expect(!solver_value_definition.valid(
        &unsafe_definition,
        terms.items[equal.index()].sort,
        equal_definition,
    ));

    terms.clearRetainingCapacity();
    instructions[fixture.i_truthy_not.index()].operation.binary.operator = .not_equal;
    program.solver_terms = &.{};
    const not_equal = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_truthy_not)).?;
    program.solver_terms = terms.items;
    try std.testing.expectEqual(solver.Truth.false_value, solver.evaluateTruth(&program, not_equal));

    terms.clearRetainingCapacity();
    instructions[fixture.i_truthy_condition.index()].operation = .{ .environment_get = .{
        .target = .{ .ambient = {} },
        .name = "unknown_value",
    } };
    instructions[fixture.i_truthy_condition.index()].effects = .semantic_environment_read;
    program.solver_terms = &.{};
    try std.testing.expectEqual(
        @as(?ir.SolverTermId, null),
        try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_truthy_not),
    );
    try std.testing.expectEqual(@as(usize, 0), terms.items.len);

    const references = @import("fixtures.zig").function_reference_module;
    try std.testing.expect(solver_equivalence.dynamicValuesHavePrimitiveEquality(
        &references.program,
        references.v_left_a,
        references.v_right,
    ));
    const fresh = @import("fixtures.zig").fresh_reference_module;
    try std.testing.expect(!solver_equivalence.dynamicValuesHavePrimitiveEquality(
        &fresh.program,
        fresh.v_table_a,
        fresh.v_table_b,
    ));
}

test "dynamic numeric equality is total over the NaN domain" {
    const fixture = @import("fixtures.zig").dynamic_truthiness_module;
    var values = fixture.values;
    values[fixture.v_truthy_condition.index()].type = .number;
    var instructions = fixture.instructions;
    instructions[fixture.i_truthy_condition.index()].operation = .{ .environment_get = .{
        .target = .{ .ambient = {} },
        .name = "unknown_number",
    } };
    instructions[fixture.i_truthy_condition.index()].effects = .semantic_environment_read;
    instructions[fixture.i_truthy_not.index()].operation = .{ .binary = .{
        .operator = .equal,
        .left = fixture.v_truthy_condition,
        .right = fixture.v_truthy_condition,
    } };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(std.testing.allocator);

    const total_equal = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_truthy_not)).?;
    program.solver_terms = terms.items;
    const total_definition = terms.items[total_equal.index()].operation.value_definition;
    try std.testing.expectEqual(@as(?ir.SolverTermId, null), total_definition.valid_when);
    const total_expression = terms.items[total_definition.expression.index()].operation.binary;
    try std.testing.expectEqual(ir.SolverBinaryOperator.logical_and, total_expression.operator);
    const nan_guard = terms.items[total_expression.left.index()].operation.binary;
    try std.testing.expectEqual(ir.SolverBinaryOperator.logical_and, nan_guard.operator);
    const raw_equality = terms.items[total_expression.right.index()].operation.binary;
    try std.testing.expectEqual(ir.SolverBinaryOperator.equal, raw_equality.operator);
    try std.testing.expect(solver_value_definition.valid(&program, terms.items[total_equal.index()].sort, total_definition));
    try std.testing.expect(solver_equivalence.dynamicValuesHavePrimitiveEquality(
        &program,
        fixture.v_truthy_condition,
        fixture.v_truthy_condition,
    ));
    try std.testing.expect(!solver_equivalence.dynamicValuesHaveUnguardedPrimitiveEquality(
        &program,
        fixture.v_truthy_condition,
        fixture.v_truthy_condition,
    ));
    const unguarded_query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = total_equal,
    };
    try std.testing.expectEqual(ir.SolverResolution.unknown, solver.solve(&program, unguarded_query));

    const tampered_terms = try std.testing.allocator.dupe(ir.SolverTerm, terms.items);
    defer std.testing.allocator.free(tampered_terms);
    tampered_terms[total_expression.left.index()].operation = .{ .boolean_literal = true };
    var tampered = program;
    tampered.solver_terms = tampered_terms;
    try std.testing.expect(!solver_value_definition.valid(
        &tampered,
        tampered_terms[total_equal.index()].sort,
        tampered_terms[total_equal.index()].operation.value_definition,
    ));

    const forged_terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_truthy_condition } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .value_definition = .{
            .value = fixture.v_truthy_not,
            .expression = ir.SolverTermId.fromIndex(1),
        } } },
    };
    program.solver_terms = &forged_terms;
    try std.testing.expect(!solver_value_definition.valid(
        &program,
        forged_terms[2].sort,
        forged_terms[2].operation.value_definition,
    ));

    terms.clearRetainingCapacity();
    instructions[fixture.i_truthy_condition.index()].operation = .{ .constant = .{ .number = 1.5 } };
    instructions[fixture.i_truthy_condition.index()].effects = .pure;
    program.solver_terms = &.{};
    const finite_equal = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_truthy_not)).?;
    program.solver_terms = terms.items;
    try std.testing.expectEqual(solver.Truth.true_value, solver.evaluateTruth(&program, finite_equal));

    terms.clearRetainingCapacity();
    instructions[fixture.i_truthy_condition.index()].operation = .{ .constant = .{ .number = std.math.nan(f64) } };
    program.solver_terms = &.{};
    const nan_equal = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_truthy_not)).?;
    program.solver_terms = terms.items;
    try std.testing.expectEqual(solver.Truth.false_value, solver.evaluateTruth(&program, nan_equal));

    terms.clearRetainingCapacity();
    instructions[fixture.i_truthy_not.index()].operation.binary.operator = .not_equal;
    program.solver_terms = &.{};
    const nan_not_equal = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_truthy_not)).?;
    program.solver_terms = terms.items;
    try std.testing.expectEqual(solver.Truth.true_value, solver.evaluateTruth(&program, nan_not_equal));

    terms.clearRetainingCapacity();
    instructions[fixture.i_truthy_condition.index()].operation = .{ .environment_get = .{
        .target = .{ .ambient = {} },
        .name = "unknown_number",
    } };
    instructions[fixture.i_truthy_condition.index()].effects = .semantic_environment_read;
    instructions[fixture.i_truthy_not.index()].operation.binary.operator = .equal;
    instructions[fixture.i_truthy_not.index()].operation.binary.right = fixture.v_truthy_literal;
    program.solver_terms = &.{};
    const cross_category = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_truthy_not)).?;
    program.solver_terms = terms.items;
    try std.testing.expectEqual(solver.Truth.false_value, solver.evaluateTruth(&program, cross_category));

    terms.clearRetainingCapacity();
    values[fixture.v_truthy_literal.index()].type = .number;
    instructions[fixture.i_truthy_literal.index()].operation = .{ .constant = .{ .special_number = .positive_infinity } };
    instructions[fixture.i_truthy_condition.index()].operation = .{ .constant = .{ .special_number = .positive_infinity } };
    instructions[fixture.i_truthy_condition.index()].effects = .pure;
    instructions[fixture.i_truthy_not.index()].operation.binary.left = fixture.v_truthy_literal;
    instructions[fixture.i_truthy_not.index()].operation.binary.right = fixture.v_truthy_condition;
    instructions[fixture.i_truthy_not.index()].operation.binary.operator = .equal;
    program.solver_terms = &.{};
    const infinity_equal = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_truthy_not)).?;
    program.solver_terms = terms.items;
    const infinity_definition = terms.items[infinity_equal.index()].operation.value_definition;
    try std.testing.expectEqual(@as(?ir.SolverTermId, null), infinity_definition.valid_when);
    try std.testing.expectEqual(true, terms.items[infinity_definition.expression.index()].operation.boolean_literal);
    try std.testing.expectEqual(solver.Truth.true_value, solver.evaluateTruth(&program, infinity_equal));

    terms.clearRetainingCapacity();
    instructions[fixture.i_truthy_condition.index()].operation.constant = .{ .special_number = .negative_infinity };
    instructions[fixture.i_truthy_not.index()].operation.binary.operator = .not_equal;
    program.solver_terms = &.{};
    const infinity_not_equal = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_truthy_not)).?;
    program.solver_terms = terms.items;
    try std.testing.expectEqual(solver.Truth.true_value, solver.evaluateTruth(&program, infinity_not_equal));
}

test "promotion canonicalizes exact u32 sources as literal definitions" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };
    const bv32 = unsignedBit32Sort();
    var values = fixture.values;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_factor.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation = .{ .constant = .{ .integer = "305419896" } };
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = "252645135" } };
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .bit_and,
        .left = fixture.v_sum,
        .right = fixture.v_factor,
        .mode = .primitive,
    } };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(allocator);

    const bit_and_definition_id = (try ensureDefinition(allocator, &program, &terms, fixture.v_result)).?;
    try std.testing.expectEqual(@as(usize, 2), terms.items.len);
    program.solver_terms = terms.items;
    const bit_and_definition = terms.items[bit_and_definition_id.index()].operation.value_definition;
    try std.testing.expectEqual(@as(?ir.SolverTermId, null), bit_and_definition.valid_when);
    const bit_and_literal = terms.items[bit_and_definition.expression.index()].operation.bit_vector_literal;
    try std.testing.expectEqual(@as(u16, 32), bit_and_literal.bit_width);
    try std.testing.expectEqualStrings("33818120", bit_and_literal.value);
    try std.testing.expect(solver_value_definition.valid(&program, bv32, bit_and_definition));

    terms.clearRetainingCapacity();
    program.solver_terms = &.{};
    const constant_definition_id = (try ensureDefinition(allocator, &program, &terms, fixture.v_sum)).?;
    try std.testing.expectEqual(@as(usize, 2), terms.items.len);
    const constant_definition = terms.items[constant_definition_id.index()].operation.value_definition;
    try std.testing.expectEqualStrings(
        "305419896",
        terms.items[constant_definition.expression.index()].operation.bit_vector_literal.value,
    );

    terms.clearRetainingCapacity();
    instructions[fixture.i_result.index()].operation = .{ .copy = fixture.v_sum };
    program.solver_terms = &.{};
    const copy_definition_id = (try ensureDefinition(allocator, &program, &terms, fixture.v_result)).?;
    try std.testing.expectEqual(@as(usize, 2), terms.items.len);
    const copy_definition = terms.items[copy_definition_id.index()].operation.value_definition;
    try std.testing.expectEqualStrings(
        "305419896",
        terms.items[copy_definition.expression.index()].operation.bit_vector_literal.value,
    );

    terms.clearRetainingCapacity();
    instructions[fixture.i_factor.index()].operation.constant.integer = "32";
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .shift_left,
        .left = fixture.v_sum,
        .right = fixture.v_factor,
        .mode = .primitive,
        .shift_behavior = .luau_bit32,
    } };
    program.solver_terms = &.{};
    const guarded_definition_id = (try ensureDefinition(allocator, &program, &terms, fixture.v_result)).?;
    const guarded_definition = terms.items[guarded_definition_id.index()].operation.value_definition;
    try std.testing.expect(guarded_definition.valid_when != null);
    try std.testing.expect(terms.items[guarded_definition.expression.index()].operation == .binary);
}

test "promotion reuses an admitted guard for a variable u32 shift" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };
    var values = fixture.values;
    values[fixture.v_right.index()].type = u32_type;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_factor.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .shift_left,
        .left = fixture.v_sum,
        .right = fixture.v_right,
        .mode = .primitive,
        .shift_behavior = .luau_bit32,
    } };
    const bv32 = unsignedBit32Sort();
    const initial_terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv32, .operation = .{ .value = fixture.v_right } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv32, .operation = .{ .bit_vector_literal = .{ .value = "31", .bit_width = 32 } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .less_equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &initial_terms;
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(std.testing.allocator);
    try terms.appendSlice(std.testing.allocator, &initial_terms);

    const result = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_result)).?;
    try std.testing.expectEqual(@as(usize, 6), terms.items.len);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(2), terms.items[result.index()].operation.value_definition.valid_when.?);
    for (terms.items[initial_terms.len..]) |term| switch (term.operation) {
        .bit_vector_literal => |literal| try std.testing.expect(!std.mem.eql(u8, literal.value, "32")),
        else => {},
    };

    program.solver_terms = terms.items;
    try std.testing.expect(solver_value_definition.valid(&program, bv32, terms.items[result.index()].operation.value_definition));

    terms.clearRetainingCapacity();
    instructions[fixture.i_result.index()].operation.binary.shift_behavior = .zero_saturating;
    program.solver_terms = &.{};
    const total_result = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_result)).?;
    const total_definition = terms.items[total_result.index()].operation.value_definition;
    try std.testing.expectEqual(@as(?ir.SolverTermId, null), total_definition.valid_when);
    try std.testing.expectEqual(ir.SolverBinaryOperator.shift_left, terms.items[total_definition.expression.index()].operation.binary.operator);
    for (terms.items) |term| switch (term.operation) {
        .bit_vector_literal => |literal| try std.testing.expect(!std.mem.eql(u8, literal.value, "31") and !std.mem.eql(u8, literal.value, "32")),
        else => {},
    };
    program.solver_terms = terms.items;
    try std.testing.expect(solver_value_definition.valid(&program, bv32, total_definition));
}

test "partial integer promotion reuses nonzero guards without proving them" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const integer: ir.SolverSort = .{ .kind = .integer };
    for ([_]ir.BinaryOperator{ .floor_divide, .modulo }) |operator| {
        var instructions = fixture.instructions;
        instructions[fixture.i_result.index()].operation = .{ .binary = .{
            .operator = operator,
            .left = fixture.v_sum,
            .right = fixture.v_right,
        } };
        instructions[fixture.i_result.index()].effects.may_throw = true;
        const initial_terms = [_]ir.SolverTerm{
            .{ .id = ir.SolverTermId.fromIndex(0), .sort = integer, .operation = .{ .value = fixture.v_right } },
            .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(0) } },
        };
        var program = fixture.program;
        program.instructions = &instructions;
        program.solver_terms = &initial_terms;
        var terms: std.ArrayList(ir.SolverTerm) = .empty;
        defer terms.deinit(std.testing.allocator);
        try terms.appendSlice(std.testing.allocator, &initial_terms);

        const result = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_result)).?;
        const definition = terms.items[result.index()].operation.value_definition;
        const expression = terms.items[definition.expression.index()];
        const defined_by = switch (expression.operation) {
            .division => |division| division.defined_by,
            .remainder => |remainder| remainder.defined_by,
            else => return error.TestExpectedPartialIntegerExpression,
        };
        try std.testing.expectEqual(ir.SolverTermId.fromIndex(1), defined_by);
        program.solver_terms = terms.items;
        try std.testing.expect(!solver_preconditions.termPreconditionsProved(&program, result, solver.evaluatesTrue));

        const equality = ir.SolverTermId.fromIndex(terms.items.len);
        try terms.append(std.testing.allocator, .{
            .id = equality,
            .sort = .{ .kind = .boolean },
            .operation = .{ .binary = .{ .operator = .equal, .left = result, .right = result } },
        });
        const constraints = [_]ir.Constraint{.{
            .id = ir.ConstraintId.fromIndex(0),
            .predicate = defined_by,
            .evidence = &.{fixture.proof},
            .scope = .{ .function = fixture.f_add },
        }};
        program.solver_terms = terms.items;
        program.constraints = &constraints;
        var query: ir.SolverQuery = .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .goal = equality,
        };
        try std.testing.expect(!solver_preconditions.queryCovered(&program, query, solver.evaluatesTrue));
        query.assumptions = &.{ir.ConstraintId.fromIndex(0)};
        try std.testing.expect(solver_preconditions.queryCovered(&program, query, solver.evaluatesTrue));
        try std.testing.expectEqual(ir.SolverResolution.proved, solver.solve(&program, query));
    }
}

test "partial promotion adopts the divisor term owned by an admitted guard" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const integer: ir.SolverSort = .{ .kind = .integer };
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .modulo,
        .left = fixture.v_sum,
        .right = fixture.v_factor,
    } };
    instructions[fixture.i_result.index()].effects.may_throw = true;
    const initial_terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = integer, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(0) } },
    };
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &initial_terms;
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(std.testing.allocator);
    try terms.appendSlice(std.testing.allocator, &initial_terms);

    const result = (try ensureDefinition(std.testing.allocator, &program, &terms, fixture.v_result)).?;
    const definition = terms.items[result.index()].operation.value_definition;
    const remainder = terms.items[definition.expression.index()].operation.remainder;
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(0), remainder.right);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(1), remainder.defined_by);
}
