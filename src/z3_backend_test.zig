const std = @import("std");
const lifter = @import("semantic_lifter");
const ir = lifter.ir;
const defaultBackend = lifter.z3_backend.defaultBackend;
const version = lifter.z3_backend.version;

test {
    _ = @import("z3_dynamic_category_test.zig");
    _ = @import("z3_dynamic_identity_test.zig");
    _ = @import("z3_dynamic_promotion_test.zig");
    _ = @import("z3_dynamic_truthiness_test.zig");
    _ = @import("z3_real_model_test.zig");
}

test "linked Z3 backend proves an integer identity" {
    try std.testing.expect(std.mem.indexOf(u8, version(), "Z3 4.16.0") != null);
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "9" } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "4" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .integer }, .operation = .{ .binary = .{ .operator = .subtract, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "5" } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(2), .right = ir.SolverTermId.fromIndex(3) } } },
    };
    const program: ir.Program = .{ .program_id = "z3-integer-identity", .entry_function = ir.FunctionId.fromIndex(0), .functions = &.{}, .blocks = &.{}, .instructions = &.{}, .values = &.{}, .solver_terms = &terms };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(4) };
    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverEngine.z3, result.engine);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
}

test "Z3 and internal facts agree on every query-kind polarity" {
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = false } },
    };
    const program: ir.Program = .{
        .program_id = "query-kind-polarity",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &terms,
    };
    const cases = [_]struct {
        kind: ir.QueryKind,
        goal: ir.SolverTermId,
        expected: ir.SolverResolution,
    }{
        .{ .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(0), .expected = .proved },
        .{ .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(1), .expected = .disproved },
        .{ .kind = .prove_false, .goal = ir.SolverTermId.fromIndex(1), .expected = .proved },
        .{ .kind = .prove_false, .goal = ir.SolverTermId.fromIndex(0), .expected = .disproved },
        .{ .kind = .prove_equivalent, .goal = ir.SolverTermId.fromIndex(0), .expected = .proved },
        .{ .kind = .prove_equivalent, .goal = ir.SolverTermId.fromIndex(1), .expected = .disproved },
        .{ .kind = .prove_unreachable, .goal = ir.SolverTermId.fromIndex(1), .expected = .proved },
        .{ .kind = .prove_unreachable, .goal = ir.SolverTermId.fromIndex(0), .expected = .disproved },
        .{ .kind = .find_model, .goal = ir.SolverTermId.fromIndex(0), .expected = .proved },
        .{ .kind = .find_model, .goal = ir.SolverTermId.fromIndex(1), .expected = .disproved },
    };

    for (cases) |case| {
        const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = case.kind, .goal = case.goal };
        try std.testing.expectEqual(case.expected, lifter.solver.solve(&program, query));
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(case.expected, result.resolution);
    }
}

const BinaryDifferentialCase = struct {
    operator: ir.SolverBinaryOperator,
    sort: ir.SolverSort,
    left: []const u8,
    right: []const u8,
    expected: []const u8,
};

fn literalTerm(id: usize, sort: ir.SolverSort, value: []const u8) ir.SolverTerm {
    const operation: ir.SolverTermOperation = switch (sort.kind) {
        .boolean => .{ .boolean_literal = std.mem.eql(u8, value, "true") },
        .integer => .{ .integer_literal = value },
        .bit_vector => .{ .bit_vector_literal = .{ .value = value, .bit_width = sort.bit_width } },
        .real, .dynamic_value => unreachable,
    };
    return .{ .id = ir.SolverTermId.fromIndex(id), .sort = sort, .operation = operation };
}

fn binaryResultSort(operator: ir.SolverBinaryOperator, operand_sort: ir.SolverSort) ir.SolverSort {
    return switch (operator) {
        .equal, .not_equal, .less, .less_equal, .greater, .greater_equal, .logical_and, .logical_or => .{ .kind = .boolean },
        .add, .subtract, .multiply, .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => operand_sort,
    };
}

test "Z3 and internal facts agree across bounded binary semantics" {
    const boolean: ir.SolverSort = .{ .kind = .boolean };
    const integer: ir.SolverSort = .{ .kind = .integer };
    const unsigned_bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8 };
    const signed_bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8, .signed = true };
    const unsigned_bv64: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 64 };
    const cases = [_]BinaryDifferentialCase{
        .{ .operator = .equal, .sort = boolean, .left = "true", .right = "true", .expected = "true" },
        .{ .operator = .not_equal, .sort = integer, .left = "7", .right = "-7", .expected = "true" },
        .{ .operator = .less, .sort = integer, .left = "-2", .right = "1", .expected = "true" },
        .{ .operator = .less_equal, .sort = integer, .left = "1", .right = "1", .expected = "true" },
        .{ .operator = .greater, .sort = integer, .left = "2", .right = "1", .expected = "true" },
        .{ .operator = .greater_equal, .sort = integer, .left = "1", .right = "1", .expected = "true" },
        .{ .operator = .logical_and, .sort = boolean, .left = "true", .right = "false", .expected = "false" },
        .{ .operator = .logical_or, .sort = boolean, .left = "false", .right = "true", .expected = "true" },
        .{ .operator = .add, .sort = integer, .left = "-7", .right = "3", .expected = "-4" },
        .{ .operator = .subtract, .sort = integer, .left = "3", .right = "7", .expected = "-4" },
        .{ .operator = .multiply, .sort = integer, .left = "-3", .right = "4", .expected = "-12" },
        .{ .operator = .add, .sort = unsigned_bv8, .left = "255", .right = "1", .expected = "0" },
        .{ .operator = .subtract, .sort = unsigned_bv8, .left = "0", .right = "1", .expected = "255" },
        .{ .operator = .multiply, .sort = unsigned_bv8, .left = "20", .right = "20", .expected = "144" },
        .{ .operator = .add, .sort = unsigned_bv64, .left = "18446744073709551615", .right = "1", .expected = "0" },
        .{ .operator = .bit_and, .sort = unsigned_bv8, .left = "170", .right = "204", .expected = "136" },
        .{ .operator = .bit_or, .sort = unsigned_bv8, .left = "170", .right = "204", .expected = "238" },
        .{ .operator = .bit_xor, .sort = unsigned_bv8, .left = "170", .right = "204", .expected = "102" },
        .{ .operator = .shift_left, .sort = unsigned_bv8, .left = "129", .right = "1", .expected = "2" },
        .{ .operator = .shift_left, .sort = unsigned_bv8, .left = "129", .right = "8", .expected = "0" },
        .{ .operator = .shift_right, .sort = unsigned_bv8, .left = "128", .right = "1", .expected = "64" },
        .{ .operator = .shift_right, .sort = signed_bv8, .left = "128", .right = "1", .expected = "192" },
        .{ .operator = .less, .sort = unsigned_bv8, .left = "128", .right = "1", .expected = "false" },
        .{ .operator = .less, .sort = signed_bv8, .left = "128", .right = "1", .expected = "true" },
        .{ .operator = .less_equal, .sort = unsigned_bv8, .left = "128", .right = "1", .expected = "false" },
        .{ .operator = .less_equal, .sort = signed_bv8, .left = "128", .right = "1", .expected = "true" },
        .{ .operator = .greater, .sort = unsigned_bv8, .left = "1", .right = "128", .expected = "false" },
        .{ .operator = .greater, .sort = signed_bv8, .left = "1", .right = "128", .expected = "true" },
        .{ .operator = .greater_equal, .sort = unsigned_bv8, .left = "1", .right = "128", .expected = "false" },
        .{ .operator = .greater_equal, .sort = signed_bv8, .left = "1", .right = "128", .expected = "true" },
    };

    for (cases) |case| {
        const result_sort = binaryResultSort(case.operator, case.sort);
        const terms = [_]ir.SolverTerm{
            literalTerm(0, case.sort, case.left),
            literalTerm(1, case.sort, case.right),
            .{ .id = ir.SolverTermId.fromIndex(2), .sort = result_sort, .operation = .{ .binary = .{
                .operator = case.operator,
                .left = ir.SolverTermId.fromIndex(0),
                .right = ir.SolverTermId.fromIndex(1),
            } } },
            literalTerm(3, result_sort, case.expected),
            .{ .id = ir.SolverTermId.fromIndex(4), .sort = boolean, .operation = .{ .binary = .{
                .operator = .equal,
                .left = ir.SolverTermId.fromIndex(2),
                .right = ir.SolverTermId.fromIndex(3),
            } } },
        };
        const program: ir.Program = .{
            .program_id = "bounded-binary-differential",
            .entry_function = ir.FunctionId.fromIndex(0),
            .functions = &.{},
            .blocks = &.{},
            .instructions = &.{},
            .values = &.{},
            .solver_terms = &terms,
        };
        const query: ir.SolverQuery = .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .goal = ir.SolverTermId.fromIndex(4),
        };

        const internal = lifter.solver.solve(&program, query);
        try std.testing.expectEqual(ir.SolverResolution.proved, internal);
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(internal, result.resolution);
    }
}

const StructuralDifferentialKind = enum {
    logical_not,
    if_then_else,
    bit_vector_not,
    bit_vector_extract,
    bit_vector_concat,
    zero_extend,
    sign_extend,
    rotate_left,
    rotate_right,
    integer_to_bit_vector,
    bit_vector_to_signed_integer,
    bit_vector_to_unsigned_integer,
    arithmetic_negate,
    is_nonzero,
};

const StructuralDifferentialCase = struct {
    kind: StructuralDifferentialKind,
    left_sort: ir.SolverSort,
    left: []const u8,
    right_sort: ir.SolverSort = .{ .kind = .integer },
    right: []const u8 = "0",
    auxiliary_sort: ir.SolverSort = .{ .kind = .integer },
    auxiliary: []const u8 = "0",
    result_sort: ir.SolverSort,
    expected: []const u8,
    high: u16 = 0,
    low: u16 = 0,
    extra_bits: u16 = 0,
};

fn structuralOperation(case: StructuralDifferentialCase) ir.SolverTermOperation {
    const left = ir.SolverTermId.fromIndex(0);
    const right = ir.SolverTermId.fromIndex(1);
    const auxiliary = ir.SolverTermId.fromIndex(2);
    return switch (case.kind) {
        .logical_not => .{ .logical_not = left },
        .if_then_else => .{ .if_then_else = .{
            .condition = left,
            .then_term = right,
            .else_term = auxiliary,
        } },
        .bit_vector_not => .{ .bit_vector_not = left },
        .bit_vector_extract => .{ .bit_vector_extract = .{
            .operand = left,
            .high = case.high,
            .low = case.low,
        } },
        .bit_vector_concat => .{ .bit_vector_concat = .{ .high = left, .low = right } },
        .zero_extend => .{ .bit_vector_extend = .{
            .operand = left,
            .extra_bits = case.extra_bits,
            .mode = .zero,
        } },
        .sign_extend => .{ .bit_vector_extend = .{
            .operand = left,
            .extra_bits = case.extra_bits,
            .mode = .sign,
        } },
        .rotate_left => .{ .bit_vector_rotate = .{ .operand = left, .amount = right, .direction = .left } },
        .rotate_right => .{ .bit_vector_rotate = .{ .operand = left, .amount = right, .direction = .right } },
        .integer_to_bit_vector => .{ .integer_to_bit_vector = left },
        .bit_vector_to_signed_integer => .{ .bit_vector_to_integer = .{ .operand = left, .signed = true } },
        .bit_vector_to_unsigned_integer => .{ .bit_vector_to_integer = .{ .operand = left, .signed = false } },
        .arithmetic_negate => .{ .arithmetic_negate = left },
        .is_nonzero => .{ .is_nonzero = left },
    };
}

test "Z3 and internal facts agree across bounded structural semantics" {
    const boolean: ir.SolverSort = .{ .kind = .boolean };
    const integer: ir.SolverSort = .{ .kind = .integer };
    const bv4: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 4 };
    const bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8 };
    const bv64: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 64 };
    const cases = [_]StructuralDifferentialCase{
        .{ .kind = .logical_not, .left_sort = boolean, .left = "false", .result_sort = boolean, .expected = "true" },
        .{
            .kind = .if_then_else,
            .left_sort = boolean,
            .left = "true",
            .right_sort = integer,
            .right = "7",
            .auxiliary_sort = integer,
            .auxiliary = "9",
            .result_sort = integer,
            .expected = "7",
        },
        .{ .kind = .bit_vector_not, .left_sort = bv8, .left = "165", .result_sort = bv8, .expected = "90" },
        .{
            .kind = .bit_vector_extract,
            .left_sort = bv8,
            .left = "165",
            .result_sort = bv4,
            .expected = "9",
            .high = 5,
            .low = 2,
        },
        .{
            .kind = .bit_vector_concat,
            .left_sort = bv4,
            .left = "9",
            .right_sort = bv4,
            .right = "3",
            .result_sort = bv8,
            .expected = "147",
        },
        .{ .kind = .zero_extend, .left_sort = bv4, .left = "9", .result_sort = bv8, .expected = "9", .extra_bits = 4 },
        .{ .kind = .sign_extend, .left_sort = bv4, .left = "9", .result_sort = bv8, .expected = "249", .extra_bits = 4 },
        .{ .kind = .rotate_left, .left_sort = bv8, .left = "165", .right_sort = bv8, .right = "1", .result_sort = bv8, .expected = "75" },
        .{ .kind = .rotate_right, .left_sort = bv8, .left = "165", .right_sort = bv8, .right = "1", .result_sort = bv8, .expected = "210" },
        .{ .kind = .integer_to_bit_vector, .left_sort = integer, .left = "-1", .result_sort = bv8, .expected = "255" },
        .{ .kind = .integer_to_bit_vector, .left_sort = integer, .left = "-1", .result_sort = bv64, .expected = "18446744073709551615" },
        .{ .kind = .bit_vector_to_signed_integer, .left_sort = bv8, .left = "255", .result_sort = integer, .expected = "-1" },
        .{ .kind = .bit_vector_to_signed_integer, .left_sort = bv64, .left = "18446744073709551615", .result_sort = integer, .expected = "-1" },
        .{ .kind = .bit_vector_to_unsigned_integer, .left_sort = bv8, .left = "255", .result_sort = integer, .expected = "255" },
        .{ .kind = .arithmetic_negate, .left_sort = integer, .left = "7", .result_sort = integer, .expected = "-7" },
        .{ .kind = .arithmetic_negate, .left_sort = bv8, .left = "165", .result_sort = bv8, .expected = "91" },
        .{ .kind = .is_nonzero, .left_sort = integer, .left = "-1", .result_sort = boolean, .expected = "true" },
        .{ .kind = .is_nonzero, .left_sort = bv8, .left = "0", .result_sort = boolean, .expected = "false" },
    };

    for (cases) |case| {
        const terms = [_]ir.SolverTerm{
            literalTerm(0, case.left_sort, case.left),
            literalTerm(1, case.right_sort, case.right),
            literalTerm(2, case.auxiliary_sort, case.auxiliary),
            .{ .id = ir.SolverTermId.fromIndex(3), .sort = case.result_sort, .operation = structuralOperation(case) },
            literalTerm(4, case.result_sort, case.expected),
            .{ .id = ir.SolverTermId.fromIndex(5), .sort = boolean, .operation = .{ .binary = .{
                .operator = .equal,
                .left = ir.SolverTermId.fromIndex(3),
                .right = ir.SolverTermId.fromIndex(4),
            } } },
        };
        const program: ir.Program = .{
            .program_id = "bounded-structural-differential",
            .entry_function = ir.FunctionId.fromIndex(0),
            .functions = &.{},
            .blocks = &.{},
            .instructions = &.{},
            .values = &.{},
            .solver_terms = &terms,
        };
        const query: ir.SolverQuery = .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .goal = ir.SolverTermId.fromIndex(5),
        };

        const internal = lifter.solver.solve(&program, query);
        try std.testing.expectEqual(ir.SolverResolution.proved, internal);
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(internal, result.resolution);
    }
}

test "Z3 lowers solver-neutral conditional selection" {
    const condition_value = ir.ValueId.fromIndex(0);
    const then_value = ir.ValueId.fromIndex(1);
    const else_value = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = condition_value, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = then_value, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = else_value, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .parameter = 2 } },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .value = condition_value } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .value = then_value } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .integer }, .operation = .{ .value = else_value } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .integer }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(0),
            .then_term = ir.SolverTermId.fromIndex(1),
            .else_term = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(3),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
    }};
    const program: ir.Program = .{
        .program_id = "z3-if-then-else",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
        .constraints = &constraints,
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(4),
    };

    try std.testing.expectEqual(ir.SolverResolution.unknown, lifter.solver.solve(&program, query));
    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqualSlices(ir.ConstraintId, &.{ir.ConstraintId.fromIndex(0)}, result.unsat_core.items);
}

test "Z3 reconstructs arbitrary-width bit-vector structure" {
    const bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8 };
    const bv16: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 16 };
    const bv64: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 64 };
    const bv128: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 128 };
    const boolean: ir.SolverSort = .{ .kind = .boolean };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv128, .operation = .{ .bit_vector_literal = .{
            .value = "340282366920938463463374607431768211455",
            .bit_width = 128,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv64, .operation = .{ .bit_vector_extract = .{
            .operand = ir.SolverTermId.fromIndex(0),
            .high = 127,
            .low = 64,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = bv64, .operation = .{ .bit_vector_extract = .{
            .operand = ir.SolverTermId.fromIndex(0),
            .high = 63,
            .low = 0,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = bv128, .operation = .{ .bit_vector_concat = .{
            .high = ir.SolverTermId.fromIndex(1),
            .low = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = bv128, .operation = .{ .bit_vector_not = ir.SolverTermId.fromIndex(3) } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = bv128, .operation = .{ .bit_vector_literal = .{ .value = "0", .bit_width = 128 } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(4),
            .right = ir.SolverTermId.fromIndex(5),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = bv8, .operation = .{ .bit_vector_literal = .{ .value = "128", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = bv16, .operation = .{ .bit_vector_extend = .{
            .operand = ir.SolverTermId.fromIndex(7),
            .extra_bits = 8,
            .mode = .sign,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = bv16, .operation = .{ .bit_vector_literal = .{ .value = "65408", .bit_width = 16 } } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(8),
            .right = ir.SolverTermId.fromIndex(9),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(11), .sort = bv16, .operation = .{ .bit_vector_extend = .{
            .operand = ir.SolverTermId.fromIndex(7),
            .extra_bits = 8,
            .mode = .zero,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(12), .sort = bv16, .operation = .{ .bit_vector_literal = .{ .value = "128", .bit_width = 16 } } },
        .{ .id = ir.SolverTermId.fromIndex(13), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(11),
            .right = ir.SolverTermId.fromIndex(12),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(14), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(6),
            .right = ir.SolverTermId.fromIndex(10),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(15), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(14),
            .right = ir.SolverTermId.fromIndex(13),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(16), .sort = bv128, .operation = .{ .bit_vector_literal = .{ .value = "1", .bit_width = 128 } } },
        .{ .id = ir.SolverTermId.fromIndex(17), .sort = bv128, .operation = .{ .bit_vector_literal = .{ .value = "64", .bit_width = 128 } } },
        .{ .id = ir.SolverTermId.fromIndex(18), .sort = bv128, .operation = .{ .bit_vector_rotate = .{
            .operand = ir.SolverTermId.fromIndex(16),
            .amount = ir.SolverTermId.fromIndex(17),
            .direction = .left,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(19), .sort = bv128, .operation = .{ .bit_vector_literal = .{
            .value = "18446744073709551616",
            .bit_width = 128,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(20), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(18),
            .right = ir.SolverTermId.fromIndex(19),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(21), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(15),
            .right = ir.SolverTermId.fromIndex(20),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(22), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "-1" } },
        .{ .id = ir.SolverTermId.fromIndex(23), .sort = bv128, .operation = .{ .integer_to_bit_vector = ir.SolverTermId.fromIndex(22) } },
        .{ .id = ir.SolverTermId.fromIndex(24), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(23),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(25), .sort = .{ .kind = .integer }, .operation = .{ .bit_vector_to_integer = .{
            .operand = ir.SolverTermId.fromIndex(23),
            .signed = true,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(26), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(25),
            .right = ir.SolverTermId.fromIndex(22),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(27), .sort = .{ .kind = .integer }, .operation = .{ .bit_vector_to_integer = .{
            .operand = ir.SolverTermId.fromIndex(23),
            .signed = false,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(28), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "340282366920938463463374607431768211455" } },
        .{ .id = ir.SolverTermId.fromIndex(29), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(27),
            .right = ir.SolverTermId.fromIndex(28),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(30), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(24),
            .right = ir.SolverTermId.fromIndex(26),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(31), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(30),
            .right = ir.SolverTermId.fromIndex(29),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(32), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(21),
            .right = ir.SolverTermId.fromIndex(31),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(33), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "5" } },
        .{ .id = ir.SolverTermId.fromIndex(34), .sort = .{ .kind = .integer }, .operation = .{ .arithmetic_negate = ir.SolverTermId.fromIndex(33) } },
        .{ .id = ir.SolverTermId.fromIndex(35), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "-5" } },
        .{ .id = ir.SolverTermId.fromIndex(36), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(34),
            .right = ir.SolverTermId.fromIndex(35),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(37), .sort = bv128, .operation = .{ .arithmetic_negate = ir.SolverTermId.fromIndex(16) } },
        .{ .id = ir.SolverTermId.fromIndex(38), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(37),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(39), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(36),
            .right = ir.SolverTermId.fromIndex(38),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(40), .sort = .{ .kind = .real }, .operation = .{ .real_literal = .{
            .numerator = "3",
            .denominator = "2",
        } } },
        .{ .id = ir.SolverTermId.fromIndex(41), .sort = .{ .kind = .real }, .operation = .{ .arithmetic_negate = ir.SolverTermId.fromIndex(40) } },
        .{ .id = ir.SolverTermId.fromIndex(42), .sort = .{ .kind = .real }, .operation = .{ .real_literal = .{
            .numerator = "-3",
            .denominator = "2",
        } } },
        .{ .id = ir.SolverTermId.fromIndex(43), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(41),
            .right = ir.SolverTermId.fromIndex(42),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(44), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(39),
            .right = ir.SolverTermId.fromIndex(43),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(45), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(32),
            .right = ir.SolverTermId.fromIndex(44),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "z3-bit-vector-structure",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(45),
    };

    try std.testing.expectEqual(ir.SolverResolution.unknown, lifter.solver.solve(&program, query));
    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
}

test "Z3 and internal facts agree on signed and oversized bit-vector shifts" {
    const boolean: ir.SolverSort = .{ .kind = .boolean };
    const unsigned_bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8 };
    const signed_bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8, .signed = true };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = unsigned_bv8, .operation = .{ .bit_vector_literal = .{ .value = "128", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = unsigned_bv8, .operation = .{ .bit_vector_literal = .{ .value = "1", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = unsigned_bv8, .operation = .{ .binary = .{
            .operator = .shift_right,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = unsigned_bv8, .operation = .{ .bit_vector_literal = .{ .value = "64", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(2),
            .right = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "128", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "1", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = signed_bv8, .operation = .{ .binary = .{
            .operator = .shift_right,
            .left = ir.SolverTermId.fromIndex(5),
            .right = ir.SolverTermId.fromIndex(6),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "192", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(7),
            .right = ir.SolverTermId.fromIndex(8),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = unsigned_bv8, .operation = .{ .bit_vector_literal = .{ .value = "8", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(11), .sort = unsigned_bv8, .operation = .{ .binary = .{
            .operator = .shift_right,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(10),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(12), .sort = unsigned_bv8, .operation = .{ .bit_vector_literal = .{ .value = "0", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(13), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(11),
            .right = ir.SolverTermId.fromIndex(12),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(14), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "8", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(15), .sort = signed_bv8, .operation = .{ .binary = .{
            .operator = .shift_right,
            .left = ir.SolverTermId.fromIndex(5),
            .right = ir.SolverTermId.fromIndex(14),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(16), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "255", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(17), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(15),
            .right = ir.SolverTermId.fromIndex(16),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(18), .sort = boolean, .operation = .{ .binary = .{
            .operator = .less,
            .left = ir.SolverTermId.fromIndex(5),
            .right = ir.SolverTermId.fromIndex(6),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(19), .sort = boolean, .operation = .{ .binary = .{
            .operator = .less,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(20), .sort = boolean, .operation = .{ .logical_not = ir.SolverTermId.fromIndex(19) } },
        .{ .id = ir.SolverTermId.fromIndex(21), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(4),
            .right = ir.SolverTermId.fromIndex(9),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(22), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(13),
            .right = ir.SolverTermId.fromIndex(17),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(23), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(18),
            .right = ir.SolverTermId.fromIndex(20),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(24), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(21),
            .right = ir.SolverTermId.fromIndex(22),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(25), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(24),
            .right = ir.SolverTermId.fromIndex(23),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "z3-signed-bit-vector-operations",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(25),
    };

    try std.testing.expectEqual(ir.SolverResolution.proved, lifter.solver.solve(&program, query));
    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
}

test "Z3 consumes an admitted partial source value definition" {
    const fixture = lifter.fixtures.arithmetic_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation = .{ .constant = .{ .integer = "7" } };
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .modulo,
        .left = fixture.v_sum,
        .right = fixture.v_factor,
    } };
    const integer: ir.SolverSort = .{ .kind = .integer };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = integer, .operation = .{ .value = fixture.v_sum } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = integer, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(1) } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = integer, .operation = .{ .remainder = .{
            .mode = .integer_floor,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
            .defined_by = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = integer, .operation = .{ .value_definition = .{
            .value = fixture.v_result,
            .expression = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = integer, .operation = .{ .integer_literal = "1" } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(4),
            .right = ir.SolverTermId.fromIndex(5),
        } } },
    };
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(2),
        .evidence = &.{fixture.proof},
    }};
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(6),
    };

    var report = try lifter.validate.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
    try std.testing.expectEqual(ir.SolverResolution.proved, lifter.solver.solve(&program, query));
    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
}
