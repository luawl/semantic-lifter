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

test "Z3 lowers guarded explicit division modes" {
    const boolean: ir.SolverSort = .{ .kind = .boolean };
    const integer: ir.SolverSort = .{ .kind = .integer };
    const real: ir.SolverSort = .{ .kind = .real };
    const unsigned_bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8 };
    const signed_bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8, .signed = true };
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = integer, .operation = .{ .integer_literal = "-5" } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = integer, .operation = .{ .integer_literal = "2" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = boolean, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(1) } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = integer, .operation = .{ .division = .{
            .mode = .integer_euclidean,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
            .defined_by = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = integer, .operation = .{ .integer_literal = "-3" } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(3),
            .right = ir.SolverTermId.fromIndex(4),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = real, .operation = .{ .real_literal = .{ .numerator = "3", .denominator = "2" } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = real, .operation = .{ .real_literal = .{ .numerator = "3", .denominator = "4" } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = boolean, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(7) } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = real, .operation = .{ .division = .{
            .mode = .real,
            .left = ir.SolverTermId.fromIndex(6),
            .right = ir.SolverTermId.fromIndex(7),
            .defined_by = ir.SolverTermId.fromIndex(8),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = real, .operation = .{ .real_literal = .{ .numerator = "2", .denominator = "1" } } },
        .{ .id = ir.SolverTermId.fromIndex(11), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(9),
            .right = ir.SolverTermId.fromIndex(10),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(12), .sort = unsigned_bv8, .operation = .{ .bit_vector_literal = .{ .value = "255", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(13), .sort = unsigned_bv8, .operation = .{ .bit_vector_literal = .{ .value = "2", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(14), .sort = boolean, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(13) } },
        .{ .id = ir.SolverTermId.fromIndex(15), .sort = unsigned_bv8, .operation = .{ .division = .{
            .mode = .bit_vector_unsigned,
            .left = ir.SolverTermId.fromIndex(12),
            .right = ir.SolverTermId.fromIndex(13),
            .defined_by = ir.SolverTermId.fromIndex(14),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(16), .sort = unsigned_bv8, .operation = .{ .bit_vector_literal = .{ .value = "127", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(17), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(15),
            .right = ir.SolverTermId.fromIndex(16),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(18), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "251", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(19), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "2", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(20), .sort = boolean, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(19) } },
        .{ .id = ir.SolverTermId.fromIndex(21), .sort = signed_bv8, .operation = .{ .division = .{
            .mode = .bit_vector_signed,
            .left = ir.SolverTermId.fromIndex(18),
            .right = ir.SolverTermId.fromIndex(19),
            .defined_by = ir.SolverTermId.fromIndex(20),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(22), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "254", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(23), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(21),
            .right = ir.SolverTermId.fromIndex(22),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(24), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(5),
            .right = ir.SolverTermId.fromIndex(11),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(25), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(17),
            .right = ir.SolverTermId.fromIndex(23),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(26), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(24),
            .right = ir.SolverTermId.fromIndex(25),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(27), .sort = integer, .operation = .{ .remainder = .{
            .mode = .integer_euclidean,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
            .defined_by = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(28), .sort = integer, .operation = .{ .integer_literal = "1" } },
        .{ .id = ir.SolverTermId.fromIndex(29), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(27),
            .right = ir.SolverTermId.fromIndex(28),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(30), .sort = integer, .operation = .{ .integer_literal = "5" } },
        .{ .id = ir.SolverTermId.fromIndex(31), .sort = integer, .operation = .{ .integer_literal = "-2" } },
        .{ .id = ir.SolverTermId.fromIndex(32), .sort = boolean, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(31) } },
        .{ .id = ir.SolverTermId.fromIndex(33), .sort = integer, .operation = .{ .remainder = .{
            .mode = .integer_floor,
            .left = ir.SolverTermId.fromIndex(30),
            .right = ir.SolverTermId.fromIndex(31),
            .defined_by = ir.SolverTermId.fromIndex(32),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(34), .sort = integer, .operation = .{ .integer_literal = "-1" } },
        .{ .id = ir.SolverTermId.fromIndex(35), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(33),
            .right = ir.SolverTermId.fromIndex(34),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(36), .sort = unsigned_bv8, .operation = .{ .remainder = .{
            .mode = .bit_vector_unsigned,
            .left = ir.SolverTermId.fromIndex(12),
            .right = ir.SolverTermId.fromIndex(13),
            .defined_by = ir.SolverTermId.fromIndex(14),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(37), .sort = unsigned_bv8, .operation = .{ .bit_vector_literal = .{ .value = "1", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(38), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(36),
            .right = ir.SolverTermId.fromIndex(37),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(39), .sort = signed_bv8, .operation = .{ .remainder = .{
            .mode = .bit_vector_signed_dividend,
            .left = ir.SolverTermId.fromIndex(18),
            .right = ir.SolverTermId.fromIndex(19),
            .defined_by = ir.SolverTermId.fromIndex(20),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(40), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "255", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(41), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(39),
            .right = ir.SolverTermId.fromIndex(40),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(42), .sort = signed_bv8, .operation = .{ .remainder = .{
            .mode = .bit_vector_signed_divisor,
            .left = ir.SolverTermId.fromIndex(18),
            .right = ir.SolverTermId.fromIndex(19),
            .defined_by = ir.SolverTermId.fromIndex(20),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(43), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "1", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(44), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(42),
            .right = ir.SolverTermId.fromIndex(43),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(45), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(29),
            .right = ir.SolverTermId.fromIndex(35),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(46), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(38),
            .right = ir.SolverTermId.fromIndex(41),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(47), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(46),
            .right = ir.SolverTermId.fromIndex(44),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(48), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(45),
            .right = ir.SolverTermId.fromIndex(47),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(49), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(26),
            .right = ir.SolverTermId.fromIndex(48),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(50), .sort = integer, .operation = .{ .division = .{
            .mode = .integer_floor,
            .left = ir.SolverTermId.fromIndex(30),
            .right = ir.SolverTermId.fromIndex(31),
            .defined_by = ir.SolverTermId.fromIndex(32),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(51), .sort = integer, .operation = .{ .integer_literal = "-3" } },
        .{ .id = ir.SolverTermId.fromIndex(52), .sort = boolean, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(50),
            .right = ir.SolverTermId.fromIndex(51),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(53), .sort = boolean, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(49),
            .right = ir.SolverTermId.fromIndex(52),
        } } },
    };
    const constraints = [_]ir.Constraint{
        .{ .id = ir.ConstraintId.fromIndex(0), .predicate = ir.SolverTermId.fromIndex(2) },
        .{ .id = ir.ConstraintId.fromIndex(1), .predicate = ir.SolverTermId.fromIndex(8) },
        .{ .id = ir.ConstraintId.fromIndex(2), .predicate = ir.SolverTermId.fromIndex(14) },
        .{ .id = ir.ConstraintId.fromIndex(3), .predicate = ir.SolverTermId.fromIndex(20) },
        .{ .id = ir.ConstraintId.fromIndex(4), .predicate = ir.SolverTermId.fromIndex(32) },
    };
    const program: ir.Program = .{
        .program_id = "z3-guarded-division",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &terms,
        .constraints = &constraints,
    };
    var query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{
            ir.ConstraintId.fromIndex(0),
            ir.ConstraintId.fromIndex(1),
            ir.ConstraintId.fromIndex(2),
            ir.ConstraintId.fromIndex(3),
            ir.ConstraintId.fromIndex(4),
        },
        .goal = ir.SolverTermId.fromIndex(53),
    };

    query.assumptions = &.{ ir.ConstraintId.fromIndex(0), ir.ConstraintId.fromIndex(2), ir.ConstraintId.fromIndex(3), ir.ConstraintId.fromIndex(4) };
    var inferred_guard = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer inferred_guard.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, inferred_guard.resolution);

    terms[8].operation = .{ .semantic_atom = .{ .instruction_effects = ir.InstructionId.fromIndex(0) } };
    try std.testing.expectError(error.MissingSolverPrecondition, defaultBackend().solve(std.testing.allocator, &program, query));
    terms[8].operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(7) };
    query.assumptions = &.{
        ir.ConstraintId.fromIndex(0),
        ir.ConstraintId.fromIndex(1),
        ir.ConstraintId.fromIndex(2),
        ir.ConstraintId.fromIndex(3),
        ir.ConstraintId.fromIndex(4),
    };
    try std.testing.expectEqual(ir.SolverResolution.unknown, lifter.solver.solve(&program, query));
    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
}

test "Z3 matches internal integer division semantics in every sign quadrant" {
    const cases = [_]struct {
        left: []const u8,
        right: []const u8,
        euclidean_quotient: []const u8,
        euclidean_remainder: []const u8,
        floor_quotient: []const u8,
        floor_remainder: []const u8,
    }{
        .{ .left = "7", .right = "3", .euclidean_quotient = "2", .euclidean_remainder = "1", .floor_quotient = "2", .floor_remainder = "1" },
        .{ .left = "-7", .right = "3", .euclidean_quotient = "-3", .euclidean_remainder = "2", .floor_quotient = "-3", .floor_remainder = "2" },
        .{ .left = "7", .right = "-3", .euclidean_quotient = "-2", .euclidean_remainder = "1", .floor_quotient = "-3", .floor_remainder = "-2" },
        .{ .left = "-7", .right = "-3", .euclidean_quotient = "3", .euclidean_remainder = "2", .floor_quotient = "2", .floor_remainder = "-1" },
    };
    const integer: ir.SolverSort = .{ .kind = .integer };
    const boolean: ir.SolverSort = .{ .kind = .boolean };

    for (cases) |values| {
        const terms = [_]ir.SolverTerm{
            .{ .id = ir.SolverTermId.fromIndex(0), .sort = integer, .operation = .{ .integer_literal = values.left } },
            .{ .id = ir.SolverTermId.fromIndex(1), .sort = integer, .operation = .{ .integer_literal = values.right } },
            .{ .id = ir.SolverTermId.fromIndex(2), .sort = boolean, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(1) } },
            .{ .id = ir.SolverTermId.fromIndex(3), .sort = integer, .operation = .{ .division = .{
                .mode = .integer_euclidean,
                .left = ir.SolverTermId.fromIndex(0),
                .right = ir.SolverTermId.fromIndex(1),
                .defined_by = ir.SolverTermId.fromIndex(2),
            } } },
            .{ .id = ir.SolverTermId.fromIndex(4), .sort = integer, .operation = .{ .integer_literal = values.euclidean_quotient } },
            .{ .id = ir.SolverTermId.fromIndex(5), .sort = boolean, .operation = .{ .binary = .{
                .operator = .equal,
                .left = ir.SolverTermId.fromIndex(3),
                .right = ir.SolverTermId.fromIndex(4),
            } } },
            .{ .id = ir.SolverTermId.fromIndex(6), .sort = integer, .operation = .{ .remainder = .{
                .mode = .integer_euclidean,
                .left = ir.SolverTermId.fromIndex(0),
                .right = ir.SolverTermId.fromIndex(1),
                .defined_by = ir.SolverTermId.fromIndex(2),
            } } },
            .{ .id = ir.SolverTermId.fromIndex(7), .sort = integer, .operation = .{ .integer_literal = values.euclidean_remainder } },
            .{ .id = ir.SolverTermId.fromIndex(8), .sort = boolean, .operation = .{ .binary = .{
                .operator = .equal,
                .left = ir.SolverTermId.fromIndex(6),
                .right = ir.SolverTermId.fromIndex(7),
            } } },
            .{ .id = ir.SolverTermId.fromIndex(9), .sort = integer, .operation = .{ .division = .{
                .mode = .integer_floor,
                .left = ir.SolverTermId.fromIndex(0),
                .right = ir.SolverTermId.fromIndex(1),
                .defined_by = ir.SolverTermId.fromIndex(2),
            } } },
            .{ .id = ir.SolverTermId.fromIndex(10), .sort = integer, .operation = .{ .integer_literal = values.floor_quotient } },
            .{ .id = ir.SolverTermId.fromIndex(11), .sort = boolean, .operation = .{ .binary = .{
                .operator = .equal,
                .left = ir.SolverTermId.fromIndex(9),
                .right = ir.SolverTermId.fromIndex(10),
            } } },
            .{ .id = ir.SolverTermId.fromIndex(12), .sort = integer, .operation = .{ .remainder = .{
                .mode = .integer_floor,
                .left = ir.SolverTermId.fromIndex(0),
                .right = ir.SolverTermId.fromIndex(1),
                .defined_by = ir.SolverTermId.fromIndex(2),
            } } },
            .{ .id = ir.SolverTermId.fromIndex(13), .sort = integer, .operation = .{ .integer_literal = values.floor_remainder } },
            .{ .id = ir.SolverTermId.fromIndex(14), .sort = boolean, .operation = .{ .binary = .{
                .operator = .equal,
                .left = ir.SolverTermId.fromIndex(12),
                .right = ir.SolverTermId.fromIndex(13),
            } } },
            .{ .id = ir.SolverTermId.fromIndex(15), .sort = boolean, .operation = .{ .binary = .{
                .operator = .logical_and,
                .left = ir.SolverTermId.fromIndex(5),
                .right = ir.SolverTermId.fromIndex(8),
            } } },
            .{ .id = ir.SolverTermId.fromIndex(16), .sort = boolean, .operation = .{ .binary = .{
                .operator = .logical_and,
                .left = ir.SolverTermId.fromIndex(11),
                .right = ir.SolverTermId.fromIndex(14),
            } } },
            .{ .id = ir.SolverTermId.fromIndex(17), .sort = boolean, .operation = .{ .binary = .{
                .operator = .logical_and,
                .left = ir.SolverTermId.fromIndex(15),
                .right = ir.SolverTermId.fromIndex(16),
            } } },
        };
        const constraints = [_]ir.Constraint{.{
            .id = ir.ConstraintId.fromIndex(0),
            .predicate = ir.SolverTermId.fromIndex(2),
        }};
        const program: ir.Program = .{
            .program_id = "integer-division-sign-quadrants",
            .entry_function = ir.FunctionId.fromIndex(0),
            .functions = &.{},
            .blocks = &.{},
            .instructions = &.{},
            .values = &.{},
            .solver_terms = &terms,
            .constraints = &constraints,
        };
        const query: ir.SolverQuery = .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .assumptions = &.{ir.ConstraintId.fromIndex(0)},
            .goal = ir.SolverTermId.fromIndex(17),
        };

        try std.testing.expectEqual(ir.SolverResolution.proved, lifter.solver.solve(&program, query));
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    }
}

const BitVectorDivisionKind = enum {
    unsigned_division,
    signed_division,
    unsigned_remainder,
    signed_dividend_remainder,
    signed_divisor_remainder,
};

const BitVectorDivisionCase = struct {
    kind: BitVectorDivisionKind,
    left: []const u8,
    right: []const u8,
    expected: []const u8,
};

fn bitVectorDivisionOperation(case: BitVectorDivisionCase) ir.SolverTermOperation {
    const left = ir.SolverTermId.fromIndex(0);
    const right = ir.SolverTermId.fromIndex(1);
    const defined_by = ir.SolverTermId.fromIndex(2);
    return switch (case.kind) {
        .unsigned_division => .{ .division = .{
            .mode = .bit_vector_unsigned,
            .left = left,
            .right = right,
            .defined_by = defined_by,
        } },
        .signed_division => .{ .division = .{
            .mode = .bit_vector_signed,
            .left = left,
            .right = right,
            .defined_by = defined_by,
        } },
        .unsigned_remainder => .{ .remainder = .{
            .mode = .bit_vector_unsigned,
            .left = left,
            .right = right,
            .defined_by = defined_by,
        } },
        .signed_dividend_remainder => .{ .remainder = .{
            .mode = .bit_vector_signed_dividend,
            .left = left,
            .right = right,
            .defined_by = defined_by,
        } },
        .signed_divisor_remainder => .{ .remainder = .{
            .mode = .bit_vector_signed_divisor,
            .left = left,
            .right = right,
            .defined_by = defined_by,
        } },
    };
}

test "Z3 and internal facts agree across bounded bit-vector division semantics" {
    const boolean: ir.SolverSort = .{ .kind = .boolean };
    const unsigned_bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8 };
    const signed_bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8, .signed = true };
    const cases = [_]BitVectorDivisionCase{
        .{ .kind = .unsigned_division, .left = "255", .right = "2", .expected = "127" },
        .{ .kind = .unsigned_remainder, .left = "255", .right = "2", .expected = "1" },
        .{ .kind = .signed_division, .left = "5", .right = "2", .expected = "2" },
        .{ .kind = .signed_division, .left = "251", .right = "2", .expected = "254" },
        .{ .kind = .signed_division, .left = "5", .right = "254", .expected = "254" },
        .{ .kind = .signed_division, .left = "251", .right = "254", .expected = "2" },
        .{ .kind = .signed_division, .left = "128", .right = "255", .expected = "128" },
        .{ .kind = .signed_dividend_remainder, .left = "5", .right = "2", .expected = "1" },
        .{ .kind = .signed_dividend_remainder, .left = "251", .right = "2", .expected = "255" },
        .{ .kind = .signed_dividend_remainder, .left = "5", .right = "254", .expected = "1" },
        .{ .kind = .signed_dividend_remainder, .left = "251", .right = "254", .expected = "255" },
        .{ .kind = .signed_dividend_remainder, .left = "128", .right = "255", .expected = "0" },
        .{ .kind = .signed_divisor_remainder, .left = "5", .right = "2", .expected = "1" },
        .{ .kind = .signed_divisor_remainder, .left = "251", .right = "2", .expected = "1" },
        .{ .kind = .signed_divisor_remainder, .left = "5", .right = "254", .expected = "255" },
        .{ .kind = .signed_divisor_remainder, .left = "251", .right = "254", .expected = "255" },
        .{ .kind = .signed_divisor_remainder, .left = "128", .right = "255", .expected = "0" },
    };

    for (cases) |case| {
        const sort = switch (case.kind) {
            .unsigned_division, .unsigned_remainder => unsigned_bv8,
            .signed_division, .signed_dividend_remainder, .signed_divisor_remainder => signed_bv8,
        };
        const terms = [_]ir.SolverTerm{
            literalTerm(0, sort, case.left),
            literalTerm(1, sort, case.right),
            .{ .id = ir.SolverTermId.fromIndex(2), .sort = boolean, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(1) } },
            .{ .id = ir.SolverTermId.fromIndex(3), .sort = sort, .operation = bitVectorDivisionOperation(case) },
            literalTerm(4, sort, case.expected),
            .{ .id = ir.SolverTermId.fromIndex(5), .sort = boolean, .operation = .{ .binary = .{
                .operator = .equal,
                .left = ir.SolverTermId.fromIndex(3),
                .right = ir.SolverTermId.fromIndex(4),
            } } },
        };
        const constraints = [_]ir.Constraint{.{
            .id = ir.ConstraintId.fromIndex(0),
            .predicate = ir.SolverTermId.fromIndex(2),
        }};
        const program: ir.Program = .{
            .program_id = "bounded-bit-vector-division-differential",
            .entry_function = ir.FunctionId.fromIndex(0),
            .functions = &.{},
            .blocks = &.{},
            .instructions = &.{},
            .values = &.{},
            .solver_terms = &terms,
            .constraints = &constraints,
        };
        const query: ir.SolverQuery = .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .assumptions = &.{ir.ConstraintId.fromIndex(0)},
            .goal = ir.SolverTermId.fromIndex(5),
        };

        const internal = lifter.solver.solve(&program, query);
        try std.testing.expectEqual(ir.SolverResolution.proved, internal);
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(internal, result.resolution);
    }
}

test "Z3 proves a symbolic implication under explicit assumptions" {
    const value_id = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{.{ .id = value_id, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .parameter = 0 } }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = value_id } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "0" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .greater, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "1" } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .integer }, .operation = .{ .binary = .{ .operator = .add, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(3) } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .greater, .left = ir.SolverTermId.fromIndex(4), .right = ir.SolverTermId.fromIndex(1) } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
    };
    const constraints = [_]ir.Constraint{
        .{ .id = ir.ConstraintId.fromIndex(0), .predicate = ir.SolverTermId.fromIndex(2) },
        .{ .id = ir.ConstraintId.fromIndex(1), .predicate = ir.SolverTermId.fromIndex(6) },
    };
    const program: ir.Program = .{ .program_id = "z3-symbolic-implication", .entry_function = ir.FunctionId.fromIndex(0), .functions = &.{}, .blocks = &.{}, .instructions = &.{}, .values = &values, .solver_terms = &terms, .constraints = &constraints };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .assumptions = &.{ ir.ConstraintId.fromIndex(0), ir.ConstraintId.fromIndex(1) }, .goal = ir.SolverTermId.fromIndex(5) };
    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqualSlices(ir.ConstraintId, &.{ir.ConstraintId.fromIndex(0)}, result.unsat_core.items);
}

test "Z3 returns typed integer and rational models" {
    {
        const value_id = ir.ValueId.fromIndex(0);
        const values = [_]ir.Value{.{ .id = value_id, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .parameter = 0 } }};
        const terms = [_]ir.SolverTerm{
            .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = value_id } },
            .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "7" } },
            .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
        };
        const program: ir.Program = .{ .program_id = "z3-typed-model", .entry_function = ir.FunctionId.fromIndex(0), .functions = &.{}, .blocks = &.{}, .instructions = &.{}, .values = &values, .solver_terms = &terms };
        const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
        try std.testing.expectEqual(@as(usize, 1), result.model.items.len);
        try std.testing.expectEqualStrings("7", result.model.items[0].value.integer);
        try std.testing.expectEqual(
            lifter.solver_model.Replay.satisfied,
            try lifter.solver_model.replayAlloc(std.testing.allocator, &program, query, result.model.items),
        );
    }
    {
        const value_id = ir.ValueId.fromIndex(0);
        const values = [_]ir.Value{.{ .id = value_id, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .parameter = 0 } }};
        const terms = [_]ir.SolverTerm{
            .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .real }, .operation = .{ .value = value_id } },
            .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .real }, .operation = .{ .real_literal = .{ .numerator = "3", .denominator = "2" } } },
            .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
        };
        const program: ir.Program = .{ .program_id = "z3-rational-model", .entry_function = ir.FunctionId.fromIndex(0), .functions = &.{}, .blocks = &.{}, .instructions = &.{}, .values = &values, .solver_terms = &terms };
        const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        const rational = result.model.items[0].value.real;
        try std.testing.expectEqualStrings("3", rational.numerator);
        try std.testing.expectEqualStrings("2", rational.denominator);
        try std.testing.expectEqual(
            lifter.solver_model.Replay.satisfied,
            try lifter.solver_model.replayAlloc(std.testing.allocator, &program, query, result.model.items),
        );
    }
}

test "Z3 proves bit-vector and arbitrary precision identities" {
    {
        const value_id = ir.ValueId.fromIndex(0);
        const values = [_]ir.Value{.{ .id = value_id, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .parameter = 0 } }};
        const bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8 };
        const terms = [_]ir.SolverTerm{
            .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv8, .operation = .{ .value = value_id } },
            .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv8, .operation = .{ .bit_vector_literal = .{ .value = "0", .bit_width = 8 } } },
            .{ .id = ir.SolverTermId.fromIndex(2), .sort = bv8, .operation = .{ .binary = .{ .operator = .bit_and, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
            .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(2), .right = ir.SolverTermId.fromIndex(1) } } },
        };
        const program: ir.Program = .{ .program_id = "z3-bit-vector-mask", .entry_function = ir.FunctionId.fromIndex(0), .functions = &.{}, .blocks = &.{}, .instructions = &.{}, .values = &values, .solver_terms = &terms };
        const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(3) };
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    }
    {
        const bv128: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 128 };
        const terms = [_]ir.SolverTerm{
            .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv128, .operation = .{ .bit_vector_literal = .{
                .value = "340282366920938463463374607431768211455",
                .bit_width = 128,
            } } },
            .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv128, .operation = .{ .bit_vector_literal = .{
                .value = "1",
                .bit_width = 128,
            } } },
            .{ .id = ir.SolverTermId.fromIndex(2), .sort = bv128, .operation = .{ .binary = .{
                .operator = .add,
                .left = ir.SolverTermId.fromIndex(0),
                .right = ir.SolverTermId.fromIndex(1),
            } } },
            .{ .id = ir.SolverTermId.fromIndex(3), .sort = bv128, .operation = .{ .bit_vector_literal = .{
                .value = "0",
                .bit_width = 128,
            } } },
            .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
                .operator = .equal,
                .left = ir.SolverTermId.fromIndex(2),
                .right = ir.SolverTermId.fromIndex(3),
            } } },
        };
        const program: ir.Program = .{ .program_id = "z3-wide-bit-vector-wrap", .entry_function = ir.FunctionId.fromIndex(0), .functions = &.{}, .blocks = &.{}, .instructions = &.{}, .values = &.{}, .solver_terms = &terms };
        const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(4) };
        try std.testing.expectEqual(ir.SolverResolution.unknown, lifter.solver.solve(&program, query));
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    }
    {
        const terms = [_]ir.SolverTerm{
            .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "9223372036854775808" } },
            .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "9223372036854775808" } },
            .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
        };
        const program: ir.Program = .{ .program_id = "z3-arbitrary-precision-integer", .entry_function = ir.FunctionId.fromIndex(0), .functions = &.{}, .blocks = &.{}, .instructions = &.{}, .values = &.{}, .solver_terms = &terms };
        const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) };
        try std.testing.expect(lifter.solver.evaluate(&program, ir.SolverTermId.fromIndex(0)) == .unknown);
        try std.testing.expectEqual(ir.SolverResolution.proved, lifter.solver.solve(&program, query));
        var result = try defaultBackend().solve(std.testing.allocator, &program, query);
        defer result.deinit(std.testing.allocator);
        try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    }
}

test "Z3 returns wide bit-vector models without host-width truncation" {
    const value_id = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = value_id,
        .function = ir.FunctionId.fromIndex(0),
        .type = .dynamic,
        .origin = .{ .parameter = 0 },
    }};
    const bv128: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 128 };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv128, .operation = .{ .value = value_id } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv128, .operation = .{ .bit_vector_literal = .{
            .value = "340282366920938463463374607431768211455",
            .bit_width = 128,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "z3-wide-bit-vector-model",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .find_model,
        .goal = ir.SolverTermId.fromIndex(2),
    };
    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqual(@as(usize, 1), result.model.items.len);
    const model = result.model.items[0].value.bit_vector;
    try std.testing.expectEqual(@as(u16, 128), model.bit_width);
    try std.testing.expectEqualStrings("340282366920938463463374607431768211455", model.value);
}

test "Z3 receives exact wide constants from normalized IR value definitions" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_factor.index()].type = .{ .kind = .integer, .bit_width = 128, .signed = false };
    var instructions = fixture.instructions;
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{
        .integer = "340282366920938463463374607431768211455",
    } };
    const bv128: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 128 };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv128, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv128, .operation = .{ .bit_vector_literal = .{
            .value = "340282366920938463463374607431768211455",
            .bit_width = 128,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) };

    try std.testing.expectEqual(ir.SolverResolution.unknown, lifter.solver.solve(&program, query));
    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
}

test "Z3 semantic atoms require matching explicit assumptions" {
    const fixture = lifter.fixtures.arithmetic_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .semantic_atom = .{ .instruction_effects = fixture.i_sum } } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .semantic_atom = .{ .primitive_operator_domain = fixture.i_sum } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .semantic_atom = .{ .instruction_effects = fixture.i_result } } },
    };
    const constraints = [_]ir.Constraint{.{ .id = ir.ConstraintId.fromIndex(0), .predicate = ir.SolverTermId.fromIndex(0) }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    const assumed_exact: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .assumptions = &.{ir.ConstraintId.fromIndex(0)}, .goal = ir.SolverTermId.fromIndex(0) };
    const unassumed: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(1), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(0) };
    const wrong_property: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(2), .kind = .prove_true, .assumptions = &.{ir.ConstraintId.fromIndex(0)}, .goal = ir.SolverTermId.fromIndex(1) };
    const wrong_instruction: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(3), .kind = .prove_true, .assumptions = &.{ir.ConstraintId.fromIndex(0)}, .goal = ir.SolverTermId.fromIndex(2) };
    var exact_result = try defaultBackend().solve(std.testing.allocator, &program, assumed_exact);
    defer exact_result.deinit(std.testing.allocator);
    var unassumed_result = try defaultBackend().solve(std.testing.allocator, &program, unassumed);
    defer unassumed_result.deinit(std.testing.allocator);
    var property_result = try defaultBackend().solve(std.testing.allocator, &program, wrong_property);
    defer property_result.deinit(std.testing.allocator);
    var instruction_result = try defaultBackend().solve(std.testing.allocator, &program, wrong_instruction);
    defer instruction_result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, exact_result.resolution);
    try std.testing.expectEqual(ir.SolverResolution.disproved, unassumed_result.resolution);
    try std.testing.expectEqual(ir.SolverResolution.disproved, property_result.resolution);
    try std.testing.expectEqual(ir.SolverResolution.disproved, instruction_result.resolution);
    try std.testing.expectEqualSlices(ir.ConstraintId, &.{ir.ConstraintId.fromIndex(0)}, exact_result.unsat_core.items);
    try std.testing.expectEqual(@as(usize, 1), unassumed_result.model.items.len);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(0), unassumed_result.model.items[0].term);
    try std.testing.expect(!unassumed_result.model.items[0].value.boolean);
}

test "Z3 orchestration admits and emits a typed semantic claim" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_left.index()].type = .dynamic;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation.binary.mode = .primitive;
    const instruction_claims = [_]ir.ClaimId{ir.ClaimId.fromIndex(0)};
    instructions[fixture.i_sum.index()].claims = &instruction_claims;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .semantic_atom = .{ .primitive_operator_domain = fixture.i_sum } },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{fixture.proof},
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(0),
    }};
    const claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .instruction = fixture.i_sum },
        .predicate = ir.SolverTermId.fromIndex(0),
        .purpose = .{ .primitive_operator_domain = .pure },
        .status = .unproven,
        .required_for_emission = true,
        .evidence = &.{fixture.proof},
        .query = ir.QueryId.fromIndex(0),
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .primitive_domain,
        .subject = .{ .instruction = fixture.i_sum },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "Z3 must discharge the linked primitive-domain obligation",
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    program.queries = &queries;
    program.claims = &claims;
    program.obligations = &obligations;

    var resolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &program, defaultBackend());
    defer resolved.deinit();
    try std.testing.expectEqual(ir.ClaimStatus.proved, resolved.program.claims[0].status);
    try std.testing.expectEqual(ir.ObligationStatus.discharged, resolved.program.obligations[0].status);
    try std.testing.expectEqual(resolved.program.claims[0].certificate, resolved.program.obligations[0].certificate);
    try std.testing.expectEqual(@as(usize, 1), resolved.program.unsat_cores.len);
    try std.testing.expectEqualSlices(ir.ConstraintId, &.{ir.ConstraintId.fromIndex(0)}, resolved.program.unsat_cores[0].constraints);
    var report = try lifter.validate.validate(std.testing.allocator, &resolved.program, .readable_luau);
    defer report.deinit();
    try std.testing.expect(report.isClean());

    const tampered_cores = try std.testing.allocator.dupe(ir.UnsatCore, resolved.program.unsat_cores);
    defer std.testing.allocator.free(tampered_cores);
    tampered_cores[0].constraints = &.{};
    const tampered_certificates = try std.testing.allocator.dupe(ir.SolverCertificate, resolved.program.certificates);
    defer std.testing.allocator.free(tampered_certificates);
    var tampered = resolved.program;
    tampered.unsat_cores = tampered_cores;
    tampered.certificates = tampered_certificates;
    const tampered_digest = try lifter.proof_digest.computeAlloc(
        std.testing.allocator,
        &tampered,
        tampered.queries[tampered_certificates[0].query.index()],
        tampered_certificates[0].engine,
        tampered_certificates[0].resolution,
        tampered_certificates[0].evidence,
        &.{},
        &.{},
    );
    defer std.testing.allocator.free(tampered_digest);
    tampered_certificates[0].certificate_digest = tampered_digest;
    var tampered_report = try lifter.validate.validate(std.testing.allocator, &tampered, .readable_luau);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.isClean());
    try std.testing.expectError(
        error.ContradictoryUnsatCore,
        lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &tampered, defaultBackend()),
    );

    var outcome = try lifter.pipeline.runAlloc(
        std.testing.allocator,
        &program,
        defaultBackend(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "return (left + right) * 2") != null);
}

test "Z3 receives exact IR constants through normalized value terms" {
    const fixture = lifter.fixtures.arithmetic_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation = .{ .constant = .{ .integer = "4" } };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = fixture.v_result } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "8" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(2),
    };
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;

    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
}

test "Z3 pipeline plans both directions from scoped branch facts" {
    const fixture = lifter.fixtures.absolute_value_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = fixture.v_is_negative },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{fixture.proof},
        .scope = .{ .block = fixture.b_entry },
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;

    var outcome = try lifter.pipeline.runAlloc(
        std.testing.allocator,
        &program,
        defaultBackend(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expectEqual(ir.ClaimStatus.proved, outcome.program().?.claims[0].status);
    try std.testing.expectEqual(ir.ClaimStatus.disproved, outcome.program().?.claims[1].status);
    try std.testing.expectEqual(@as(usize, 2), outcome.program().?.certificates.len);
    try std.testing.expectEqual(@as(usize, 1), outcome.program().?.unsat_cores.len);
    try std.testing.expectEqual(@as(usize, 1), outcome.program().?.solver_models.len);
    try std.testing.expectEqual(fixture.b_negative, outcome.program().?.blocks[fixture.b_entry.index()].terminator.jump.target);
    try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "if ") == null);
}

test "Z3 proves relational edge facts through exact-pure IR definitions" {
    const fixture = lifter.fixtures.relational_dispatch_module;
    var outcome = try lifter.pipeline.runAlloc(
        std.testing.allocator,
        &fixture.program,
        defaultBackend(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();

    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expectEqual(@as(usize, 4), outcome.program().?.queries.len);
    try std.testing.expectEqual(@as(usize, 4), outcome.program().?.certificates.len);
    try std.testing.expectEqual(fixture.b_true, outcome.program().?.blocks[fixture.b_left.index()].terminator.jump.target);
    try std.testing.expectEqual(fixture.b_false, outcome.program().?.blocks[fixture.b_right.index()].terminator.jump.target);
    try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "state_matches") == null);
    try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "if selector then") != null);
}
