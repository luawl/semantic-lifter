const std = @import("std");
const ir = @import("ir.zig");

pub const max_dependencies = 3;

pub const DependencyIterator = struct {
    operation: ir.SolverTermOperation,
    index: u8 = 0,

    pub fn next(self: *DependencyIterator) ?ir.SolverTermId {
        const dependency = switch (self.operation) {
            .dynamic_truthiness, .dynamic_number_is_nan, .logical_not, .bit_vector_not, .integer_to_bit_vector, .arithmetic_negate, .is_nonzero => |operand| if (self.index == 0) operand else null,
            .value_definition => |definition| switch (self.index) {
                0 => definition.expression,
                1 => definition.valid_when,
                else => null,
            },
            .binary => |binary| switch (self.index) {
                0 => binary.left,
                1 => binary.right,
                else => null,
            },
            .if_then_else => |selection| switch (self.index) {
                0 => selection.condition,
                1 => selection.then_term,
                2 => selection.else_term,
                else => null,
            },
            .bit_vector_extract => |extract| if (self.index == 0) extract.operand else null,
            .bit_vector_concat => |concat| switch (self.index) {
                0 => concat.high,
                1 => concat.low,
                else => null,
            },
            .bit_vector_extend => |extension| if (self.index == 0) extension.operand else null,
            .bit_vector_rotate => |rotation| switch (self.index) {
                0 => rotation.operand,
                1 => rotation.amount,
                else => null,
            },
            .bit_vector_to_integer => |conversion| if (self.index == 0) conversion.operand else null,
            .division => |division| switch (self.index) {
                0 => division.left,
                1 => division.right,
                2 => division.defined_by,
                else => null,
            },
            .remainder => |remainder| switch (self.index) {
                0 => remainder.left,
                1 => remainder.right,
                2 => remainder.defined_by,
                else => null,
            },
            .value, .semantic_atom, .boolean_literal, .integer_literal, .real_literal, .bit_vector_literal => null,
        };
        if (dependency != null) self.index += 1;
        return dependency;
    }
};

pub fn dependencies(operation: ir.SolverTermOperation) DependencyIterator {
    return .{ .operation = operation };
}

pub const QueryTermSet = struct {
    allocator: std.mem.Allocator,
    marked: []bool,

    pub const InitError = error{
        InvalidQueryReference,
        InvalidTermGraph,
    } || std.mem.Allocator.Error;

    pub fn init(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        query: ir.SolverQuery,
    ) InitError!QueryTermSet {
        const marked = try allocator.alloc(bool, program.solver_terms.len);
        errdefer allocator.free(marked);
        @memset(marked, false);

        try markRoot(marked, query.goal);
        for (query.assumptions) |constraint_id| {
            if (constraint_id.index() >= program.constraints.len) return error.InvalidQueryReference;
            try markRoot(marked, program.constraints[constraint_id.index()].predicate);
        }

        var term_offset = program.solver_terms.len;
        while (term_offset != 0) {
            term_offset -= 1;
            if (!marked[term_offset]) continue;
            const term = program.solver_terms[term_offset];
            if (term.id.index() != term_offset) return error.InvalidTermGraph;
            var iterator = dependencies(term.operation);
            while (iterator.next()) |dependency| {
                if (dependency.index() >= term_offset) return error.InvalidTermGraph;
                marked[dependency.index()] = true;
            }
        }

        return .{ .allocator = allocator, .marked = marked };
    }

    pub fn deinit(self: *QueryTermSet) void {
        self.allocator.free(self.marked);
        self.* = undefined;
    }

    pub fn contains(self: QueryTermSet, term_id: ir.SolverTermId) bool {
        return term_id.index() < self.marked.len and self.marked[term_id.index()];
    }

    fn markRoot(marked: []bool, term_id: ir.SolverTermId) error{InvalidQueryReference}!void {
        if (term_id.index() >= marked.len) return error.InvalidQueryReference;
        marked[term_id.index()] = true;
    }
};

pub fn remapDependencies(
    operation: ir.SolverTermOperation,
    mapped: []const ir.SolverTermId,
) ?ir.SolverTermOperation {
    return switch (operation) {
        .value, .semantic_atom, .boolean_literal, .integer_literal, .real_literal, .bit_vector_literal => if (mapped.len == 0) operation else null,
        .value_definition => |definition| remapValueDefinition(definition, mapped),
        .dynamic_truthiness => if (mapped.len == 1) .{ .dynamic_truthiness = mapped[0] } else null,
        .dynamic_number_is_nan => if (mapped.len == 1) .{ .dynamic_number_is_nan = mapped[0] } else null,
        .logical_not => if (mapped.len == 1) .{ .logical_not = mapped[0] } else null,
        .binary => |binary| if (mapped.len == 2) .{ .binary = .{
            .operator = binary.operator,
            .left = mapped[0],
            .right = mapped[1],
        } } else null,
        .if_then_else => if (mapped.len == 3) .{ .if_then_else = .{
            .condition = mapped[0],
            .then_term = mapped[1],
            .else_term = mapped[2],
        } } else null,
        .bit_vector_not => if (mapped.len == 1) .{ .bit_vector_not = mapped[0] } else null,
        .bit_vector_extract => |extract| if (mapped.len == 1) .{ .bit_vector_extract = .{
            .operand = mapped[0],
            .high = extract.high,
            .low = extract.low,
        } } else null,
        .bit_vector_concat => if (mapped.len == 2) .{ .bit_vector_concat = .{
            .high = mapped[0],
            .low = mapped[1],
        } } else null,
        .bit_vector_extend => |extension| if (mapped.len == 1) .{ .bit_vector_extend = .{
            .operand = mapped[0],
            .extra_bits = extension.extra_bits,
            .mode = extension.mode,
        } } else null,
        .bit_vector_rotate => |rotation| if (mapped.len == 2) .{ .bit_vector_rotate = .{
            .operand = mapped[0],
            .amount = mapped[1],
            .direction = rotation.direction,
        } } else null,
        .integer_to_bit_vector => if (mapped.len == 1) .{ .integer_to_bit_vector = mapped[0] } else null,
        .bit_vector_to_integer => |conversion| if (mapped.len == 1) .{ .bit_vector_to_integer = .{
            .operand = mapped[0],
            .signed = conversion.signed,
        } } else null,
        .arithmetic_negate => if (mapped.len == 1) .{ .arithmetic_negate = mapped[0] } else null,
        .is_nonzero => if (mapped.len == 1) .{ .is_nonzero = mapped[0] } else null,
        .division => |division| if (mapped.len == 3) .{ .division = .{
            .mode = division.mode,
            .left = mapped[0],
            .right = mapped[1],
            .defined_by = mapped[2],
        } } else null,
        .remainder => |remainder| if (mapped.len == 3) .{ .remainder = .{
            .mode = remainder.mode,
            .left = mapped[0],
            .right = mapped[1],
            .defined_by = mapped[2],
        } } else null,
    };
}

fn remapValueDefinition(
    definition: ir.SolverValueDefinition,
    mapped: []const ir.SolverTermId,
) ?ir.SolverTermOperation {
    const expected: usize = if (definition.valid_when == null) 1 else 2;
    if (mapped.len != expected) return null;
    return .{ .value_definition = .{
        .value = definition.value,
        .expression = mapped[0],
        .valid_when = if (expected == 2) mapped[1] else null,
    } };
}

pub fn sameOperationHead(left: ir.SolverTermOperation, right: ir.SolverTermOperation) bool {
    return switch (left) {
        .value => |left_value| switch (right) {
            .value => |right_value| left_value == right_value,
            else => false,
        },
        .value_definition => |left_definition| switch (right) {
            .value_definition => |right_definition| left_definition.value == right_definition.value,
            else => false,
        },
        .semantic_atom => |left_atom| switch (right) {
            .semantic_atom => |right_atom| std.meta.eql(left_atom, right_atom),
            else => false,
        },
        .dynamic_truthiness => switch (right) {
            .dynamic_truthiness => true,
            else => false,
        },
        .dynamic_number_is_nan => switch (right) {
            .dynamic_number_is_nan => true,
            else => false,
        },
        .boolean_literal => |left_value| switch (right) {
            .boolean_literal => |right_value| left_value == right_value,
            else => false,
        },
        .integer_literal => |left_value| switch (right) {
            .integer_literal => |right_value| std.mem.eql(u8, left_value, right_value),
            else => false,
        },
        .real_literal => |left_value| switch (right) {
            .real_literal => |right_value| std.mem.eql(u8, left_value.numerator, right_value.numerator) and
                std.mem.eql(u8, left_value.denominator, right_value.denominator),
            else => false,
        },
        .bit_vector_literal => |left_value| switch (right) {
            .bit_vector_literal => |right_value| left_value.bit_width == right_value.bit_width and
                std.mem.eql(u8, left_value.value, right_value.value),
            else => false,
        },
        .logical_not => switch (right) {
            .logical_not => true,
            else => false,
        },
        .binary => |left_binary| switch (right) {
            .binary => |right_binary| left_binary.operator == right_binary.operator,
            else => false,
        },
        .if_then_else => switch (right) {
            .if_then_else => true,
            else => false,
        },
        .bit_vector_not => switch (right) {
            .bit_vector_not => true,
            else => false,
        },
        .bit_vector_extract => |left_extract| switch (right) {
            .bit_vector_extract => |right_extract| left_extract.high == right_extract.high and left_extract.low == right_extract.low,
            else => false,
        },
        .bit_vector_concat => switch (right) {
            .bit_vector_concat => true,
            else => false,
        },
        .bit_vector_extend => |left_extension| switch (right) {
            .bit_vector_extend => |right_extension| left_extension.extra_bits == right_extension.extra_bits and
                left_extension.mode == right_extension.mode,
            else => false,
        },
        .bit_vector_rotate => |left_rotation| switch (right) {
            .bit_vector_rotate => |right_rotation| left_rotation.direction == right_rotation.direction,
            else => false,
        },
        .integer_to_bit_vector => switch (right) {
            .integer_to_bit_vector => true,
            else => false,
        },
        .bit_vector_to_integer => |left_conversion| switch (right) {
            .bit_vector_to_integer => |right_conversion| left_conversion.signed == right_conversion.signed,
            else => false,
        },
        .arithmetic_negate => switch (right) {
            .arithmetic_negate => true,
            else => false,
        },
        .is_nonzero => switch (right) {
            .is_nonzero => true,
            else => false,
        },
        .division => |left_division| switch (right) {
            .division => |right_division| left_division.mode == right_division.mode,
            else => false,
        },
        .remainder => |left_remainder| switch (right) {
            .remainder => |right_remainder| left_remainder.mode == right_remainder.mode,
            else => false,
        },
    };
}

test "conditional dependencies retain semantic operand order" {
    var iterator = dependencies(.{ .if_then_else = .{
        .condition = ir.SolverTermId.fromIndex(2),
        .then_term = ir.SolverTermId.fromIndex(5),
        .else_term = ir.SolverTermId.fromIndex(7),
    } });
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(2), iterator.next().?);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(5), iterator.next().?);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(7), iterator.next().?);
    try std.testing.expectEqual(@as(?ir.SolverTermId, null), iterator.next());
}

test "query term sets include goal and assumption dependencies only" {
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "3" } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "5" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .less,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "7" } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(3) } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = false } },
    };
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(4),
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .find_model,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(2),
    };
    const program: ir.Program = .{
        .program_id = "query-term-reachability",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &terms,
        .constraints = &constraints,
    };

    var reachable = try QueryTermSet.init(std.testing.allocator, &program, query);
    defer reachable.deinit();
    for (0..5) |term_index| try std.testing.expect(reachable.contains(ir.SolverTermId.fromIndex(term_index)));
    try std.testing.expect(!reachable.contains(ir.SolverTermId.fromIndex(5)));
    try std.testing.expect(!reachable.contains(ir.SolverTermId.fromIndex(99)));
}

test "guarded value definitions expose expression before condition" {
    var iterator = dependencies(.{ .value_definition = .{
        .value = ir.ValueId.fromIndex(4),
        .expression = ir.SolverTermId.fromIndex(7),
        .valid_when = ir.SolverTermId.fromIndex(9),
    } });
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(7), iterator.next().?);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(9), iterator.next().?);
    try std.testing.expectEqual(@as(?ir.SolverTermId, null), iterator.next());
}

test "dependency remapping preserves semantic metadata" {
    const definition: ir.SolverTermOperation = .{ .value_definition = .{
        .value = ir.ValueId.fromIndex(3),
        .expression = ir.SolverTermId.fromIndex(4),
        .valid_when = ir.SolverTermId.fromIndex(5),
    } };
    const remapped_definition = remapDependencies(definition, &.{
        ir.SolverTermId.fromIndex(10),
        ir.SolverTermId.fromIndex(11),
    }).?.value_definition;
    try std.testing.expectEqual(ir.ValueId.fromIndex(3), remapped_definition.value);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(10), remapped_definition.expression);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(11), remapped_definition.valid_when.?);

    const division: ir.SolverTermOperation = .{ .division = .{
        .mode = .bit_vector_signed,
        .left = ir.SolverTermId.fromIndex(1),
        .right = ir.SolverTermId.fromIndex(2),
        .defined_by = ir.SolverTermId.fromIndex(3),
    } };
    const remapped_division = remapDependencies(division, &.{
        ir.SolverTermId.fromIndex(7),
        ir.SolverTermId.fromIndex(8),
        ir.SolverTermId.fromIndex(9),
    }).?.division;
    try std.testing.expectEqual(ir.SolverDivisionMode.bit_vector_signed, remapped_division.mode);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(7), remapped_division.left);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(8), remapped_division.right);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(9), remapped_division.defined_by);
    try std.testing.expect(remapDependencies(division, &.{ir.SolverTermId.fromIndex(7)}) == null);
}

test "bit-vector structure exposes dependencies and keeps shape metadata" {
    var concat_dependencies = dependencies(.{ .bit_vector_concat = .{
        .high = ir.SolverTermId.fromIndex(4),
        .low = ir.SolverTermId.fromIndex(9),
    } });
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(4), concat_dependencies.next().?);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(9), concat_dependencies.next().?);
    try std.testing.expectEqual(@as(?ir.SolverTermId, null), concat_dependencies.next());

    const left_extract: ir.SolverTermOperation = .{ .bit_vector_extract = .{
        .operand = ir.SolverTermId.fromIndex(1),
        .high = 12,
        .low = 5,
    } };
    const same_extract: ir.SolverTermOperation = .{ .bit_vector_extract = .{
        .operand = ir.SolverTermId.fromIndex(8),
        .high = 12,
        .low = 5,
    } };
    const different_extract: ir.SolverTermOperation = .{ .bit_vector_extract = .{
        .operand = ir.SolverTermId.fromIndex(1),
        .high = 11,
        .low = 5,
    } };
    try std.testing.expect(sameOperationHead(left_extract, same_extract));
    try std.testing.expect(!sameOperationHead(left_extract, different_extract));

    const zero_extend: ir.SolverTermOperation = .{ .bit_vector_extend = .{
        .operand = ir.SolverTermId.fromIndex(1),
        .extra_bits = 8,
        .mode = .zero,
    } };
    const sign_extend: ir.SolverTermOperation = .{ .bit_vector_extend = .{
        .operand = ir.SolverTermId.fromIndex(1),
        .extra_bits = 8,
        .mode = .sign,
    } };
    try std.testing.expect(!sameOperationHead(zero_extend, sign_extend));

    const rotate_left: ir.SolverTermOperation = .{ .bit_vector_rotate = .{
        .operand = ir.SolverTermId.fromIndex(3),
        .amount = ir.SolverTermId.fromIndex(6),
        .direction = .left,
    } };
    const rotate_right: ir.SolverTermOperation = .{ .bit_vector_rotate = .{
        .operand = ir.SolverTermId.fromIndex(3),
        .amount = ir.SolverTermId.fromIndex(6),
        .direction = .right,
    } };
    try std.testing.expect(!sameOperationHead(rotate_left, rotate_right));
    var rotate_dependencies = dependencies(rotate_left);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(3), rotate_dependencies.next().?);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(6), rotate_dependencies.next().?);
    try std.testing.expectEqual(@as(?ir.SolverTermId, null), rotate_dependencies.next());

    var to_word_dependencies = dependencies(.{ .integer_to_bit_vector = ir.SolverTermId.fromIndex(12) });
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(12), to_word_dependencies.next().?);
    try std.testing.expectEqual(@as(?ir.SolverTermId, null), to_word_dependencies.next());
    const signed_integer: ir.SolverTermOperation = .{ .bit_vector_to_integer = .{
        .operand = ir.SolverTermId.fromIndex(13),
        .signed = true,
    } };
    const unsigned_integer: ir.SolverTermOperation = .{ .bit_vector_to_integer = .{
        .operand = ir.SolverTermId.fromIndex(13),
        .signed = false,
    } };
    try std.testing.expect(!sameOperationHead(signed_integer, unsigned_integer));
    var negate_dependencies = dependencies(.{ .arithmetic_negate = ir.SolverTermId.fromIndex(14) });
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(14), negate_dependencies.next().?);
    try std.testing.expectEqual(@as(?ir.SolverTermId, null), negate_dependencies.next());

    const division: ir.SolverTermOperation = .{ .division = .{
        .mode = .bit_vector_signed,
        .left = ir.SolverTermId.fromIndex(15),
        .right = ir.SolverTermId.fromIndex(16),
        .defined_by = ir.SolverTermId.fromIndex(17),
    } };
    var division_dependencies = dependencies(division);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(15), division_dependencies.next().?);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(16), division_dependencies.next().?);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(17), division_dependencies.next().?);
    try std.testing.expectEqual(@as(?ir.SolverTermId, null), division_dependencies.next());
    const unsigned_division: ir.SolverTermOperation = .{ .division = .{
        .mode = .bit_vector_unsigned,
        .left = ir.SolverTermId.fromIndex(15),
        .right = ir.SolverTermId.fromIndex(16),
        .defined_by = ir.SolverTermId.fromIndex(17),
    } };
    try std.testing.expect(!sameOperationHead(division, unsigned_division));

    const remainder: ir.SolverTermOperation = .{ .remainder = .{
        .mode = .bit_vector_signed_dividend,
        .left = ir.SolverTermId.fromIndex(18),
        .right = ir.SolverTermId.fromIndex(19),
        .defined_by = ir.SolverTermId.fromIndex(20),
    } };
    var remainder_dependencies = dependencies(remainder);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(18), remainder_dependencies.next().?);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(19), remainder_dependencies.next().?);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(20), remainder_dependencies.next().?);
    try std.testing.expectEqual(@as(?ir.SolverTermId, null), remainder_dependencies.next());
    const divisor_remainder: ir.SolverTermOperation = .{ .remainder = .{
        .mode = .bit_vector_signed_divisor,
        .left = ir.SolverTermId.fromIndex(18),
        .right = ir.SolverTermId.fromIndex(19),
        .defined_by = ir.SolverTermId.fromIndex(20),
    } };
    try std.testing.expect(!sameOperationHead(remainder, divisor_remainder));
}
