const std = @import("std");
const ir = @import("ir.zig");
const normalized_value = @import("normalized_value.zig");
const solver = @import("solver.zig");
const solver_term = @import("solver_term.zig");
const solver_equivalence = @import("solver_equivalence.zig");
const model_value = @import("solver_model_value.zig");
const numerals = @import("numerals.zig");

pub const Replay = enum {
    satisfied,
    contradictory,
    incomplete,
};

pub const Error = model_value.Error || error{InvalidModelInput};

pub fn replayAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    query: ir.SolverQuery,
    bindings: []const ir.SolverModelBinding,
) Error!Replay {
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const working_allocator = arena.allocator();

    var reachable = solver_term.QueryTermSet.init(working_allocator, program, query) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.InvalidQueryReference, error.InvalidTermGraph => return error.InvalidModelInput,
    };
    defer reachable.deinit();

    const binding_values = try working_allocator.alloc(?ir.SolverModelValue, program.solver_terms.len);
    @memset(binding_values, null);
    for (bindings) |binding| {
        if (!reachable.contains(binding.term) or binding_values[binding.term.index()] != null) return error.InvalidModelInput;
        if (!modelValueMatchesSort(binding.value, program.solver_terms[binding.term.index()].sort)) return error.InvalidModelInput;
        binding_values[binding.term.index()] = binding.value;
    }
    if (!dynamicIdentitiesCanonical(program, bindings) or !dynamicBindingsSemanticallyCoherent(program, bindings)) {
        return error.InvalidModelInput;
    }

    const values = try working_allocator.alloc(model_value.Value, program.solver_terms.len);
    for (values) |*value| value.* = model_value.unknown();
    const context: model_value.Context = .{ .allocator = working_allocator };
    const source_evaluator: SourceEvaluator = .{ .program = program, .context = context };

    for (program.solver_terms, 0..) |term, term_index| {
        if (!reachable.contains(term.id)) continue;
        var value = try evaluateTerm(program, context, source_evaluator, values, term, term_index);
        if (binding_values[term_index]) |binding| {
            const bound = try context.fromModel(binding);
            if (model_value.isUnknown(value)) {
                value = bound;
            } else if (!((try context.eql(value, bound)) orelse return error.InvalidModelInput)) {
                return .contradictory;
            }
        }
        values[term_index] = value;
    }

    for (query.assumptions) |constraint_id| {
        if (constraint_id.index() >= program.constraints.len) return error.InvalidModelInput;
        const predicate = program.constraints[constraint_id.index()].predicate;
        const assumption = model_value.truth(try priorValue(values, predicate, program.solver_terms.len)) orelse return .incomplete;
        if (!assumption) return .contradictory;
    }

    const goal = model_value.truth(try priorValue(values, query.goal, program.solver_terms.len)) orelse return .incomplete;
    return if (goal == expectedGoal(query.kind)) .satisfied else .contradictory;
}

fn evaluateTerm(
    program: *const ir.Program,
    context: model_value.Context,
    source_evaluator: SourceEvaluator,
    values: []const model_value.Value,
    term: ir.SolverTerm,
    term_index: usize,
) Error!model_value.Value {
    return switch (term.operation) {
        .value => |value_id| source_evaluator.evaluate(value_id, term.sort, 0),
        .value_definition => |definition| priorValue(values, definition.expression, term_index),
        .semantic_atom => model_value.unknown(),
        .dynamic_truthiness => |operand| if (solver_equivalence.dynamicTermTruthiness(program, operand)) |truth|
            context.booleanValue(truth)
        else
            model_value.unknown(),
        .dynamic_number_is_nan => |operand| if (solver_equivalence.dynamicTermIsNaN(program, operand)) |is_nan|
            context.booleanValue(is_nan)
        else
            model_value.unknown(),
        .boolean_literal => |value| context.booleanValue(value),
        .integer_literal => |value| context.integerLiteral(value),
        .real_literal => |value| context.realLiteral(value),
        .bit_vector_literal => |value| context.bitVectorLiteral(value),
        .logical_not => |operand| context.logicalNot(try priorValue(values, operand, term_index)),
        .binary => |binary| evaluateBinaryTerm(program, context, values, binary, term_index),
        .if_then_else => |selection| context.select(
            try priorValue(values, selection.condition, term_index),
            try priorValue(values, selection.then_term, term_index),
            try priorValue(values, selection.else_term, term_index),
        ),
        .bit_vector_not => |operand| context.bitVectorNot(try priorValue(values, operand, term_index)),
        .bit_vector_extract => |extract| context.bitVectorExtract(
            try priorValue(values, extract.operand, term_index),
            extract.high,
            extract.low,
        ),
        .bit_vector_concat => |concat| context.bitVectorConcat(
            try priorValue(values, concat.high, term_index),
            try priorValue(values, concat.low, term_index),
        ),
        .bit_vector_extend => |extension| context.bitVectorExtend(
            try priorValue(values, extension.operand, term_index),
            extension.extra_bits,
            extension.mode,
        ),
        .bit_vector_rotate => |rotation| context.bitVectorRotate(
            try priorValue(values, rotation.operand, term_index),
            try priorValue(values, rotation.amount, term_index),
            rotation.direction,
        ),
        .integer_to_bit_vector => |operand| context.integerToBitVector(
            try priorValue(values, operand, term_index),
            term.sort.bit_width,
        ),
        .bit_vector_to_integer => |conversion| context.bitVectorToInteger(
            try priorValue(values, conversion.operand, term_index),
            conversion.signed,
        ),
        .arithmetic_negate => |operand| context.negate(try priorValue(values, operand, term_index)),
        .is_nonzero => |operand| context.isNonzero(try priorValue(values, operand, term_index)),
        .division => |division| context.division(
            division.mode,
            try priorValue(values, division.left, term_index),
            try priorValue(values, division.right, term_index),
            try priorValue(values, division.defined_by, term_index),
        ),
        .remainder => |remainder| context.remainder(
            remainder.mode,
            try priorValue(values, remainder.left, term_index),
            try priorValue(values, remainder.right, term_index),
            try priorValue(values, remainder.defined_by, term_index),
        ),
    };
}

fn evaluateBinaryTerm(
    program: *const ir.Program,
    context: model_value.Context,
    values: []const model_value.Value,
    binary: ir.SolverBinary,
    term_index: usize,
) Error!model_value.Value {
    if ((binary.operator == .equal or binary.operator == .not_equal) and
        solver_equivalence.termsEquivalent(program, binary.left, binary.right))
    {
        return context.booleanValue(binary.operator == .equal);
    }
    if ((binary.operator == .equal or binary.operator == .not_equal) and
        solver_equivalence.termsDistinct(program, binary.left, binary.right))
    {
        return context.booleanValue(binary.operator == .not_equal);
    }
    return context.binary(
        binary.operator,
        try priorSort(program, binary.left, term_index),
        try priorValue(values, binary.left, term_index),
        try priorValue(values, binary.right, term_index),
    );
}

fn priorValue(values: []const model_value.Value, term_id: ir.SolverTermId, upper_bound: usize) Error!model_value.Value {
    if (term_id.index() >= upper_bound or term_id.index() >= values.len) return error.InvalidModelInput;
    return values[term_id.index()];
}

fn priorSort(program: *const ir.Program, term_id: ir.SolverTermId, upper_bound: usize) Error!ir.SolverSort {
    if (term_id.index() >= upper_bound or term_id.index() >= program.solver_terms.len) return error.InvalidModelInput;
    return program.solver_terms[term_id.index()].sort;
}

fn expectedGoal(kind: ir.QueryKind) bool {
    return switch (kind) {
        .prove_true, .prove_equivalent => false,
        .prove_false, .prove_unreachable, .find_model => true,
    };
}

pub fn modelValueMatchesSort(value: ir.SolverModelValue, sort: ir.SolverSort) bool {
    return switch (value) {
        .boolean => sort.kind == .boolean,
        .integer => |integer| sort.kind == .integer and numerals.isCanonicalSignedDecimal(integer),
        .real => |real| sort.kind == .real and
            numerals.isCanonicalSignedDecimal(real.numerator) and
            numerals.isCanonicalUnsignedDecimal(real.denominator) and
            !std.mem.eql(u8, real.denominator, "0"),
        .bit_vector => |bit_vector| sort.kind == .bit_vector and
            sort.bit_width == bit_vector.bit_width and
            numerals.unsignedFitsBits(bit_vector.value, bit_vector.bit_width),
        .dynamic_identity => sort.kind == .dynamic_value,
    };
}

pub fn dynamicIdentitiesCanonical(program: *const ir.Program, bindings: []const ir.SolverModelBinding) bool {
    for (bindings) |binding| if (binding.term.index() >= program.solver_terms.len) return false;

    var next_identity: u64 = 0;
    for (program.solver_terms, 0..) |_, term_index| {
        for (bindings) |binding| {
            if (binding.term.index() != term_index) continue;
            const identity = switch (binding.value) {
                .dynamic_identity => |value| @as(u64, value),
                else => continue,
            };
            if (identity > next_identity) return false;
            if (identity == next_identity) next_identity += 1;
        }
    }
    return true;
}

pub const DynamicBindingsCoherence = enum {
    coherent,
    contradictory,
    unrepresentable,
};

pub fn dynamicBindingsCoherence(program: *const ir.Program, bindings: []const ir.SolverModelBinding) DynamicBindingsCoherence {
    if (!truthinessBindingsCoherent(program, bindings) or !nanBindingsCoherent(program, bindings)) return .contradictory;
    var first_boolean_identity: ?u32 = null;
    var second_boolean_identity: ?u32 = null;
    for (bindings, 0..) |binding, binding_index| {
        const identity = switch (binding.value) {
            .dynamic_identity => |value| value,
            else => continue,
        };
        if (binding.term.index() >= program.solver_terms.len) return .contradictory;
        if (solver_equivalence.dynamicTermDescriptor(program, binding.term)) |descriptor| {
            if (descriptor.category == .boolean and
                identity != first_boolean_identity and
                identity != second_boolean_identity)
            {
                if (first_boolean_identity == null) {
                    first_boolean_identity = identity;
                } else if (second_boolean_identity == null) {
                    second_boolean_identity = identity;
                } else {
                    return .contradictory;
                }
            }
        }
        for (bindings[0..binding_index]) |prior| {
            const prior_identity = switch (prior.value) {
                .dynamic_identity => |value| value,
                else => continue,
            };
            if (prior.term.index() >= program.solver_terms.len) return .contradictory;
            if (solver_equivalence.termsEquivalent(program, binding.term, prior.term) and identity != prior_identity) return .contradictory;
            if (solver_equivalence.termsDistinct(program, binding.term, prior.term) and identity == prior_identity) return .contradictory;

            const descriptor = solver_equivalence.dynamicTermDescriptor(program, binding.term) orelse continue;
            const prior_descriptor = solver_equivalence.dynamicTermDescriptor(program, prior.term) orelse continue;
            if (descriptor.category == .number and
                prior_descriptor.category == .number and
                descriptor.exact_number != null and
                prior_descriptor.exact_number != null and
                solver_equivalence.dynamicDescriptorRelation(descriptor, prior_descriptor) == .unresolved)
            {
                return .unrepresentable;
            }
        }
    }
    return .coherent;
}

fn truthinessBindingsCoherent(program: *const ir.Program, bindings: []const ir.SolverModelBinding) bool {
    for (bindings) |binding| {
        const truth = switch (binding.value) {
            .boolean => |value| value,
            else => continue,
        };
        if (binding.term.index() >= program.solver_terms.len) return false;
        const operand = switch (program.solver_terms[binding.term.index()].operation) {
            .dynamic_truthiness => |term_id| term_id,
            else => continue,
        };
        const identity = directDynamicIdentity(bindings, operand) orelse return false;
        if (solver_equivalence.dynamicTermTruthiness(program, operand)) |known| {
            if (known != truth) return false;
        }
        for (bindings) |dynamic_binding| {
            const dynamic_identity = switch (dynamic_binding.value) {
                .dynamic_identity => |value| value,
                else => continue,
            };
            if (dynamic_identity != identity or dynamic_binding.term.index() >= program.solver_terms.len) continue;
            if (solver_equivalence.dynamicTermTruthiness(program, dynamic_binding.term)) |known| {
                if (known != truth) return false;
            }
        }
        for (bindings) |other_binding| {
            const other_truth = switch (other_binding.value) {
                .boolean => |value| value,
                else => continue,
            };
            if (other_binding.term.index() >= program.solver_terms.len) return false;
            const other_operand = switch (program.solver_terms[other_binding.term.index()].operation) {
                .dynamic_truthiness => |term_id| term_id,
                else => continue,
            };
            const other_identity = directDynamicIdentity(bindings, other_operand) orelse return false;
            if (identity == other_identity and truth != other_truth) return false;
        }
    }
    return true;
}

fn nanBindingsCoherent(program: *const ir.Program, bindings: []const ir.SolverModelBinding) bool {
    for (bindings) |binding| {
        const is_nan = switch (binding.value) {
            .boolean => |value| value,
            else => continue,
        };
        if (binding.term.index() >= program.solver_terms.len) return false;
        const operand = switch (program.solver_terms[binding.term.index()].operation) {
            .dynamic_number_is_nan => |term_id| term_id,
            else => continue,
        };
        const identity = directDynamicIdentity(bindings, operand) orelse return false;
        if (solver_equivalence.dynamicTermIsNaN(program, operand)) |known| {
            if (known != is_nan) return false;
        }
        for (bindings) |dynamic_binding| {
            const dynamic_identity = switch (dynamic_binding.value) {
                .dynamic_identity => |value| value,
                else => continue,
            };
            if (dynamic_identity != identity or dynamic_binding.term.index() >= program.solver_terms.len) continue;
            if (solver_equivalence.dynamicTermIsNaN(program, dynamic_binding.term)) |known| {
                if (known != is_nan) return false;
            }
        }
        for (bindings) |other_binding| {
            const other_is_nan = switch (other_binding.value) {
                .boolean => |value| value,
                else => continue,
            };
            if (other_binding.term.index() >= program.solver_terms.len) return false;
            const other_operand = switch (program.solver_terms[other_binding.term.index()].operation) {
                .dynamic_number_is_nan => |term_id| term_id,
                else => continue,
            };
            const other_identity = directDynamicIdentity(bindings, other_operand) orelse return false;
            if (identity == other_identity and is_nan != other_is_nan) return false;
        }
    }
    return true;
}

fn directDynamicIdentity(bindings: []const ir.SolverModelBinding, term_id: ir.SolverTermId) ?u32 {
    var found: ?u32 = null;
    for (bindings) |binding| {
        if (binding.term != term_id) continue;
        const identity = switch (binding.value) {
            .dynamic_identity => |value| value,
            else => return null,
        };
        if (found != null) return null;
        found = identity;
    }
    return found;
}

pub fn dynamicBindingsSemanticallyCoherent(program: *const ir.Program, bindings: []const ir.SolverModelBinding) bool {
    return dynamicBindingsCoherence(program, bindings) == .coherent;
}

// Luau reads an IR integer as a double: within +-2^53 the exact value is Luau's; beyond it the replay
// must not use the mathematical value (the internal evaluator's walk applies the same bound).
fn exactLuauReplayInteger(value: model_value.Value) model_value.Value {
    const limit: i64 = 1 << 53;
    return switch (value) {
        .integer => |integer| if (integer.toConst().orderAgainstScalar(limit) == .gt or
            integer.toConst().orderAgainstScalar(-limit) == .lt) model_value.unknown() else value,
        else => value,
    };
}

const SourceEvaluator = struct {
    program: *const ir.Program,
    context: model_value.Context,

    fn evaluate(self: SourceEvaluator, value_id: ir.ValueId, sort: ir.SolverSort, depth: usize) Error!model_value.Value {
        if (value_id.index() >= self.program.values.len or depth > self.program.values.len + self.program.instructions.len) {
            return error.InvalidModelInput;
        }
        const source = solver.normalizedValueSource(self.program, value_id) orelse return model_value.unknown();
        return switch (source) {
            .constant => |constant| self.literal(constant.literal, sort),
            .copy => |copy| self.evaluate(copy.source, sort, depth + 1),
            .unary => |source_unary| self.unary(source_unary.operator, source_unary.operand, sort, depth + 1),
            .binary => |source_binary| self.binary(source_binary, sort, depth + 1),
        };
    }

    fn literal(self: SourceEvaluator, literal_value: ir.Literal, sort: ir.SolverSort) Error!model_value.Value {
        return switch (literal_value) {
            .boolean => |value| if (sort.kind == .boolean) self.context.booleanValue(value) else model_value.unknown(),
            .integer => |value| switch (sort.kind) {
                .integer => exactLuauReplayInteger(try self.context.integerLiteral(value)),
                .bit_vector => self.context.integerToBitVector(exactLuauReplayInteger(try self.context.integerLiteral(value)), sort.bit_width),
                else => model_value.unknown(),
            },
            .nil_value, .number, .special_number, .string => model_value.unknown(),
        };
    }

    fn unary(
        self: SourceEvaluator,
        operator: ir.UnaryOperator,
        operand: ir.ValueId,
        result_sort: ir.SolverSort,
        depth: usize,
    ) Error!model_value.Value {
        if (result_sort.kind == .boolean) {
            if (solver_equivalence.exactPrimitiveBooleanResult(self.program, .{ .unary = .{
                .operator = operator,
                .operand = operand,
            } })) |value| return self.context.booleanValue(value);
        }
        return switch (operator) {
            .logical_not => if (result_sort.kind == .boolean and self.valueHasScalarSort(operand, .boolean))
                self.context.logicalNot(try self.evaluate(operand, .{ .kind = .boolean }, depth))
            else
                model_value.unknown(),
            .negate => if (result_sort.kind == .integer and self.valueHasScalarSort(operand, .integer))
                self.context.negate(try self.evaluate(operand, .{ .kind = .integer }, depth))
            else
                model_value.unknown(),
            .length => if (result_sort.kind == .integer) blk: {
                const length = normalized_value.exactStringLength(self.program, operand) orelse break :blk model_value.unknown();
                var buffer: [32]u8 = undefined;
                const decimal = std.fmt.bufPrint(&buffer, "{d}", .{length}) catch break :blk model_value.unknown();
                break :blk try self.context.integerLiteral(decimal);
            } else model_value.unknown(),
            .bit_not => model_value.unknown(),
        };
    }

    fn binary(
        self: SourceEvaluator,
        operation: @FieldType(solver.NormalizedValueSource, "binary"),
        result_sort: ir.SolverSort,
        depth: usize,
    ) Error!model_value.Value {
        if (result_sort.kind == .boolean) {
            if (solver_equivalence.exactPrimitiveBooleanResult(self.program, .{ .binary = .{
                .operator = operation.operator,
                .left = operation.left,
                .right = operation.right,
            } })) |value| return self.context.booleanValue(value);
        }
        const operator = normalized_value.solverBinaryOperator(operation.operator) orelse return model_value.unknown();
        const operand_sort = self.normalizedOperandSort(result_sort, operation) orelse return model_value.unknown();
        return exactLuauReplayInteger(try self.context.binary(
            operator,
            operand_sort,
            try self.evaluate(operation.left, operand_sort, depth),
            try self.evaluate(operation.right, operand_sort, depth),
        ));
    }

    fn normalizedOperandSort(
        self: SourceEvaluator,
        result_sort: ir.SolverSort,
        operation: @FieldType(solver.NormalizedValueSource, "binary"),
    ) ?ir.SolverSort {
        const boolean_sort: ir.SolverSort = .{ .kind = .boolean };
        const integer_sort: ir.SolverSort = .{ .kind = .integer };
        return switch (operation.operator) {
            .logical_and, .logical_or => if (result_sort.kind == .boolean and
                self.valueHasScalarSort(operation.left, .boolean) and
                self.valueHasScalarSort(operation.right, .boolean))
                boolean_sort
            else
                null,
            .add, .subtract, .multiply => if (result_sort.kind == .integer and
                self.valueHasScalarSort(operation.left, .integer) and
                self.valueHasScalarSort(operation.right, .integer))
                integer_sort
            else
                null,
            .equal, .not_equal => blk: {
                if (result_sort.kind != .boolean) break :blk null;
                const left = self.scalarSort(operation.left) orelse break :blk null;
                const right = self.scalarSort(operation.right) orelse break :blk null;
                break :blk if (sameSort(left, right)) left else null;
            },
            .less, .less_equal, .greater, .greater_equal => if (result_sort.kind == .boolean and
                self.valueHasScalarSort(operation.left, .integer) and
                self.valueHasScalarSort(operation.right, .integer))
                integer_sort
            else
                null,
            .divide, .floor_divide, .modulo, .power, .concat, .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => null,
        };
    }

    fn scalarSort(self: SourceEvaluator, value_id: ir.ValueId) ?ir.SolverSort {
        if (value_id.index() >= self.program.values.len) return null;
        return switch (self.program.values[value_id.index()].type.kind) {
            .boolean => .{ .kind = .boolean },
            .integer => .{ .kind = .integer },
            else => null,
        };
    }

    fn valueHasScalarSort(self: SourceEvaluator, value_id: ir.ValueId, kind: ir.SolverSortKind) bool {
        const sort = self.scalarSort(value_id) orelse return false;
        return sort.kind == kind;
    }
};

fn sameSort(left: ir.SolverSort, right: ir.SolverSort) bool {
    return left.kind == right.kind and left.bit_width == right.bit_width and left.signed == right.signed;
}
