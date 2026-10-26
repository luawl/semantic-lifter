const std = @import("std");
const ir = @import("ir.zig");
const evaluator = @import("solver_evaluator.zig");
const solver_equivalence = @import("solver_equivalence.zig");
const solver_preconditions = @import("solver_preconditions.zig");

pub const BitVectorConstant = evaluator.BitVectorConstant;
pub const Truth = evaluator.Truth;
pub const Constant = evaluator.Constant;
pub const NormalizedValueSource = evaluator.NormalizedValueSource;
pub const normalizedValueSource = evaluator.normalizedValueSource;
pub const isExactPure = evaluator.isExactPure;
pub const evaluate = evaluator.evaluate;
pub const evaluateValue = evaluator.evaluateValue;
pub const evaluateTruth = evaluator.evaluateTruth;
pub const evaluatesTrue = evaluator.evaluatesTrue;

pub fn solve(program: *const ir.Program, query: ir.SolverQuery) ir.SolverResolution {
    if (!solver_preconditions.queryCovered(program, query, evaluatesTrue)) return .unknown;
    var assumptions_are_concrete = true;
    for (query.assumptions) |constraint_id| {
        if (constraint_id.index() >= program.constraints.len) return .unknown;
        switch (evaluateTruth(program, program.constraints[constraint_id.index()].predicate)) {
            .true_value => {},
            .false_value => return if (query.kind == .find_model) .disproved else .proved,
            .unknown => assumptions_are_concrete = false,
        }
    }

    if ((query.kind == .prove_true or query.kind == .prove_equivalent) and queryAssumesGoal(program, query)) return .proved;

    const truth = evaluateTruthWithAssumptions(program, query, query.goal, 0);
    return switch (query.kind) {
        .prove_true, .prove_equivalent => switch (truth) {
            .true_value => .proved,
            .false_value => if (assumptions_are_concrete) .disproved else .unknown,
            .unknown => .unknown,
        },
        .prove_false, .prove_unreachable => switch (truth) {
            .false_value => .proved,
            .true_value => if (assumptions_are_concrete) .disproved else .unknown,
            .unknown => .unknown,
        },
        .find_model => if (!assumptions_are_concrete)
            .unknown
        else switch (truth) {
            .true_value => .proved,
            .false_value => .disproved,
            .unknown => .unknown,
        },
    };
}

fn evaluateTruthWithAssumptions(
    program: *const ir.Program,
    query: ir.SolverQuery,
    term_id: ir.SolverTermId,
    depth: usize,
) Truth {
    if (term_id.index() >= program.solver_terms.len or depth > program.solver_terms.len) return .unknown;
    if (queryAssumesTerm(program, query, term_id)) return .true_value;
    const exact = evaluateTruth(program, term_id);
    if (exact != .unknown) return exact;

    return switch (program.solver_terms[term_id.index()].operation) {
        .value_definition => |definition| evaluateTruthWithAssumptions(program, query, definition.expression, depth + 1),
        .logical_not => |operand| negateTruth(evaluateTruthWithAssumptions(program, query, operand, depth + 1)),
        .binary => |binary| switch (binary.operator) {
            .logical_and => combineTruth(
                evaluateTruthWithAssumptions(program, query, binary.left, depth + 1),
                evaluateTruthWithAssumptions(program, query, binary.right, depth + 1),
                true,
            ),
            .logical_or => combineTruth(
                evaluateTruthWithAssumptions(program, query, binary.left, depth + 1),
                evaluateTruthWithAssumptions(program, query, binary.right, depth + 1),
                false,
            ),
            else => .unknown,
        },
        .if_then_else => |selection| switch (evaluateTruthWithAssumptions(program, query, selection.condition, depth + 1)) {
            .true_value => evaluateTruthWithAssumptions(program, query, selection.then_term, depth + 1),
            .false_value => evaluateTruthWithAssumptions(program, query, selection.else_term, depth + 1),
            .unknown => blk: {
                const then_truth = evaluateTruthWithAssumptions(program, query, selection.then_term, depth + 1);
                const else_truth = evaluateTruthWithAssumptions(program, query, selection.else_term, depth + 1);
                break :blk if (then_truth == else_truth) then_truth else .unknown;
            },
        },
        else => .unknown,
    };
}

fn negateTruth(truth: Truth) Truth {
    return switch (truth) {
        .true_value => .false_value,
        .false_value => .true_value,
        .unknown => .unknown,
    };
}

fn combineTruth(left: Truth, right: Truth, is_and: bool) Truth {
    const decisive: Truth = if (is_and) .false_value else .true_value;
    if (left == decisive or right == decisive) return decisive;
    if (left != .unknown and right != .unknown) return if (is_and) .true_value else .false_value;
    return .unknown;
}

fn queryAssumesGoal(program: *const ir.Program, query: ir.SolverQuery) bool {
    return queryAssumesTerm(program, query, query.goal);
}

fn queryAssumesTerm(program: *const ir.Program, query: ir.SolverQuery, term_id: ir.SolverTermId) bool {
    for (query.assumptions) |constraint_id| {
        if (constraint_id.index() < program.constraints.len and
            solver_equivalence.termsEquivalent(program, program.constraints[constraint_id.index()].predicate, term_id))
        {
            return true;
        }
    }
    return false;
}

test "internal facts replay exact normalized relational definitions" {
    const fixture = @import("fixtures.zig").relational_dispatch_module;
    const t_condition = ir.SolverTermId.fromIndex(fixture.solver_terms.len);
    const t_not_condition = ir.SolverTermId.fromIndex(fixture.solver_terms.len + 1);
    const terms = fixture.solver_terms ++ [_]ir.SolverTerm{
        .{ .id = t_condition, .sort = .{ .kind = .boolean }, .operation = .{ .value = fixture.v_condition } },
        .{ .id = t_not_condition, .sort = .{ .kind = .boolean }, .operation = .{ .logical_not = t_condition } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    var exact_instructions = fixture.instructions;
    exact_instructions[fixture.i_one.index()].operation = .{ .constant = .{ .integer = "7" } };
    exact_instructions[fixture.i_condition.index()].operation = .{ .binary = .{
        .operator = .equal,
        .left = fixture.v_dispatch_state,
        .right = fixture.v_one,
        .mode = .primitive,
    } };
    program.instructions = &exact_instructions;
    const left_match: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{fixture.c_left},
        .goal = t_condition,
    };
    const left_mismatch: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(1),
        .kind = .prove_true,
        .assumptions = &.{fixture.c_left},
        .goal = t_not_condition,
    };
    const right_mismatch: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(2),
        .kind = .prove_true,
        .assumptions = &.{fixture.c_right},
        .goal = t_not_condition,
    };
    try std.testing.expectEqual(ir.SolverResolution.proved, solve(&program, left_match));
    try std.testing.expectEqual(ir.SolverResolution.unknown, solve(&program, left_mismatch));
    try std.testing.expectEqual(ir.SolverResolution.proved, solve(&program, right_mismatch));

    var changed_instructions = exact_instructions;
    changed_instructions[fixture.i_one.index()].operation = .{ .constant = .{ .integer = "8" } };
    program.instructions = &changed_instructions;
    try std.testing.expectEqual(ir.SolverResolution.unknown, solve(&program, left_match));
}

test "internal facts leave affine implications for an external solver" {
    const fixture = @import("fixtures.zig").relational_dispatch_module;
    const t_condition = ir.SolverTermId.fromIndex(fixture.solver_terms.len);
    const t_not_condition = ir.SolverTermId.fromIndex(fixture.solver_terms.len + 1);
    const terms = fixture.solver_terms ++ [_]ir.SolverTerm{
        .{ .id = t_condition, .sort = .{ .kind = .boolean }, .operation = .{ .value = fixture.v_condition } },
        .{ .id = t_not_condition, .sort = .{ .kind = .boolean }, .operation = .{ .logical_not = t_condition } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    const left: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{fixture.c_left},
        .goal = t_condition,
    };
    const right: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(1),
        .kind = .prove_true,
        .assumptions = &.{fixture.c_right},
        .goal = t_not_condition,
    };
    try std.testing.expectEqual(ir.SolverResolution.unknown, solve(&program, left));
    try std.testing.expectEqual(ir.SolverResolution.unknown, solve(&program, right));
}

test "internal fact engine proves normalized constant predicates" {
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "9" } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "4" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .integer }, .operation = .{ .binary = .{ .operator = .subtract, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "5" } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = ir.SolverTermId.fromIndex(2), .right = ir.SolverTermId.fromIndex(3) } } },
    };
    const functions = [_]ir.Function{};
    const program: ir.Program = .{
        .program_id = "solver-fixture",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &functions,
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
    try @import("std").testing.expectEqual(ir.SolverResolution.proved, solve(&program, query));
}

test "exact IR constant values normalize into solver facts" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "2" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    try std.testing.expectEqual(Constant{ .integer = 2 }, evaluateValue(&program, fixture.v_factor));
    try std.testing.expectEqual(Truth.true_value, evaluateTruth(&program, ir.SolverTermId.fromIndex(2)));
}

test "internal facts evaluate explicit dynamic truthiness" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const v_nil = ir.ValueId.fromIndex(0);
    const v_false = ir.ValueId.fromIndex(1);
    const v_string = ir.ValueId.fromIndex(2);
    const v_table = ir.ValueId.fromIndex(3);
    const v_unknown = ir.ValueId.fromIndex(4);
    const v_copy = ir.ValueId.fromIndex(5);
    const values = [_]ir.Value{
        .{ .id = v_nil, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = v_false, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = v_string, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = v_table, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = v_unknown, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = v_copy, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = block_id, .operation = .{ .constant = .{ .nil_value = {} } }, .results = &.{v_nil}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = block_id, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{v_false}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = block_id, .operation = .{ .constant = .{ .string = "value" } }, .results = &.{v_string}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = block_id, .operation = .{ .make_table = {} }, .results = &.{v_table}, .effects = .table_constructor },
        .{ .id = ir.InstructionId.fromIndex(4), .block = block_id, .operation = .{ .copy = v_string }, .results = &.{v_copy}, .effects = .pure },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_nil } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_false } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(2) } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_string } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(4) } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_table } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(6) } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_unknown } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(8) } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_copy } },
        .{ .id = ir.SolverTermId.fromIndex(11), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(10) } },
    };
    const program: ir.Program = .{
        .program_id = "internal-dynamic-truthiness",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };
    try std.testing.expectEqual(Truth.false_value, evaluateTruth(&program, ir.SolverTermId.fromIndex(1)));
    try std.testing.expectEqual(Truth.false_value, evaluateTruth(&program, ir.SolverTermId.fromIndex(3)));
    try std.testing.expectEqual(Truth.true_value, evaluateTruth(&program, ir.SolverTermId.fromIndex(5)));
    try std.testing.expectEqual(Truth.true_value, evaluateTruth(&program, ir.SolverTermId.fromIndex(7)));
    try std.testing.expectEqual(Truth.unknown, evaluateTruth(&program, ir.SolverTermId.fromIndex(9)));
    try std.testing.expectEqual(Truth.true_value, evaluateTruth(&program, ir.SolverTermId.fromIndex(11)));
}

test "internal facts evaluate dynamic numeric NaN domains" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var values = fixture.values;
    values[fixture.v_left.index()].type = .number;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_number_is_nan = ir.SolverTermId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_left } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_number_is_nan = ir.SolverTermId.fromIndex(2) } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_right } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_number_is_nan = ir.SolverTermId.fromIndex(4) } },
    };
    var program = fixture.program;
    program.values = &values;
    program.solver_terms = &terms;

    try std.testing.expectEqual(Truth.false_value, evaluateTruth(&program, ir.SolverTermId.fromIndex(1)));
    try std.testing.expectEqual(Truth.unknown, evaluateTruth(&program, ir.SolverTermId.fromIndex(3)));
    try std.testing.expectEqual(Truth.false_value, evaluateTruth(&program, ir.SolverTermId.fromIndex(5)));
}

test "internal Boolean facts preserve decisive values with unknown operands" {
    const unknown_value = ir.ValueId.fromIndex(0);
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .value = unknown_value } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = false } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .logical_and, .left = ir.SolverTermId.fromIndex(1), .right = ir.SolverTermId.fromIndex(0) } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .logical_and, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .logical_or, .left = ir.SolverTermId.fromIndex(2), .right = ir.SolverTermId.fromIndex(0) } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .logical_or, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(2) } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .logical_and, .left = ir.SolverTermId.fromIndex(2), .right = ir.SolverTermId.fromIndex(0) } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .logical_or, .left = ir.SolverTermId.fromIndex(1), .right = ir.SolverTermId.fromIndex(0) } } },
    };
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
    }};
    const program: ir.Program = .{
        .program_id = "internal-three-valued-booleans",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{.{
            .id = unknown_value,
            .function = ir.FunctionId.fromIndex(0),
            .type = .boolean,
            .origin = .{ .parameter = 0 },
        }},
        .solver_terms = &terms,
        .constraints = &constraints,
    };

    for (3..5) |term_index| try std.testing.expectEqual(Truth.false_value, evaluateTruth(&program, ir.SolverTermId.fromIndex(term_index)));
    for (5..7) |term_index| try std.testing.expectEqual(Truth.true_value, evaluateTruth(&program, ir.SolverTermId.fromIndex(term_index)));
    for (7..9) |term_index| try std.testing.expectEqual(Truth.unknown, evaluateTruth(&program, ir.SolverTermId.fromIndex(term_index)));

    const unassumed: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(7) };
    try std.testing.expectEqual(ir.SolverResolution.unknown, solve(&program, unassumed));
    var assumed = unassumed;
    assumed.assumptions = &.{ir.ConstraintId.fromIndex(0)};
    try std.testing.expectEqual(ir.SolverResolution.proved, solve(&program, assumed));
}

test "dynamic logical selection is not evaluated as a Boolean connective" {
    const x = ir.ValueId.fromIndex(0);
    const yes = ir.ValueId.fromIndex(1);
    const no = ir.ValueId.fromIndex(2);
    const or_true = ir.ValueId.fromIndex(3);
    const and_false = ir.ValueId.fromIndex(4);
    const is_true = ir.ValueId.fromIndex(5);
    const is_false = ir.ValueId.fromIndex(6);
    const values = [_]ir.Value{
        .{ .id = x, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = yes, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = no, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = or_true, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = and_false, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = is_true, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = is_false, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .boolean = true } }, .results = &.{yes}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .boolean = false } }, .results = &.{no}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .logical_or, .left = x, .right = yes } }, .results = &.{or_true}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .logical_and, .left = x, .right = no } }, .results = &.{and_false}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .equal, .left = or_true, .right = yes } }, .results = &.{is_true}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(5), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .equal, .left = and_false, .right = no } }, .results = &.{is_false}, .effects = .pure },
    };
    const program: ir.Program = .{
        .program_id = "dynamic-logical-selection-evaluation",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };

    // `x or true` and `x and false` select a value from a non-boolean operand, so the walk must not decide the
    // surrounding equality as if the result were a Boolean connective. Before the gate both are decided true.
    const is_true_result = evaluateValue(&program, is_true);
    try std.testing.expect(!(is_true_result == .boolean and is_true_result.boolean));
    const is_false_result = evaluateValue(&program, is_false);
    try std.testing.expect(!(is_false_result == .boolean and is_false_result.boolean));
}

test "internal integer arithmetic never wraps beyond its exact range" {
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "9223372036854775807" } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "1" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .integer }, .operation = .{ .binary = .{
            .operator = .add,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "checked-integer-facts",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &terms,
    };
    try std.testing.expect(evaluate(&program, ir.SolverTermId.fromIndex(2)) == .unknown);
}

test "internal facts evaluate concrete and equal-arm conditional selections" {
    const condition_value = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = condition_value,
        .function = ir.FunctionId.fromIndex(0),
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "7" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "9" } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .integer }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(0),
            .then_term = ir.SolverTermId.fromIndex(1),
            .else_term = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .value = condition_value } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .integer }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(4),
            .then_term = ir.SolverTermId.fromIndex(1),
            .else_term = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .integer }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(4),
            .then_term = ir.SolverTermId.fromIndex(1),
            .else_term = ir.SolverTermId.fromIndex(2),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "internal-if-then-else",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
    };

    try std.testing.expectEqual(@as(i64, 7), evaluate(&program, ir.SolverTermId.fromIndex(3)).integer);
    try std.testing.expectEqual(@as(i64, 7), evaluate(&program, ir.SolverTermId.fromIndex(5)).integer);
    try std.testing.expect(evaluate(&program, ir.SolverTermId.fromIndex(6)) == .unknown);
}

test "internal facts evaluate bounded bit-vector structure exactly" {
    const bv4: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 4 };
    const bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8 };
    const bv128: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 128 };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv8, .operation = .{ .bit_vector_literal = .{ .value = "165", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv8, .operation = .{ .bit_vector_not = ir.SolverTermId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = bv4, .operation = .{ .bit_vector_extract = .{
            .operand = ir.SolverTermId.fromIndex(0),
            .high = 5,
            .low = 2,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = bv4, .operation = .{ .bit_vector_literal = .{ .value = "3", .bit_width = 4 } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = bv8, .operation = .{ .bit_vector_concat = .{
            .high = ir.SolverTermId.fromIndex(2),
            .low = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = bv8, .operation = .{ .bit_vector_extend = .{
            .operand = ir.SolverTermId.fromIndex(2),
            .extra_bits = 4,
            .mode = .zero,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = bv8, .operation = .{ .bit_vector_extend = .{
            .operand = ir.SolverTermId.fromIndex(2),
            .extra_bits = 4,
            .mode = .sign,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = bv8, .operation = .{ .bit_vector_literal = .{ .value = "1", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = bv8, .operation = .{ .bit_vector_rotate = .{
            .operand = ir.SolverTermId.fromIndex(0),
            .amount = ir.SolverTermId.fromIndex(7),
            .direction = .left,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = bv8, .operation = .{ .bit_vector_rotate = .{
            .operand = ir.SolverTermId.fromIndex(0),
            .amount = ir.SolverTermId.fromIndex(7),
            .direction = .right,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = bv128, .operation = .{ .bit_vector_literal = .{ .value = "0", .bit_width = 128 } } },
        .{ .id = ir.SolverTermId.fromIndex(11), .sort = bv128, .operation = .{ .bit_vector_not = ir.SolverTermId.fromIndex(10) } },
        .{ .id = ir.SolverTermId.fromIndex(12), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "-1" } },
        .{ .id = ir.SolverTermId.fromIndex(13), .sort = bv8, .operation = .{ .integer_to_bit_vector = ir.SolverTermId.fromIndex(12) } },
        .{ .id = ir.SolverTermId.fromIndex(14), .sort = .{ .kind = .integer }, .operation = .{ .bit_vector_to_integer = .{
            .operand = ir.SolverTermId.fromIndex(13),
            .signed = true,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(15), .sort = .{ .kind = .integer }, .operation = .{ .bit_vector_to_integer = .{
            .operand = ir.SolverTermId.fromIndex(13),
            .signed = false,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(16), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "260" } },
        .{ .id = ir.SolverTermId.fromIndex(17), .sort = bv8, .operation = .{ .integer_to_bit_vector = ir.SolverTermId.fromIndex(16) } },
        .{ .id = ir.SolverTermId.fromIndex(18), .sort = bv8, .operation = .{ .arithmetic_negate = ir.SolverTermId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(19), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "7" } },
        .{ .id = ir.SolverTermId.fromIndex(20), .sort = .{ .kind = .integer }, .operation = .{ .arithmetic_negate = ir.SolverTermId.fromIndex(19) } },
        .{ .id = ir.SolverTermId.fromIndex(21), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "-9223372036854775808" } },
        .{ .id = ir.SolverTermId.fromIndex(22), .sort = .{ .kind = .integer }, .operation = .{ .arithmetic_negate = ir.SolverTermId.fromIndex(21) } },
        .{ .id = ir.SolverTermId.fromIndex(23), .sort = bv8, .operation = .{ .binary = .{
            .operator = .add,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(13),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(24), .sort = bv8, .operation = .{ .binary = .{
            .operator = .subtract,
            .left = ir.SolverTermId.fromIndex(7),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(25), .sort = bv8, .operation = .{ .binary = .{
            .operator = .multiply,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "internal-bit-vector-structure",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &terms,
    };

    const inverted = evaluate(&program, ir.SolverTermId.fromIndex(1)).bit_vector;
    try std.testing.expectEqual(@as(u64, 90), inverted.value);
    try std.testing.expectEqual(@as(u16, 8), inverted.bit_width);
    const extracted = evaluate(&program, ir.SolverTermId.fromIndex(2)).bit_vector;
    try std.testing.expectEqual(@as(u64, 9), extracted.value);
    try std.testing.expectEqual(@as(u16, 4), extracted.bit_width);
    try std.testing.expectEqual(@as(u64, 147), evaluate(&program, ir.SolverTermId.fromIndex(4)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 9), evaluate(&program, ir.SolverTermId.fromIndex(5)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 249), evaluate(&program, ir.SolverTermId.fromIndex(6)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 75), evaluate(&program, ir.SolverTermId.fromIndex(8)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 210), evaluate(&program, ir.SolverTermId.fromIndex(9)).bit_vector.value);
    try std.testing.expect(evaluate(&program, ir.SolverTermId.fromIndex(11)) == .unknown);
    try std.testing.expectEqual(@as(u64, 255), evaluate(&program, ir.SolverTermId.fromIndex(13)).bit_vector.value);
    try std.testing.expectEqual(@as(i64, -1), evaluate(&program, ir.SolverTermId.fromIndex(14)).integer);
    try std.testing.expectEqual(@as(i64, 255), evaluate(&program, ir.SolverTermId.fromIndex(15)).integer);
    try std.testing.expectEqual(@as(u64, 4), evaluate(&program, ir.SolverTermId.fromIndex(17)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 91), evaluate(&program, ir.SolverTermId.fromIndex(18)).bit_vector.value);
    try std.testing.expectEqual(@as(i64, -7), evaluate(&program, ir.SolverTermId.fromIndex(20)).integer);
    try std.testing.expect(evaluate(&program, ir.SolverTermId.fromIndex(22)) == .unknown);
    try std.testing.expectEqual(@as(u64, 164), evaluate(&program, ir.SolverTermId.fromIndex(23)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 92), evaluate(&program, ir.SolverTermId.fromIndex(24)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 89), evaluate(&program, ir.SolverTermId.fromIndex(25)).bit_vector.value);
}

test "internal bit-vector ordering and shifts preserve signedness and oversized counts" {
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
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "128", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "1", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = signed_bv8, .operation = .{ .binary = .{
            .operator = .shift_right,
            .left = ir.SolverTermId.fromIndex(3),
            .right = ir.SolverTermId.fromIndex(4),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = unsigned_bv8, .operation = .{ .bit_vector_literal = .{ .value = "8", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = unsigned_bv8, .operation = .{ .binary = .{
            .operator = .shift_right,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(6),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "8", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = signed_bv8, .operation = .{ .binary = .{
            .operator = .shift_right,
            .left = ir.SolverTermId.fromIndex(3),
            .right = ir.SolverTermId.fromIndex(8),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = boolean, .operation = .{ .binary = .{
            .operator = .less,
            .left = ir.SolverTermId.fromIndex(3),
            .right = ir.SolverTermId.fromIndex(4),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(11), .sort = boolean, .operation = .{ .binary = .{
            .operator = .less,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "internal-signed-bit-vector-operations",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &terms,
    };

    try std.testing.expectEqual(@as(u64, 64), evaluate(&program, ir.SolverTermId.fromIndex(2)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 192), evaluate(&program, ir.SolverTermId.fromIndex(5)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 0), evaluate(&program, ir.SolverTermId.fromIndex(7)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 255), evaluate(&program, ir.SolverTermId.fromIndex(9)).bit_vector.value);
    try std.testing.expectEqual(Truth.true_value, evaluateTruth(&program, ir.SolverTermId.fromIndex(10)));
    try std.testing.expectEqual(Truth.false_value, evaluateTruth(&program, ir.SolverTermId.fromIndex(11)));
}

test "internal facts evaluate guarded explicit division modes" {
    const boolean: ir.SolverSort = .{ .kind = .boolean };
    const integer: ir.SolverSort = .{ .kind = .integer };
    const unsigned_bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8 };
    const signed_bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8, .signed = true };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = integer, .operation = .{ .integer_literal = "-5" } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = integer, .operation = .{ .integer_literal = "2" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = boolean, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(1) } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = integer, .operation = .{ .division = .{
            .mode = .integer_euclidean,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
            .defined_by = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = integer, .operation = .{ .integer_literal = "5" } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = integer, .operation = .{ .integer_literal = "-2" } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = boolean, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(5) } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = integer, .operation = .{ .division = .{
            .mode = .integer_euclidean,
            .left = ir.SolverTermId.fromIndex(4),
            .right = ir.SolverTermId.fromIndex(5),
            .defined_by = ir.SolverTermId.fromIndex(6),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = unsigned_bv8, .operation = .{ .bit_vector_literal = .{ .value = "255", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = unsigned_bv8, .operation = .{ .bit_vector_literal = .{ .value = "2", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = boolean, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(9) } },
        .{ .id = ir.SolverTermId.fromIndex(11), .sort = unsigned_bv8, .operation = .{ .division = .{
            .mode = .bit_vector_unsigned,
            .left = ir.SolverTermId.fromIndex(8),
            .right = ir.SolverTermId.fromIndex(9),
            .defined_by = ir.SolverTermId.fromIndex(10),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(12), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "251", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(13), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "2", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(14), .sort = boolean, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(13) } },
        .{ .id = ir.SolverTermId.fromIndex(15), .sort = signed_bv8, .operation = .{ .division = .{
            .mode = .bit_vector_signed,
            .left = ir.SolverTermId.fromIndex(12),
            .right = ir.SolverTermId.fromIndex(13),
            .defined_by = ir.SolverTermId.fromIndex(14),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(16), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "128", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(17), .sort = signed_bv8, .operation = .{ .bit_vector_literal = .{ .value = "255", .bit_width = 8 } } },
        .{ .id = ir.SolverTermId.fromIndex(18), .sort = boolean, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(17) } },
        .{ .id = ir.SolverTermId.fromIndex(19), .sort = signed_bv8, .operation = .{ .division = .{
            .mode = .bit_vector_signed,
            .left = ir.SolverTermId.fromIndex(16),
            .right = ir.SolverTermId.fromIndex(17),
            .defined_by = ir.SolverTermId.fromIndex(18),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(20), .sort = integer, .operation = .{ .integer_literal = "0" } },
        .{ .id = ir.SolverTermId.fromIndex(21), .sort = boolean, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(20) } },
        .{ .id = ir.SolverTermId.fromIndex(22), .sort = integer, .operation = .{ .division = .{
            .mode = .integer_euclidean,
            .left = ir.SolverTermId.fromIndex(4),
            .right = ir.SolverTermId.fromIndex(20),
            .defined_by = ir.SolverTermId.fromIndex(21),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(23), .sort = integer, .operation = .{ .remainder = .{
            .mode = .integer_euclidean,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
            .defined_by = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(24), .sort = integer, .operation = .{ .remainder = .{
            .mode = .integer_floor,
            .left = ir.SolverTermId.fromIndex(4),
            .right = ir.SolverTermId.fromIndex(5),
            .defined_by = ir.SolverTermId.fromIndex(6),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(25), .sort = unsigned_bv8, .operation = .{ .remainder = .{
            .mode = .bit_vector_unsigned,
            .left = ir.SolverTermId.fromIndex(8),
            .right = ir.SolverTermId.fromIndex(9),
            .defined_by = ir.SolverTermId.fromIndex(10),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(26), .sort = signed_bv8, .operation = .{ .remainder = .{
            .mode = .bit_vector_signed_dividend,
            .left = ir.SolverTermId.fromIndex(12),
            .right = ir.SolverTermId.fromIndex(13),
            .defined_by = ir.SolverTermId.fromIndex(14),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(27), .sort = signed_bv8, .operation = .{ .remainder = .{
            .mode = .bit_vector_signed_divisor,
            .left = ir.SolverTermId.fromIndex(12),
            .right = ir.SolverTermId.fromIndex(13),
            .defined_by = ir.SolverTermId.fromIndex(14),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(28), .sort = integer, .operation = .{ .remainder = .{
            .mode = .integer_euclidean,
            .left = ir.SolverTermId.fromIndex(4),
            .right = ir.SolverTermId.fromIndex(20),
            .defined_by = ir.SolverTermId.fromIndex(21),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(29), .sort = integer, .operation = .{ .division = .{
            .mode = .integer_floor,
            .left = ir.SolverTermId.fromIndex(4),
            .right = ir.SolverTermId.fromIndex(5),
            .defined_by = ir.SolverTermId.fromIndex(6),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "internal-guarded-division",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &terms,
    };

    try std.testing.expectEqual(@as(i64, -3), evaluate(&program, ir.SolverTermId.fromIndex(3)).integer);
    try std.testing.expectEqual(@as(i64, -2), evaluate(&program, ir.SolverTermId.fromIndex(7)).integer);
    try std.testing.expectEqual(@as(u64, 127), evaluate(&program, ir.SolverTermId.fromIndex(11)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 254), evaluate(&program, ir.SolverTermId.fromIndex(15)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 128), evaluate(&program, ir.SolverTermId.fromIndex(19)).bit_vector.value);
    try std.testing.expect(evaluate(&program, ir.SolverTermId.fromIndex(22)) == .unknown);
    try std.testing.expectEqual(@as(i64, 1), evaluate(&program, ir.SolverTermId.fromIndex(23)).integer);
    try std.testing.expectEqual(@as(i64, -1), evaluate(&program, ir.SolverTermId.fromIndex(24)).integer);
    try std.testing.expectEqual(@as(u64, 1), evaluate(&program, ir.SolverTermId.fromIndex(25)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 255), evaluate(&program, ir.SolverTermId.fromIndex(26)).bit_vector.value);
    try std.testing.expectEqual(@as(u64, 1), evaluate(&program, ir.SolverTermId.fromIndex(27)).bit_vector.value);
    try std.testing.expect(evaluate(&program, ir.SolverTermId.fromIndex(28)) == .unknown);
    try std.testing.expectEqual(@as(i64, -3), evaluate(&program, ir.SolverTermId.fromIndex(29)).integer);
}

test "raw internal solving enforces semantic preconditions" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const integer: ir.SolverSort = .{ .kind = .integer };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = integer, .operation = .{ .value = fixture.v_left } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = integer, .operation = .{ .division = .{
            .mode = .integer_floor,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
            .defined_by = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(2),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
    };
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(1),
        .evidence = &.{fixture.proof},
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    var query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(3),
    };

    try std.testing.expectEqual(ir.SolverResolution.unknown, solve(&program, query));
    query.assumptions = &.{ir.ConstraintId.fromIndex(0)};
    try std.testing.expectEqual(ir.SolverResolution.proved, solve(&program, query));
}

test "exact primitive IR expression chains normalize without solver-term duplication" {
    const fixture = @import("fixtures.zig").arithmetic_module;
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
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    try std.testing.expectEqual(Constant{ .integer = 8 }, evaluateValue(&program, fixture.v_result));
    try std.testing.expectEqual(Truth.true_value, evaluateTruth(&program, ir.SolverTermId.fromIndex(2)));
}

test "IR integer arithmetic never contradicts Luau doubles beyond 2^53" {
    const two53 = ir.ValueId.fromIndex(0);
    const one = ir.ValueId.fromIndex(1);
    const wide = ir.ValueId.fromIndex(2);
    const sum = ir.ValueId.fromIndex(3);
    const rounds_back = ir.ValueId.fromIndex(4);
    const grew = ir.ValueId.fromIndex(5);
    const same_double = ir.ValueId.fromIndex(6);
    const small = ir.ValueId.fromIndex(7);
    const number_base = ir.ValueId.fromIndex(8);
    const number_four = ir.ValueId.fromIndex(9);
    const number_sum = ir.ValueId.fromIndex(10);
    const number_wide = ir.ValueId.fromIndex(11);
    const number_sum_equal = ir.ValueId.fromIndex(12);
    const number_high = ir.ValueId.fromIndex(13);
    const number_low = ir.ValueId.fromIndex(14);
    const number_literal_equal = ir.ValueId.fromIndex(15);
    const values = [_]ir.Value{
        .{ .id = two53, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = one, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = wide, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = sum, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = rounds_back, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = grew, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
        .{ .id = same_double, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(6), .index = 0 } } },
        .{ .id = small, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(7), .index = 0 } } },
        .{ .id = number_base, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(8), .index = 0 } } },
        .{ .id = number_four, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(9), .index = 0 } } },
        .{ .id = number_sum, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(10), .index = 0 } } },
        .{ .id = number_wide, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(11), .index = 0 } } },
        .{ .id = number_sum_equal, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(12), .index = 0 } } },
        .{ .id = number_high, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(13), .index = 0 } } },
        .{ .id = number_low, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(14), .index = 0 } } },
        .{ .id = number_literal_equal, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(15), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "9007199254740992" } }, .results = &.{two53}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{one}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "9007199254740993" } }, .results = &.{wide}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .add, .left = two53, .right = one } }, .results = &.{sum}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .equal, .left = sum, .right = two53 } }, .results = &.{rounds_back}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(5), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .less, .left = two53, .right = sum } }, .results = &.{grew}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(6), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .equal, .left = wide, .right = two53 } }, .results = &.{same_double}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(7), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .add, .left = one, .right = one } }, .results = &.{small}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(8), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "9007199254740991" } }, .results = &.{number_base}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(9), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "4" } }, .results = &.{number_four}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(10), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .add, .left = number_base, .right = number_four } }, .results = &.{number_sum}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(11), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "9007199254740996" } }, .results = &.{number_wide}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(12), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .equal, .left = number_sum, .right = number_wide } }, .results = &.{number_sum_equal}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(13), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "9007199254740993" } }, .results = &.{number_high}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(14), .block = ir.BlockId.fromIndex(0), .operation = .{ .constant = .{ .integer = "9007199254740992" } }, .results = &.{number_low}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(15), .block = ir.BlockId.fromIndex(0), .operation = .{ .binary = .{ .operator = .equal, .left = number_high, .right = number_low } }, .results = &.{number_literal_equal}, .effects = .pure },
    };
    const program: ir.Program = .{
        .program_id = "ir-integer-arithmetic-versus-luau-doubles",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };

    // An integer payload beyond 2^53 anywhere in the walk must read as unknown, for every value type, so the
    // resolver never decides a branch against Luau's double arithmetic. Before the bound these are decided wrong.
    const rounds_back_result = evaluateValue(&program, rounds_back);
    try std.testing.expect(!(rounds_back_result == .boolean and !rounds_back_result.boolean));
    const grew_result = evaluateValue(&program, grew);
    try std.testing.expect(!(grew_result == .boolean and grew_result.boolean));
    const same_double_result = evaluateValue(&program, same_double);
    try std.testing.expect(!(same_double_result == .boolean and !same_double_result.boolean));
    const number_sum_result = evaluateValue(&program, number_sum_equal);
    try std.testing.expect(!(number_sum_result == .boolean and !number_sum_result.boolean));
    const number_literal_result = evaluateValue(&program, number_literal_equal);
    try std.testing.expect(!(number_literal_result == .boolean and !number_literal_result.boolean));
    const small_result = evaluateValue(&program, small);
    try std.testing.expect(small_result == .integer and small_result.integer == 2);
}

test "partial source modulo does not enter the total solver binary theory" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .modulo,
        .left = fixture.v_sum,
        .right = fixture.v_factor,
    } };
    var program = fixture.program;
    program.instructions = &instructions;

    try std.testing.expectEqual(@as(?NormalizedValueSource, null), normalizedValueSource(&program, fixture.v_result));
}

test "internal backend treats contradictory assumptions as unsatisfiable" {
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = false } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
    };
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
    }};
    const program: ir.Program = .{
        .program_id = "contradictory-assumptions",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &terms,
        .constraints = &constraints,
    };
    const proof_query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(1),
    };
    const model_query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(1),
        .kind = .find_model,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(1),
    };
    try @import("std").testing.expectEqual(ir.SolverResolution.proved, solve(&program, proof_query));
    try @import("std").testing.expectEqual(ir.SolverResolution.disproved, solve(&program, model_query));
}

test "internal fact engine distinguishes atoms from explicit hypotheses" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .semantic_atom = .{ .instruction_effects = fixture.i_sum } },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;

    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(0),
    };
    try @import("std").testing.expectEqual(Truth.unknown, evaluateTruth(&program, query.goal));
    try @import("std").testing.expectEqual(ir.SolverResolution.proved, solve(&program, query));

    var unassumed = query;
    unassumed.assumptions = &.{};
    try @import("std").testing.expectEqual(ir.SolverResolution.unknown, solve(&program, unassumed));
}

test "internal facts preserve fresh table and thread allocation identity" {
    const fixture = @import("fixtures.zig").fresh_reference_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_table_a } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_table_b } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_table_copy } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_thread_a } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_thread_b } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(3),
            .right = ir.SolverTermId.fromIndex(4),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    try std.testing.expectEqual(ir.SolverResolution.proved, solve(&program, .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_false,
        .goal = ir.SolverTermId.fromIndex(5),
    }));
    try std.testing.expectEqual(ir.SolverResolution.proved, solve(&program, .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(6),
    }));
    try std.testing.expectEqual(ir.SolverResolution.proved, solve(&program, .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_false,
        .goal = ir.SolverTermId.fromIndex(7),
    }));
    try std.testing.expectEqual(ir.SolverResolution.proved, solve(&program, .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(8),
    }));
}

test "internal facts preserve canonical function reference identity" {
    const fixture = @import("fixtures.zig").function_reference_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_left_a } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_left_b } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_left_copy } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_right } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(3),
        } } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    try std.testing.expectEqual(ir.SolverResolution.proved, solve(&program, .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(4),
    }));
    try std.testing.expectEqual(ir.SolverResolution.proved, solve(&program, .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(5),
    }));
    try std.testing.expectEqual(ir.SolverResolution.proved, solve(&program, .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_false,
        .goal = ir.SolverTermId.fromIndex(6),
    }));
    try std.testing.expectEqual(ir.SolverResolution.proved, solve(&program, .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(7),
    }));
}
