const std = @import("std");
const ir = @import("ir.zig");
const solver_term = @import("solver_term.zig");
const solver = @import("solver.zig");
const solver_preconditions = @import("solver_preconditions.zig");
const solver_value_definition = @import("solver_value_definition.zig");
const solver_equivalence = @import("solver_equivalence.zig");
const numerals = @import("numerals.zig");
const diagnostics = @import("diagnostics.zig");

pub fn validate(report: *diagnostics.Report, program: *const ir.Program) !void {
    for (program.solver_terms, 0..) |term, term_index| {
        if (!isCanonicalSort(term.sort)) try report.add(.invalid_solver_sort, term_index);
        var dependencies = solver_term.dependencies(term.operation);
        while (dependencies.next()) |operand| try validatePriorTerm(report, program, term_index, operand);
        switch (term.operation) {
            .value => |value_id| {
                if (!validId(value_id, program.values.len)) {
                    try report.add(.invalid_solver_term_reference, term_index);
                } else if (!sortAcceptsValue(term.sort, program.values[value_id.index()].type)) {
                    try report.add(.solver_sort_mismatch, term_index);
                }
            },
            .value_definition => |definition| {
                if (!solver_value_definition.valid(program, term.sort, definition)) {
                    try report.add(.invalid_solver_value_definition, term_index);
                }
            },
            .semantic_atom => |atom| {
                if (!validId(semanticAtomInstruction(atom), program.instructions.len)) {
                    try report.add(.invalid_semantic_atom_reference, term_index);
                }
                if (term.sort.kind != .boolean) try report.add(.solver_sort_mismatch, term_index);
            },
            .dynamic_truthiness => |operand| {
                if (!validDynamicTruthinessOperand(program, operand)) {
                    try report.add(.invalid_dynamic_truthiness_operand, term_index);
                }
                if (term.sort.kind != .boolean) try report.add(.solver_sort_mismatch, term_index);
            },
            .dynamic_number_is_nan => |operand| {
                if (!validDynamicNumberOperand(program, operand)) {
                    try report.add(.invalid_dynamic_number_operand, term_index);
                }
                if (term.sort.kind != .boolean) try report.add(.solver_sort_mismatch, term_index);
            },
            .boolean_literal => if (term.sort.kind != .boolean) try report.add(.solver_sort_mismatch, term_index),
            .integer_literal => |decimal| {
                if (!numerals.isCanonicalSignedDecimal(decimal)) try report.add(.invalid_solver_numeral, term_index);
                if (term.sort.kind != .integer) try report.add(.solver_sort_mismatch, term_index);
            },
            .real_literal => |rational| {
                if (!numerals.isCanonicalSignedDecimal(rational.numerator) or
                    !numerals.isCanonicalUnsignedDecimal(rational.denominator) or
                    std.mem.eql(u8, rational.denominator, "0"))
                {
                    try report.add(.invalid_solver_numeral, term_index);
                }
                if (term.sort.kind != .real) try report.add(.solver_sort_mismatch, term_index);
            },
            .bit_vector_literal => |literal| {
                if (!numerals.unsignedFitsBits(literal.value, literal.bit_width)) {
                    try report.add(.invalid_solver_numeral, term_index);
                }
                if (term.sort.kind != .bit_vector or term.sort.bit_width != literal.bit_width) {
                    try report.add(.solver_sort_mismatch, term_index);
                }
            },
            .logical_not => |operand| {
                if (term.sort.kind != .boolean or !termHasSort(program, operand, .boolean)) try report.add(.solver_sort_mismatch, term_index);
            },
            .binary => |binary| {
                if (!validBinarySort(program, term.sort, binary)) try report.add(.solver_sort_mismatch, term_index);
            },
            .if_then_else => |selection| {
                if (!validIfThenElseSort(program, term.sort, selection)) try report.add(.solver_sort_mismatch, term_index);
            },
            .bit_vector_not => |operand| {
                if (!validBitVectorNotSort(program, term.sort, operand)) try report.add(.solver_sort_mismatch, term_index);
            },
            .bit_vector_extract => |extract| {
                if (!validBitVectorExtractSort(program, term.sort, extract)) try report.add(.solver_sort_mismatch, term_index);
            },
            .bit_vector_concat => |concat| {
                if (!validBitVectorConcatSort(program, term.sort, concat)) try report.add(.solver_sort_mismatch, term_index);
            },
            .bit_vector_extend => |extension| {
                if (!validBitVectorExtendSort(program, term.sort, extension)) try report.add(.solver_sort_mismatch, term_index);
            },
            .bit_vector_rotate => |rotation| {
                if (!validBitVectorRotateSort(program, term.sort, rotation)) try report.add(.solver_sort_mismatch, term_index);
            },
            .integer_to_bit_vector => |operand| {
                if (!termHasSort(program, operand, .integer) or term.sort.kind != .bit_vector) try report.add(.solver_sort_mismatch, term_index);
            },
            .bit_vector_to_integer => |conversion| {
                if (!termHasSort(program, conversion.operand, .bit_vector) or term.sort.kind != .integer) try report.add(.solver_sort_mismatch, term_index);
            },
            .arithmetic_negate => |operand| {
                if (!validArithmeticNegateSort(program, term.sort, operand)) try report.add(.solver_sort_mismatch, term_index);
            },
            .is_nonzero => |operand| {
                if (!validNonzeroSort(program, term.sort, operand)) try report.add(.solver_sort_mismatch, term_index);
            },
            .division => |division| {
                if (!validDivisionSort(program, term.sort, division)) try report.add(.solver_sort_mismatch, term_index);
            },
            .remainder => |remainder| {
                if (!validRemainderSort(program, term.sort, remainder)) try report.add(.solver_sort_mismatch, term_index);
            },
        }
    }
    for (program.queries, 0..) |query, query_index| {
        if (!solver_preconditions.queryCovered(program, query, solver.evaluatesTrue)) try report.add(.solver_precondition_not_assumed, query_index);
    }
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

fn termHasSort(program: *const ir.Program, term_id: ir.SolverTermId, kind: ir.SolverSortKind) bool {
    return validId(term_id, program.solver_terms.len) and program.solver_terms[term_id.index()].sort.kind == kind;
}

fn validDynamicTruthinessOperand(program: *const ir.Program, term_id: ir.SolverTermId) bool {
    if (!termHasSort(program, term_id, .dynamic_value)) return false;
    return program.solver_terms[term_id.index()].operation == .value;
}

fn validDynamicNumberOperand(program: *const ir.Program, term_id: ir.SolverTermId) bool {
    if (!termHasSort(program, term_id, .dynamic_value)) return false;
    if (program.solver_terms[term_id.index()].operation != .value) return false;
    const descriptor = solver_equivalence.dynamicTermDescriptor(program, term_id) orelse return false;
    return descriptor.category == .number;
}

fn sameSort(left: ir.SolverSort, right: ir.SolverSort) bool {
    return left.kind == right.kind and left.bit_width == right.bit_width and left.signed == right.signed;
}

fn isCanonicalSort(sort: ir.SolverSort) bool {
    return switch (sort.kind) {
        .bit_vector => sort.bit_width != 0,
        .boolean, .integer, .real, .dynamic_value => sort.bit_width == 0 and !sort.signed,
    };
}

fn validBinarySort(program: *const ir.Program, result_sort: ir.SolverSort, binary: ir.SolverBinary) bool {
    if (!validId(binary.left, program.solver_terms.len) or !validId(binary.right, program.solver_terms.len)) return false;
    const left = program.solver_terms[binary.left.index()].sort;
    const right = program.solver_terms[binary.right.index()].sort;
    if (!sameSort(left, right)) return false;

    return switch (binary.operator) {
        .equal, .not_equal => result_sort.kind == .boolean,
        .less, .less_equal, .greater, .greater_equal => result_sort.kind == .boolean and switch (left.kind) {
            .integer, .bit_vector, .real => true,
            else => false,
        },
        .logical_and, .logical_or => result_sort.kind == .boolean and left.kind == .boolean,
        .add, .subtract, .multiply => sameSort(result_sort, left) and switch (left.kind) {
            .integer, .bit_vector, .real => true,
            else => false,
        },
        .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => sameSort(result_sort, left) and left.kind == .bit_vector,
    };
}

fn validIfThenElseSort(program: *const ir.Program, result_sort: ir.SolverSort, selection: ir.SolverIfThenElse) bool {
    if (!validId(selection.condition, program.solver_terms.len) or
        !validId(selection.then_term, program.solver_terms.len) or
        !validId(selection.else_term, program.solver_terms.len)) return false;
    const condition = program.solver_terms[selection.condition.index()].sort;
    const then_sort = program.solver_terms[selection.then_term.index()].sort;
    const else_sort = program.solver_terms[selection.else_term.index()].sort;
    return condition.kind == .boolean and
        sameSort(then_sort, else_sort) and
        sameSort(result_sort, then_sort);
}

fn validBitVectorNotSort(program: *const ir.Program, result_sort: ir.SolverSort, operand_id: ir.SolverTermId) bool {
    if (!validId(operand_id, program.solver_terms.len)) return false;
    const operand_sort = program.solver_terms[operand_id.index()].sort;
    return operand_sort.kind == .bit_vector and sameSort(result_sort, operand_sort);
}

fn validBitVectorExtractSort(program: *const ir.Program, result_sort: ir.SolverSort, extract: ir.SolverBitVectorExtract) bool {
    if (!validId(extract.operand, program.solver_terms.len)) return false;
    const operand_sort = program.solver_terms[extract.operand.index()].sort;
    if (operand_sort.kind != .bit_vector or extract.low > extract.high or extract.high >= operand_sort.bit_width) return false;
    const width = @as(u32, extract.high) - @as(u32, extract.low) + 1;
    return result_sort.kind == .bit_vector and @as(u32, result_sort.bit_width) == width;
}

fn validBitVectorConcatSort(program: *const ir.Program, result_sort: ir.SolverSort, concat: ir.SolverBitVectorConcat) bool {
    if (!validId(concat.high, program.solver_terms.len) or !validId(concat.low, program.solver_terms.len)) return false;
    const high_sort = program.solver_terms[concat.high.index()].sort;
    const low_sort = program.solver_terms[concat.low.index()].sort;
    if (high_sort.kind != .bit_vector or low_sort.kind != .bit_vector) return false;
    const width = @as(u32, high_sort.bit_width) + @as(u32, low_sort.bit_width);
    return width <= std.math.maxInt(u16) and
        result_sort.kind == .bit_vector and
        @as(u32, result_sort.bit_width) == width;
}

fn validBitVectorExtendSort(program: *const ir.Program, result_sort: ir.SolverSort, extension: ir.SolverBitVectorExtend) bool {
    if (!validId(extension.operand, program.solver_terms.len) or extension.extra_bits == 0) return false;
    const operand_sort = program.solver_terms[extension.operand.index()].sort;
    if (operand_sort.kind != .bit_vector) return false;
    const width = @as(u32, operand_sort.bit_width) + @as(u32, extension.extra_bits);
    return width <= std.math.maxInt(u16) and
        result_sort.kind == .bit_vector and
        @as(u32, result_sort.bit_width) == width;
}

fn validBitVectorRotateSort(program: *const ir.Program, result_sort: ir.SolverSort, rotation: ir.SolverBitVectorRotate) bool {
    if (!validId(rotation.operand, program.solver_terms.len) or !validId(rotation.amount, program.solver_terms.len)) return false;
    const operand_sort = program.solver_terms[rotation.operand.index()].sort;
    const amount_sort = program.solver_terms[rotation.amount.index()].sort;
    return operand_sort.kind == .bit_vector and
        amount_sort.kind == .bit_vector and
        operand_sort.bit_width == amount_sort.bit_width and
        sameSort(result_sort, operand_sort);
}

fn validArithmeticNegateSort(program: *const ir.Program, result_sort: ir.SolverSort, operand_id: ir.SolverTermId) bool {
    if (!validId(operand_id, program.solver_terms.len)) return false;
    const operand_sort = program.solver_terms[operand_id.index()].sort;
    if (!sameSort(result_sort, operand_sort)) return false;
    return switch (operand_sort.kind) {
        .integer, .real, .bit_vector => true,
        .boolean, .dynamic_value => false,
    };
}

fn validNonzeroSort(program: *const ir.Program, result_sort: ir.SolverSort, operand_id: ir.SolverTermId) bool {
    if (!validId(operand_id, program.solver_terms.len) or result_sort.kind != .boolean) return false;
    return switch (program.solver_terms[operand_id.index()].sort.kind) {
        .integer, .real, .bit_vector => true,
        .boolean, .dynamic_value => false,
    };
}

fn validDivisionSort(program: *const ir.Program, result_sort: ir.SolverSort, division: ir.SolverDivision) bool {
    if (!validId(division.left, program.solver_terms.len) or
        !validId(division.right, program.solver_terms.len) or
        !validId(division.defined_by, program.solver_terms.len)) return false;
    const left_sort = program.solver_terms[division.left.index()].sort;
    const right_sort = program.solver_terms[division.right.index()].sort;
    if (!sameSort(result_sort, left_sort) or !sameSort(left_sort, right_sort)) return false;
    if (!validNonzeroGuard(program, division.right, division.defined_by)) return false;
    return switch (division.mode) {
        .integer_euclidean, .integer_floor => result_sort.kind == .integer,
        .real => result_sort.kind == .real,
        .bit_vector_unsigned => result_sort.kind == .bit_vector and !result_sort.signed,
        .bit_vector_signed => result_sort.kind == .bit_vector and result_sort.signed,
    };
}

fn validRemainderSort(program: *const ir.Program, result_sort: ir.SolverSort, remainder: ir.SolverRemainder) bool {
    if (!validId(remainder.left, program.solver_terms.len) or
        !validId(remainder.right, program.solver_terms.len) or
        !validId(remainder.defined_by, program.solver_terms.len)) return false;
    const left_sort = program.solver_terms[remainder.left.index()].sort;
    const right_sort = program.solver_terms[remainder.right.index()].sort;
    if (!sameSort(result_sort, left_sort) or !sameSort(left_sort, right_sort)) return false;
    if (!validNonzeroGuard(program, remainder.right, remainder.defined_by)) return false;
    return switch (remainder.mode) {
        .integer_euclidean, .integer_floor => result_sort.kind == .integer,
        .bit_vector_unsigned => result_sort.kind == .bit_vector and !result_sort.signed,
        .bit_vector_signed_dividend, .bit_vector_signed_divisor => result_sort.kind == .bit_vector and result_sort.signed,
    };
}

fn validNonzeroGuard(program: *const ir.Program, right: ir.SolverTermId, defined_by: ir.SolverTermId) bool {
    return switch (program.solver_terms[defined_by.index()].operation) {
        .is_nonzero => |operand| operand == right,
        else => false,
    };
}

fn validatePriorTerm(report: *diagnostics.Report, program: *const ir.Program, term_index: usize, operand: ir.SolverTermId) !void {
    if (!validId(operand, program.solver_terms.len)) {
        try report.add(.invalid_solver_term_reference, term_index);
    } else if (operand.index() >= term_index) {
        try report.add(.solver_term_not_topological, term_index);
    }
}

fn semanticAtomInstruction(atom: ir.SemanticAtom) ir.InstructionId {
    return switch (atom) {
        .instruction_effects => |instruction_id| instruction_id,
        .no_metamethod_dispatch => |instruction_id| instruction_id,
        .primitive_operator_domain => |instruction_id| instruction_id,
    };
}

fn validId(id: anytype, len: usize) bool {
    return id.index() < len;
}
