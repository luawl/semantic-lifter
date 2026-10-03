const std = @import("std");
const lifter = @import("semantic_lifter");
const ir = lifter.ir;
const validation = lifter.validate;

test "branch conditions admit every scalar Luau truthiness domain" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const then_id = ir.BlockId.fromIndex(1);
    const else_id = ir.BlockId.fromIndex(2);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = then_id },
            .else_edge = .{ .target = else_id },
        } } },
        .{ .id = then_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = else_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry_id, then_id, else_id },
        .entry_block = entry_id,
    }};
    const admitted_types = [_]ir.ValueType{
        .dynamic,
        .{ .kind = .nil_value },
        .boolean,
        .integer,
        .number,
        .string,
        .{ .kind = .table },
        .function,
        .{ .kind = .thread },
        .{ .kind = .userdata },
    };
    for (admitted_types) |value_type| {
        const values = [_]ir.Value{.{ .id = condition, .function = function_id, .type = value_type, .origin = .{ .parameter = 0 } }};
        const program: ir.Program = .{
            .program_id = "scalar-branch-truthiness",
            .entry_function = function_id,
            .functions = &functions,
            .blocks = &blocks,
            .instructions = &.{},
            .values = &values,
        };
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(!report.contains(.invalid_branch_condition));
    }

    const tuple_values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .{ .kind = .tuple },
        .origin = .{ .parameter = 0 },
    }};
    const tuple_program: ir.Program = .{
        .program_id = "tuple-branch-condition",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &tuple_values,
    };
    var tuple_report = try validation.validate(std.testing.allocator, &tuple_program, .core);
    defer tuple_report.deinit();
    try std.testing.expect(tuple_report.contains(.invalid_branch_condition));
}

test "readable profile rejects unknown effects and open obligations" {
    const value_id = ir.ValueId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const function_id = ir.FunctionId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = value_id,
        .function = function_id,
        .type = .integer,
        .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } },
    }};
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = block_id,
        .operation = .{ .constant = .{ .integer = "1" } },
        .results = &.{value_id},
        .effects = .{},
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{instruction_id},
        .terminator = .{ .return_values = &.{value_id} },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .unknown_effects,
        .subject = .{ .instruction = instruction_id },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "frontend did not prove effects",
    }};
    const program: ir.Program = .{
        .program_id = "profile-fixture",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .obligations = &obligations,
    };

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.contains(.unknown_effects));
    try std.testing.expect(readable_report.contains(.open_profile_obligation));
    try std.testing.expect(readable_report.contains(.missing_emission_evidence));
}

test "discharged obligations require a matching proved certificate" {
    const fixture = lifter.fixtures.arithmetic_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const queries = [_]ir.SolverQuery{
        .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(0) },
        .{ .id = ir.QueryId.fromIndex(1), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(0) },
    };
    const certificates = [_]ir.SolverCertificate{.{
        .id = ir.CertificateId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .engine = .imported,
        .resolution = .proved,
        .evidence = &.{fixture.proof},
        .certificate_digest = "fixture:matching-obligation-proof",
    }};
    var obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .numeric_domain,
        .subject = .{ .program = {} },
        .status = .discharged,
        .blocks_profile = .readable_luau,
        .detail = "numeric domain is proven",
        .evidence = &.{fixture.proof},
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = ir.QueryId.fromIndex(0),
        .certificate = ir.CertificateId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.certificates = &certificates;
    program.obligations = &obligations;

    var valid_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer valid_report.deinit();
    try std.testing.expect(valid_report.isClean());

    obligations[0].query = ir.QueryId.fromIndex(1);
    var wrong_query_report = try validation.validate(std.testing.allocator, &program, .core);
    defer wrong_query_report.deinit();
    try std.testing.expect(wrong_query_report.contains(.invalid_obligation_certificate_reference));

    obligations[0].query = ir.QueryId.fromIndex(0);
    obligations[0].status = .open;
    var wrong_status_report = try validation.validate(std.testing.allocator, &program, .core);
    defer wrong_status_report.deinit();
    try std.testing.expect(wrong_status_report.contains(.obligation_certificate_resolution_mismatch));

    obligations[0].status = .discharged;
    obligations[0].certificate = null;
    var missing_proof_report = try validation.validate(std.testing.allocator, &program, .core);
    defer missing_proof_report.deinit();
    try std.testing.expect(missing_proof_report.contains(.discharged_obligation_without_proof));

    obligations[0].query = ir.QueryId.fromIndex(99);
    var invalid_query_report = try validation.validate(std.testing.allocator, &program, .core);
    defer invalid_query_report.deinit();
    try std.testing.expect(invalid_query_report.contains(.invalid_obligation_query_reference));

    obligations[0].status = .open;
    obligations[0].certificate = null;
    obligations[0].query = ir.QueryId.fromIndex(0);
    obligations[0].requirement = null;
    var missing_requirement_report = try validation.validate(std.testing.allocator, &program, .core);
    defer missing_requirement_report.deinit();
    try std.testing.expect(missing_requirement_report.contains(.obligation_query_requirement_mismatch));

    obligations[0].requirement = .{ .kind = .prove_true, .predicate = ir.SolverTermId.fromIndex(99) };
    var invalid_requirement_report = try validation.validate(std.testing.allocator, &program, .core);
    defer invalid_requirement_report.deinit();
    try std.testing.expect(invalid_requirement_report.contains(.invalid_obligation_requirement_reference));
    try std.testing.expect(invalid_requirement_report.contains(.obligation_query_requirement_mismatch));

    obligations[0].requirement = .{ .kind = .prove_false, .predicate = ir.SolverTermId.fromIndex(0) };
    var wrong_requirement_report = try validation.validate(std.testing.allocator, &program, .core);
    defer wrong_requirement_report.deinit();
    try std.testing.expect(wrong_requirement_report.contains(.obligation_query_requirement_mismatch));

    obligations[0].requirement = ir.ObligationRequirement.fromQuery(queries[0]);
    obligations[0].subject = .{ .instruction = fixture.i_sum };
    var wrong_subject_report = try validation.validate(std.testing.allocator, &program, .core);
    defer wrong_subject_report.deinit();
    try std.testing.expect(wrong_subject_report.contains(.obligation_query_subject_mismatch));
}

test "obligation subject validation survives malformed instruction ownership" {
    const fixture = lifter.fixtures.dynamic_truthiness_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_truthy_not.index()].block = ir.BlockId.fromIndex(99);
    const terms = [_]ir.SolverTerm{
        .{
            .id = ir.SolverTermId.fromIndex(0),
            .sort = .{ .kind = .boolean },
            .operation = .{ .boolean_literal = false },
        },
        .{
            .id = ir.SolverTermId.fromIndex(1),
            .sort = .{ .kind = .boolean },
            .operation = .{ .value_definition = .{
                .value = fixture.v_truthy_not,
                .expression = ir.SolverTermId.fromIndex(0),
            } },
        },
    };
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(1),
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .numeric_domain,
        .subject = .{ .function = fixture.f_entry },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "malformed ownership must not authenticate this subject",
        .evidence = &.{fixture.proof},
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.obligations = &obligations;

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.invalid_instruction_block));
    try std.testing.expect(report.contains(.obligation_query_subject_mismatch));
}

test "environment targets admit arbitrary semantic names but reject raw ambient access" {
    const fixtures = lifter.fixtures;
    var instructions = fixtures.arithmetic_module.instructions;
    instructions[0].operation = .{ .environment_get = .{
        .target = .{ .ambient = {} },
        .name = "not a source identifier",
    } };
    instructions[0].effects = .semantic_environment_read;

    var program = fixtures.arithmetic_module.program;
    program.instructions = &instructions;

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());

    var explicit_instructions = fixtures.arithmetic_module.instructions;
    explicit_instructions[fixtures.arithmetic_module.i_sum.index()].operation = .{ .environment_get = .{
        .target = .{ .value = fixtures.arithmetic_module.v_left },
        .name = "not a source identifier",
        .mode = .raw,
    } };
    explicit_instructions[fixtures.arithmetic_module.i_sum.index()].effects = .raw_table_read;
    var explicit_program = fixtures.arithmetic_module.program;
    explicit_program.instructions = &explicit_instructions;
    var explicit_report = try validation.validate(std.testing.allocator, &explicit_program, .readable_luau);
    defer explicit_report.deinit();
    try std.testing.expect(explicit_report.isClean());

    explicit_instructions[fixtures.arithmetic_module.i_sum.index()].operation.environment_get.target = .{ .ambient = {} };
    var raw_ambient_report = try validation.validate(std.testing.allocator, &explicit_program, .core);
    defer raw_ambient_report.deinit();
    try std.testing.expect(raw_ambient_report.contains(.invalid_ambient_environment_mode));
}

test "exact integer text is canonical and readable Luau rejects lossy values" {
    const fixtures = lifter.fixtures;
    var instructions = fixtures.arithmetic_module.instructions;
    var program = fixtures.arithmetic_module.program;
    program.instructions = &instructions;

    instructions[2].operation = .{ .constant = .{ .integer = "01" } };
    var malformed_report = try validation.validate(std.testing.allocator, &program, .core);
    defer malformed_report.deinit();
    try std.testing.expect(malformed_report.contains(.invalid_integer_literal));

    instructions[2].operation = .{ .constant = .{ .integer = "9007199254740993" } };
    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.contains(.inexact_luau_integer_literal));
}

test "raw non-finite numerals are rejected while tagged special numbers are admitted" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_factor.index()].type = .number;
    values[fixture.v_result.index()].type = .number;
    var instructions = fixture.instructions;
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .number = std.math.nan(f64) } };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;

    var nan_report = try validation.validate(std.testing.allocator, &program, .core);
    defer nan_report.deinit();
    try std.testing.expect(nan_report.contains(.invalid_number_literal));

    instructions[fixture.i_factor.index()].operation.constant = .{ .number = std.math.inf(f64) };
    var infinity_report = try validation.validate(std.testing.allocator, &program, .core);
    defer infinity_report.deinit();
    try std.testing.expect(infinity_report.contains(.invalid_number_literal));

    inline for (std.meta.tags(ir.SpecialNumber)) |special| {
        instructions[fixture.i_factor.index()].operation.constant = .{ .special_number = special };
        var special_report = try validation.validate(std.testing.allocator, &program, .core);
        defer special_report.deinit();
        try std.testing.expect(!special_report.contains(.invalid_number_literal));
    }
}

test "solver numerals reject noncanonical and overflowing bit-vector text" {
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "+1" } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .bit_vector, .bit_width = 8 }, .operation = .{ .bit_vector_literal = .{ .value = "256", .bit_width = 8 } } },
    };
    const program: ir.Program = .{
        .program_id = "invalid-solver-numerals",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .solver_terms = &terms,
    };
    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.invalid_solver_numeral));
}

test "solver bit-vector numerals are not limited by host integer width" {
    var terms = [_]ir.SolverTerm{
        .{
            .id = ir.SolverTermId.fromIndex(0),
            .sort = .{ .kind = .bit_vector, .bit_width = 128 },
            .operation = .{ .bit_vector_literal = .{
                .value = "340282366920938463463374607431768211455",
                .bit_width = 128,
            } },
        },
    };
    var program = lifter.fixtures.arithmetic_module.program;
    program.solver_terms = &terms;

    var valid_report = try validation.validate(std.testing.allocator, &program, .core);
    defer valid_report.deinit();
    try std.testing.expect(!valid_report.contains(.invalid_solver_numeral));

    terms[0].operation.bit_vector_literal.value = "340282366920938463463374607431768211456";
    var overflow_report = try validation.validate(std.testing.allocator, &program, .core);
    defer overflow_report.deinit();
    try std.testing.expect(overflow_report.contains(.invalid_solver_numeral));
}

test "solver sort descriptors are canonical" {
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .integer, .bit_width = 32, .signed = true },
        .operation = .{ .integer_literal = "1" },
    }};
    var program = lifter.fixtures.arithmetic_module.program;
    program.solver_terms = &terms;
    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.invalid_solver_sort));
}

test "solver conditional selection requires prior Boolean and equal-sort terms" {
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "11" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "22" } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .integer }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(0),
            .then_term = ir.SolverTermId.fromIndex(1),
            .else_term = ir.SolverTermId.fromIndex(2),
        } } },
    };
    var program = lifter.fixtures.arithmetic_module.program;
    program.solver_terms = &terms;

    var valid_report = try validation.validate(std.testing.allocator, &program, .core);
    defer valid_report.deinit();
    try std.testing.expect(!valid_report.contains(.solver_sort_mismatch));
    try std.testing.expect(!valid_report.contains(.solver_term_not_topological));

    terms[3].operation.if_then_else.condition = ir.SolverTermId.fromIndex(1);
    var condition_report = try validation.validate(std.testing.allocator, &program, .core);
    defer condition_report.deinit();
    try std.testing.expect(condition_report.contains(.solver_sort_mismatch));
    terms[3].operation.if_then_else.condition = ir.SolverTermId.fromIndex(0);

    terms[3].operation.if_then_else.else_term = ir.SolverTermId.fromIndex(0);
    var arm_report = try validation.validate(std.testing.allocator, &program, .core);
    defer arm_report.deinit();
    try std.testing.expect(arm_report.contains(.solver_sort_mismatch));
    terms[3].operation.if_then_else.else_term = ir.SolverTermId.fromIndex(2);

    terms[3].sort = .{ .kind = .boolean };
    var result_report = try validation.validate(std.testing.allocator, &program, .core);
    defer result_report.deinit();
    try std.testing.expect(result_report.contains(.solver_sort_mismatch));
    terms[3].sort = .{ .kind = .integer };

    terms[3].operation.if_then_else.then_term = ir.SolverTermId.fromIndex(3);
    var topology_report = try validation.validate(std.testing.allocator, &program, .core);
    defer topology_report.deinit();
    try std.testing.expect(topology_report.contains(.solver_term_not_topological));
    terms[3].operation.if_then_else.then_term = ir.SolverTermId.fromIndex(1);

    terms[3].operation.if_then_else.else_term = ir.SolverTermId.fromIndex(99);
    var reference_report = try validation.validate(std.testing.allocator, &program, .core);
    defer reference_report.deinit();
    try std.testing.expect(reference_report.contains(.invalid_solver_term_reference));
}

test "dynamic truthiness requires a prior direct dynamic value term" {
    const fixture = lifter.fixtures.automatic_promotion_module;
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_matched } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(1),
            .then_term = ir.SolverTermId.fromIndex(0),
            .else_term = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(0) } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    var valid_report = try validation.validate(std.testing.allocator, &program, .core);
    defer valid_report.deinit();
    try std.testing.expect(!valid_report.contains(.invalid_dynamic_truthiness_operand));
    try std.testing.expect(!valid_report.contains(.solver_sort_mismatch));

    terms[3].operation.dynamic_truthiness = ir.SolverTermId.fromIndex(2);
    var compositional_report = try validation.validate(std.testing.allocator, &program, .core);
    defer compositional_report.deinit();
    try std.testing.expect(compositional_report.contains(.invalid_dynamic_truthiness_operand));
    terms[3].operation.dynamic_truthiness = ir.SolverTermId.fromIndex(0);

    terms[3].sort = .{ .kind = .dynamic_value };
    var result_report = try validation.validate(std.testing.allocator, &program, .core);
    defer result_report.deinit();
    try std.testing.expect(result_report.contains(.solver_sort_mismatch));
}

test "dynamic number NaN predicates require a prior direct numeric dynamic value term" {
    const fixture = lifter.fixtures.arithmetic_module;
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(1),
            .then_term = ir.SolverTermId.fromIndex(0),
            .else_term = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_number_is_nan = ir.SolverTermId.fromIndex(0) } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    var valid_report = try validation.validate(std.testing.allocator, &program, .core);
    defer valid_report.deinit();
    try std.testing.expect(!valid_report.contains(.invalid_dynamic_number_operand));
    try std.testing.expect(!valid_report.contains(.solver_sort_mismatch));

    terms[3].operation.dynamic_number_is_nan = ir.SolverTermId.fromIndex(2);
    var compositional_report = try validation.validate(std.testing.allocator, &program, .core);
    defer compositional_report.deinit();
    try std.testing.expect(compositional_report.contains(.invalid_dynamic_number_operand));
    terms[3].operation.dynamic_number_is_nan = ir.SolverTermId.fromIndex(0);

    terms[0].operation.value = fixture.v_export;
    var category_report = try validation.validate(std.testing.allocator, &program, .core);
    defer category_report.deinit();
    try std.testing.expect(category_report.contains(.invalid_dynamic_number_operand));
    terms[0].operation.value = fixture.v_factor;

    terms[3].sort = .{ .kind = .dynamic_value };
    var result_report = try validation.validate(std.testing.allocator, &program, .core);
    defer result_report.deinit();
    try std.testing.expect(result_report.contains(.solver_sort_mismatch));
}

test "solver bit-vector structure enforces exact widths and bounds" {
    const bv4: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 4 };
    const bv8: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 8 };
    var terms = [_]ir.SolverTerm{
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
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "-1" } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = bv8, .operation = .{ .integer_to_bit_vector = ir.SolverTermId.fromIndex(9) } },
        .{ .id = ir.SolverTermId.fromIndex(11), .sort = .{ .kind = .integer }, .operation = .{ .bit_vector_to_integer = .{
            .operand = ir.SolverTermId.fromIndex(10),
            .signed = true,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(12), .sort = .{ .kind = .integer }, .operation = .{ .bit_vector_to_integer = .{
            .operand = ir.SolverTermId.fromIndex(10),
            .signed = false,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(13), .sort = bv8, .operation = .{ .arithmetic_negate = ir.SolverTermId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(14), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "7" } },
        .{ .id = ir.SolverTermId.fromIndex(15), .sort = .{ .kind = .integer }, .operation = .{ .arithmetic_negate = ir.SolverTermId.fromIndex(14) } },
        .{ .id = ir.SolverTermId.fromIndex(16), .sort = .{ .kind = .real }, .operation = .{ .real_literal = .{ .numerator = "3", .denominator = "2" } } },
        .{ .id = ir.SolverTermId.fromIndex(17), .sort = .{ .kind = .real }, .operation = .{ .arithmetic_negate = ir.SolverTermId.fromIndex(16) } },
    };
    var program = lifter.fixtures.arithmetic_module.program;
    program.solver_terms = &terms;

    var valid_report = try validation.validate(std.testing.allocator, &program, .core);
    defer valid_report.deinit();
    try std.testing.expect(!valid_report.contains(.solver_sort_mismatch));

    terms[1].sort.bit_width = 7;
    var not_report = try validation.validate(std.testing.allocator, &program, .core);
    defer not_report.deinit();
    try std.testing.expect(not_report.contains(.solver_sort_mismatch));
    terms[1].sort = bv8;

    terms[2].operation.bit_vector_extract.high = 8;
    var extract_bound_report = try validation.validate(std.testing.allocator, &program, .core);
    defer extract_bound_report.deinit();
    try std.testing.expect(extract_bound_report.contains(.solver_sort_mismatch));
    terms[2].operation.bit_vector_extract.high = 5;
    terms[2].operation.bit_vector_extract.low = 6;
    var extract_order_report = try validation.validate(std.testing.allocator, &program, .core);
    defer extract_order_report.deinit();
    try std.testing.expect(extract_order_report.contains(.solver_sort_mismatch));
    terms[2].operation.bit_vector_extract.low = 2;

    terms[4].sort.bit_width = 7;
    var concat_report = try validation.validate(std.testing.allocator, &program, .core);
    defer concat_report.deinit();
    try std.testing.expect(concat_report.contains(.solver_sort_mismatch));
    terms[4].sort = bv8;

    terms[5].operation.bit_vector_extend.extra_bits = 0;
    var extension_report = try validation.validate(std.testing.allocator, &program, .core);
    defer extension_report.deinit();
    try std.testing.expect(extension_report.contains(.solver_sort_mismatch));
    terms[5].operation.bit_vector_extend.extra_bits = 4;

    terms[8].operation.bit_vector_rotate.amount = ir.SolverTermId.fromIndex(3);
    var rotation_amount_report = try validation.validate(std.testing.allocator, &program, .core);
    defer rotation_amount_report.deinit();
    try std.testing.expect(rotation_amount_report.contains(.solver_sort_mismatch));
    terms[8].operation.bit_vector_rotate.amount = ir.SolverTermId.fromIndex(7);
    terms[8].sort.bit_width = 7;
    var rotation_result_report = try validation.validate(std.testing.allocator, &program, .core);
    defer rotation_result_report.deinit();
    try std.testing.expect(rotation_result_report.contains(.solver_sort_mismatch));
    terms[8].sort = bv8;

    terms[10].operation.integer_to_bit_vector = ir.SolverTermId.fromIndex(0);
    var to_word_report = try validation.validate(std.testing.allocator, &program, .core);
    defer to_word_report.deinit();
    try std.testing.expect(to_word_report.contains(.solver_sort_mismatch));
    terms[10].operation.integer_to_bit_vector = ir.SolverTermId.fromIndex(9);
    terms[11].operation.bit_vector_to_integer.operand = ir.SolverTermId.fromIndex(9);
    var to_integer_report = try validation.validate(std.testing.allocator, &program, .core);
    defer to_integer_report.deinit();
    try std.testing.expect(to_integer_report.contains(.solver_sort_mismatch));
    terms[11].operation.bit_vector_to_integer.operand = ir.SolverTermId.fromIndex(10);

    terms[13].sort = .{ .kind = .integer };
    var negate_report = try validation.validate(std.testing.allocator, &program, .core);
    defer negate_report.deinit();
    try std.testing.expect(negate_report.contains(.solver_sort_mismatch));
}

test "solver division requires an exact nonzero guard in symbolic queries" {
    const fixture = lifter.fixtures.arithmetic_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = fixture.v_left } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "-5" } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(2) } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .integer }, .operation = .{ .division = .{
            .mode = .integer_euclidean,
            .left = ir.SolverTermId.fromIndex(2),
            .right = ir.SolverTermId.fromIndex(0),
            .defined_by = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "-3" } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(4),
            .right = ir.SolverTermId.fromIndex(5),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .integer }, .operation = .{ .remainder = .{
            .mode = .integer_euclidean,
            .left = ir.SolverTermId.fromIndex(2),
            .right = ir.SolverTermId.fromIndex(0),
            .defined_by = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "0" } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(7),
            .right = ir.SolverTermId.fromIndex(8),
        } } },
    };
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(1),
        .evidence = &.{fixture.proof},
    }};
    var queries = [_]ir.SolverQuery{
        .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .assumptions = &.{ir.ConstraintId.fromIndex(0)},
            .goal = ir.SolverTermId.fromIndex(6),
        },
        .{
            .id = ir.QueryId.fromIndex(1),
            .kind = .prove_true,
            .assumptions = &.{ir.ConstraintId.fromIndex(0)},
            .goal = ir.SolverTermId.fromIndex(9),
        },
    };
    var mutable_terms = terms;
    var program = fixture.program;
    program.solver_terms = &mutable_terms;
    program.constraints = &constraints;
    program.queries = &queries;

    var valid_report = try validation.validate(std.testing.allocator, &program, .core);
    defer valid_report.deinit();
    try std.testing.expect(!valid_report.contains(.solver_sort_mismatch));
    try std.testing.expect(!valid_report.contains(.solver_precondition_not_assumed));
    var accepted = try lifter.solver_backend.internalFacts().solve(std.testing.allocator, &program, queries[0]);
    defer accepted.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.unknown, accepted.resolution);

    queries[0].assumptions = &.{};
    var missing_report = try validation.validate(std.testing.allocator, &program, .core);
    defer missing_report.deinit();
    try std.testing.expect(missing_report.contains(.solver_precondition_not_assumed));
    try std.testing.expectError(
        error.MissingSolverPrecondition,
        lifter.solver_backend.internalFacts().solve(std.testing.allocator, &program, queries[0]),
    );
    queries[0].assumptions = &.{ir.ConstraintId.fromIndex(0)};

    queries[1].assumptions = &.{};
    var missing_remainder_report = try validation.validate(std.testing.allocator, &program, .core);
    defer missing_remainder_report.deinit();
    try std.testing.expect(missing_remainder_report.contains(.solver_precondition_not_assumed));
    try std.testing.expectError(
        error.MissingSolverPrecondition,
        lifter.solver_backend.internalFacts().solve(std.testing.allocator, &program, queries[1]),
    );
    queries[1].assumptions = &.{ir.ConstraintId.fromIndex(0)};

    mutable_terms[4].operation.division.defined_by = ir.SolverTermId.fromIndex(3);
    var wrong_guard_report = try validation.validate(std.testing.allocator, &program, .core);
    defer wrong_guard_report.deinit();
    try std.testing.expect(wrong_guard_report.contains(.solver_sort_mismatch));
    mutable_terms[4].operation.division.defined_by = ir.SolverTermId.fromIndex(1);
    mutable_terms[4].operation.division.mode = .real;
    var wrong_mode_report = try validation.validate(std.testing.allocator, &program, .core);
    defer wrong_mode_report.deinit();
    try std.testing.expect(wrong_mode_report.contains(.solver_sort_mismatch));
    mutable_terms[4].operation.division.mode = .integer_euclidean;

    mutable_terms[7].operation.remainder.defined_by = ir.SolverTermId.fromIndex(3);
    var wrong_remainder_guard_report = try validation.validate(std.testing.allocator, &program, .core);
    defer wrong_remainder_guard_report.deinit();
    try std.testing.expect(wrong_remainder_guard_report.contains(.solver_sort_mismatch));
    mutable_terms[7].operation.remainder.defined_by = ir.SolverTermId.fromIndex(1);
    mutable_terms[7].operation.remainder.mode = .bit_vector_unsigned;
    var wrong_remainder_mode_report = try validation.validate(std.testing.allocator, &program, .core);
    defer wrong_remainder_mode_report.deinit();
    try std.testing.expect(wrong_remainder_mode_report.contains(.solver_sort_mismatch));
}
