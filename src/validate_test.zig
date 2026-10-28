const std = @import("std");
const lifter = @import("semantic_lifter");
const ir = lifter.ir;
const validation = lifter.validate;

const entry_binding_fixture = struct {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const captured_first = ir.ValueId.fromIndex(0);
    const captured_second = ir.ValueId.fromIndex(1);
    const place_first = ir.PlaceId.fromIndex(0);
    const place_second = ir.PlaceId.fromIndex(1);
    const capture_value_first = ir.CaptureId.fromIndex(0);
    const capture_value_second = ir.CaptureId.fromIndex(1);
    const capture_place_first = ir.CaptureId.fromIndex(2);
    const capture_place_second = ir.CaptureId.fromIndex(3);
    const external_value = ir.ExternalBindingId.fromIndex(0);
    const external_place = ir.ExternalBindingId.fromIndex(1);
    const proof = ir.EvidenceId.fromIndex(0);

    const values = [_]ir.Value{
        .{ .id = captured_first, .function = function_id, .type = .integer, .name_hint = "captured_first", .origin = .{ .capture = capture_value_first } },
        .{ .id = captured_second, .function = function_id, .type = .integer, .name_hint = "captured_second", .origin = .{ .capture = capture_value_second } },
    };
    const places = [_]ir.Place{
        .{ .id = place_first, .function = function_id, .type = .integer, .name_hint = "place_first", .origin = .{ .capture = capture_place_first }, .evidence = &.{proof} },
        .{ .id = place_second, .function = function_id, .type = .integer, .name_hint = "place_second", .origin = .{ .capture = capture_place_second }, .evidence = &.{proof} },
    };
    const captures = [_]ir.Capture{
        .{ .id = capture_value_first, .function = function_id, .kind = .{ .immutable_value = captured_first }, .evidence = &.{proof} },
        .{ .id = capture_value_second, .function = function_id, .kind = .{ .immutable_value = captured_second }, .evidence = &.{proof} },
        .{ .id = capture_place_first, .function = function_id, .kind = .{ .shared_place = place_first }, .evidence = &.{proof} },
        .{ .id = capture_place_second, .function = function_id, .kind = .{ .shared_place = place_second }, .evidence = &.{proof} },
    };
    const external_bindings = [_]ir.ExternalBinding{
        .{ .id = external_value, .kind = .immutable_value, .type = .integer, .evidence = &.{proof} },
        .{ .id = external_place, .kind = .shared_place, .type = .integer, .evidence = &.{proof} },
    };
    const entry_bindings = [_]ir.ExternalBindingId{ external_value, external_value, external_place, external_place };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .terminator = .{ .return_values = &.{ captured_first, captured_second } },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .name_hint = "entry",
        .captures = &.{ capture_value_first, capture_value_second, capture_place_first, capture_place_second },
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .source_span, .locator = "fixture:entry-external-bindings" }};
    const program: ir.Program = .{
        .program_id = "entry-external-bindings",
        .entry_function = function_id,
        .entry_bindings = &entry_bindings,
        .external_bindings = &external_bindings,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .places = &places,
        .captures = &captures,
        .evidence = &evidence,
    };
};

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

test "exact integer text is canonical and both profiles reject lossy values" {
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
    try std.testing.expect(core_report.contains(.inexact_luau_integer_literal));

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.contains(.inexact_luau_integer_literal));
}

test "core refuses integer text beyond 2^53 and a number literal carries the value" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    var instructions = fixture.instructions;
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;

    for ([_][]const u8{ "9007199254740993", "-9007199254740993", "9007199254740996", "18446744073709551615" }) |decimal| {
        instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = decimal } };
        var core_report = try validation.validate(std.testing.allocator, &program, .core);
        defer core_report.deinit();
        try std.testing.expect(core_report.contains(.inexact_luau_integer_literal));
        var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
        defer readable_report.deinit();
        try std.testing.expect(readable_report.contains(.inexact_luau_integer_literal));
    }

    for ([_][]const u8{ "9007199254740992", "-9007199254740992" }) |decimal| {
        instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = decimal } };
        var core_report = try validation.validate(std.testing.allocator, &program, .core);
        defer core_report.deinit();
        try std.testing.expect(core_report.isClean());
        var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
        defer readable_report.deinit();
        try std.testing.expect(!readable_report.contains(.inexact_luau_integer_literal));
    }

    values[fixture.v_factor.index()].type = .number;
    values[fixture.v_result.index()].type = .number;
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .number = 9007199254740996.0 } };
    var number_report = try validation.validate(std.testing.allocator, &program, .core);
    defer number_report.deinit();
    try std.testing.expect(number_report.isClean());
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

test "fixed-width integer values map to matching solver bit-vectors" {
    const fixture = lifter.fixtures.arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32, .signed = false };
    var values = fixture.values;
    values[fixture.v_factor.index()].type = u32_type;
    const bv32: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 32 };
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv32, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv32, .operation = .{ .bit_vector_literal = .{ .value = "2", .bit_width = 32 } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) };
    var program = fixture.program;
    program.values = &values;
    program.solver_terms = &terms;
    program.queries = &.{query};

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(!report.contains(.solver_sort_mismatch));
    try std.testing.expectEqual(ir.SolverResolution.proved, lifter.solver.solve(&program, query));

    terms[0].sort.signed = true;
    var mismatch_report = try validation.validate(std.testing.allocator, &program, .core);
    defer mismatch_report.deinit();
    try std.testing.expect(mismatch_report.contains(.solver_sort_mismatch));
}

test "wide bit-vector models remain typed solver-neutral artifacts" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_left.index()].type = .dynamic;
    const bv128: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 128 };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv128, .operation = .{ .value = fixture.v_left } },
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
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .find_model,
        .goal = ir.SolverTermId.fromIndex(2),
    }};
    var bindings = [_]ir.SolverModelBinding{.{
        .term = ir.SolverTermId.fromIndex(0),
        .value = .{ .bit_vector = .{
            .value = "340282366920938463463374607431768211455",
            .bit_width = 128,
        } },
    }};
    const models = [_]ir.SolverModel{.{
        .id = ir.SolverModelId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .bindings = &bindings,
    }};
    var program = fixture.program;
    program.values = &values;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.solver_models = &models;

    var valid_report = try validation.validate(std.testing.allocator, &program, .core);
    defer valid_report.deinit();
    try std.testing.expect(!valid_report.contains(.invalid_solver_model_value));
    try std.testing.expect(!valid_report.contains(.irrelevant_solver_model_term));
    try std.testing.expect(!valid_report.contains(.contradictory_solver_model));
    try std.testing.expect(!valid_report.contains(.incomplete_solver_model));

    bindings[0].value.bit_vector.value = "340282366920938463463374607431768211456";
    var overflow_report = try validation.validate(std.testing.allocator, &program, .core);
    defer overflow_report.deinit();
    try std.testing.expect(overflow_report.contains(.invalid_solver_model_value));
}

test "serialized solver models replay owning query semantics" {
    const fixture = lifter.fixtures.arithmetic_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = fixture.v_left } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "7" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .find_model,
        .goal = ir.SolverTermId.fromIndex(2),
    }};
    const bindings = [_]ir.SolverModelBinding{.{
        .term = ir.SolverTermId.fromIndex(0),
        .value = .{ .integer = "7" },
    }};
    const models = [_]ir.SolverModel{.{
        .id = ir.SolverModelId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .bindings = &bindings,
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.solver_models = &models;

    const encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(encoded);
    var parsed = try lifter.codec.parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    var valid_report = try validation.validate(std.testing.allocator, &parsed.value, .core);
    defer valid_report.deinit();
    try std.testing.expect(!valid_report.contains(.contradictory_solver_model));
    try std.testing.expect(!valid_report.contains(.incomplete_solver_model));

    const tampered_bindings = try std.testing.allocator.dupe(ir.SolverModelBinding, parsed.value.solver_models[0].bindings);
    defer std.testing.allocator.free(tampered_bindings);
    tampered_bindings[0].value = .{ .integer = "8" };
    const tampered_models = try std.testing.allocator.dupe(ir.SolverModel, parsed.value.solver_models);
    defer std.testing.allocator.free(tampered_models);
    tampered_models[0].bindings = tampered_bindings;
    var tampered = parsed.value;
    tampered.solver_models = tampered_models;
    var tampered_report = try validation.validate(std.testing.allocator, &tampered, .core);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.contradictory_solver_model));
    var found_model_index = false;
    for (tampered_report.diagnostics.items) |diagnostic| {
        if (diagnostic.code != .contradictory_solver_model) continue;
        try std.testing.expectEqual(@as(?u32, 0), diagnostic.entity_index);
        found_model_index = true;
    }
    try std.testing.expect(found_model_index);
}

test "direct vararg pack return satisfies readable admission" {
    const fixtures = lifter.fixtures;
    var report = try validation.validate(std.testing.allocator, &fixtures.variadic_identity_module.program, .readable_luau);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "value-pack producers form a canonical dominance-safe bijection" {
    const fixtures = lifter.fixtures;

    {
        const reordered = [_]ir.InstructionId{
            fixtures.open_pack_adjust_module.i_get,
            fixtures.open_pack_adjust_module.i_adjust,
            fixtures.open_pack_adjust_module.i_call,
        };
        var blocks = fixtures.open_pack_adjust_module.blocks;
        blocks[0].instructions = &reordered;
        var program = fixtures.open_pack_adjust_module.program;
        program.blocks = &blocks;
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(report.contains(.value_pack_used_before_definition));
    }

    {
        var instructions = fixtures.open_pack_adjust_module.instructions;
        instructions[1].pack_result = null;
        var program = fixtures.open_pack_adjust_module.program;
        program.instructions = &instructions;
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(report.contains(.invalid_instruction_pack_result));
        try std.testing.expect(report.contains(.missing_value_pack_definition));
    }

    {
        var instructions = fixtures.open_pack_adjust_module.instructions;
        instructions[0].pack_result = fixtures.open_pack_adjust_module.p_results;
        var program = fixtures.open_pack_adjust_module.program;
        program.instructions = &instructions;
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(report.contains(.duplicate_value_pack_definition));
        try std.testing.expect(report.contains(.instruction_pack_result_origin_mismatch));
    }

    {
        var instructions = fixtures.open_pack_adjust_module.instructions;
        instructions[2].effects = .{ .precision = .unknown };
        var program = fixtures.open_pack_adjust_module.program;
        program.instructions = &instructions;
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(report.contains(.invalid_pack_adjustment_effects));
    }

    {
        const gap_id = ir.InstructionId.fromIndex(3);
        const unused_id = ir.ValueId.fromIndex(2);
        var values = fixtures.open_pack_adjust_module.values ++ [_]ir.Value{.{
            .id = unused_id,
            .function = fixtures.open_pack_adjust_module.f_entry,
            .origin = .{ .instruction_result = .{ .instruction = gap_id, .index = 0 } },
        }};
        var instructions = fixtures.open_pack_adjust_module.instructions ++ [_]ir.Instruction{.{
            .id = gap_id,
            .block = fixtures.open_pack_adjust_module.b_entry,
            .operation = .{ .constant = .{ .nil_value = {} } },
            .results = &.{unused_id},
            .effects = .pure,
            .evidence = &.{fixtures.open_pack_adjust_module.proof},
        }};
        const reordered = [_]ir.InstructionId{
            fixtures.open_pack_adjust_module.i_get,
            fixtures.open_pack_adjust_module.i_call,
            gap_id,
            fixtures.open_pack_adjust_module.i_adjust,
        };
        var blocks = fixtures.open_pack_adjust_module.blocks;
        blocks[0].instructions = &reordered;
        var program = fixtures.open_pack_adjust_module.program;
        program.values = &values;
        program.instructions = &instructions;
        program.blocks = &blocks;
        var core_report = try validation.validate(std.testing.allocator, &program, .core);
        defer core_report.deinit();
        try std.testing.expect(core_report.isClean());
        var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
        defer readable_report.deinit();
        try std.testing.expect(readable_report.isClean());
    }
}

test "readable capability decisions occur at admission" {
    const fixtures = lifter.fixtures;

    {
        var functions = fixtures.arithmetic_module.functions;
        functions[0].is_variadic = true;
        var program = fixtures.arithmetic_module.program;
        program.functions = &functions;
        var core_report = try validation.validate(std.testing.allocator, &program, .core);
        defer core_report.deinit();
        try std.testing.expect(core_report.isClean());
        var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
        defer readable_report.deinit();
        try std.testing.expect(readable_report.isClean());

        const orphan_packs = [_]ir.ValuePack{.{
            .id = ir.ValuePackId.fromIndex(0),
            .function = functions[0].id,
            .origin = .{ .varargs = functions[0].id },
            .evidence = &.{fixtures.arithmetic_module.proof},
        }};
        var orphan_program = program;
        orphan_program.value_packs = &orphan_packs;
        var orphan_report = try validation.validate(std.testing.allocator, &orphan_program, .core);
        defer orphan_report.deinit();
        try std.testing.expect(orphan_report.contains(.missing_value_pack_definition));
    }

    {
        var core_report = try validation.validate(std.testing.allocator, &fixtures.immutable_closure_module.program, .core);
        defer core_report.deinit();
        try std.testing.expect(core_report.isClean());
        var readable_report = try validation.validate(std.testing.allocator, &fixtures.immutable_closure_module.program, .readable_luau);
        defer readable_report.deinit();
        try std.testing.expect(readable_report.isClean());
    }

    {
        var core_report = try validation.validate(std.testing.allocator, &fixtures.shared_place_closure_module.program, .core);
        defer core_report.deinit();
        try std.testing.expect(core_report.isClean());
        var readable_report = try validation.validate(std.testing.allocator, &fixtures.shared_place_closure_module.program, .readable_luau);
        defer readable_report.deinit();
        try std.testing.expect(readable_report.isClean());
    }

    {
        var core_report = try validation.validate(std.testing.allocator, &fixtures.open_pack_adjust_module.program, .core);
        defer core_report.deinit();
        try std.testing.expect(core_report.isClean());
        var readable_report = try validation.validate(std.testing.allocator, &fixtures.open_pack_adjust_module.program, .readable_luau);
        defer readable_report.deinit();
        try std.testing.expect(readable_report.isClean());
    }

    {
        var blocks = fixtures.absolute_value_module.blocks;
        blocks[2].terminator = .{ .jump = .{ .target = fixtures.absolute_value_module.b_nonnegative } };
        blocks[3].terminator = .{ .branch = .{
            .condition = fixtures.absolute_value_module.v_is_negative,
            .then_edge = .{ .target = fixtures.absolute_value_module.b_nonnegative },
            .else_edge = .{ .target = fixtures.absolute_value_module.b_negative },
        } };
        var program = fixtures.absolute_value_module.program;
        program.blocks = &blocks;
        var core_report = try validation.validate(std.testing.allocator, &program, .core);
        defer core_report.deinit();
        try std.testing.expect(core_report.isClean());
        var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
        defer readable_report.deinit();
        // Readable-profile admission can preserve an unstructured CFG through
        // the emitter's explicit dispatcher fallback. Failure to build a
        // structured plan is therefore not itself an admission error.
        try std.testing.expect(readable_report.isClean());

        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const normalized = try lifter.irreducible_normalize.normalizeInArena(arena.allocator(), &program);
        try std.testing.expectEqual(@as(usize, 1), normalized.cloned_blocks);
        try std.testing.expectEqual(@as(usize, 0), normalized.cloned_instructions);
        try std.testing.expectEqual(@as(usize, 0), normalized.cloned_values);
        const clone_id = ir.BlockId.fromIndex(program.blocks.len);
        try std.testing.expectEqual(clone_id, normalized.program.blocks[clone_id.index()].terminator.branch.then_edge.target);
        var normalized_report = try validation.validate(std.testing.allocator, &normalized.program, .readable_luau);
        defer normalized_report.deinit();
        try std.testing.expect(normalized_report.isClean());
    }
}

test "core ownership lists are complete bijections" {
    const fixtures = lifter.fixtures;
    const no_blocks = [_]ir.BlockId{};
    const duplicate_blocks = [_]ir.BlockId{
        fixtures.arithmetic_module.b_add,
        fixtures.arithmetic_module.b_add,
    };
    var functions = fixtures.arithmetic_module.functions;
    functions[0].blocks = &no_blocks;
    functions[1].blocks = &duplicate_blocks;

    const no_instructions = [_]ir.InstructionId{};
    const duplicate_instructions = [_]ir.InstructionId{
        fixtures.arithmetic_module.i_sum,
        fixtures.arithmetic_module.i_sum,
        fixtures.arithmetic_module.i_factor,
        fixtures.arithmetic_module.i_result,
    };
    var blocks = fixtures.arithmetic_module.blocks;
    blocks[0].instructions = &no_instructions;
    blocks[1].instructions = &duplicate_instructions;

    var program = fixtures.arithmetic_module.program;
    program.functions = &functions;
    program.blocks = &blocks;
    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.unlisted_function_block));
    try std.testing.expect(report.contains(.duplicate_function_block));
    try std.testing.expect(report.contains(.unlisted_block_instruction));
    try std.testing.expect(report.contains(.duplicate_block_instruction));
}

test "edge-rewrite ids equal their array positions" {
    const fixture = lifter.fixtures.absolute_value_module;
    const profiles = [_]ir.AdmissionProfile{ .core, .readable_luau };
    // The else edge skips the pure forwarder b_nonnegative, and one rewrite records that hop.
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].terminator.branch.else_edge = .{ .target = fixture.b_join, .arguments = &.{fixture.v_input} };
    var rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = fixture.b_entry,
        .kind = .branch_else,
        .from = .{ .target = fixture.b_nonnegative },
        .to = .{ .target = fixture.b_join, .arguments = &.{fixture.v_input} },
        .rule = .forwarding_jump,
    }};
    var program = fixture.program;
    program.blocks = &blocks;
    program.edge_rewrites = &rewrites;

    for (profiles) |profile| {
        var report = try validation.validate(std.testing.allocator, &program, profile);
        defer report.deinit();
        try std.testing.expect(report.isClean());
    }

    const noncanonical_ids = [_]usize{ 1, 99, std.math.maxInt(u32) };
    for (noncanonical_ids) |id| {
        rewrites[0].id = ir.EdgeRewriteId.fromIndex(id);
        for (profiles) |profile| {
            var report = try validation.validate(std.testing.allocator, &program, profile);
            defer report.deinit();
            try std.testing.expect(report.contains(.noncanonical_edge_rewrite_id));
            var reported: usize = 0;
            for (report.diagnostics.items) |diagnostic| {
                if (diagnostic.code != .noncanonical_edge_rewrite_id) continue;
                try std.testing.expectEqual(@as(?u32, 0), diagnostic.entity_index);
                reported += 1;
            }
            try std.testing.expectEqual(@as(usize, 1), reported);
        }
    }
}

test "edge-rewrite ids reject duplicated, reordered and gapped histories" {
    const fixture = lifter.fixtures.absolute_value_module;
    const profiles = [_]ir.AdmissionProfile{ .core, .readable_luau };
    // A relay block makes the else arm a chain of two forwarding hops: b_nonnegative to b_relay, then b_relay to b_join.
    const b_relay = ir.BlockId.fromIndex(5);
    var blocks = fixture.blocks ++ [_]ir.Block{.{
        .id = b_relay,
        .function = fixture.f_absolute,
        .terminator = .{ .jump = .{ .target = fixture.b_join, .arguments = &.{fixture.v_input} } },
        .evidence = &.{fixture.proof},
    }};
    blocks[fixture.b_nonnegative.index()].terminator = .{ .jump = .{ .target = b_relay } };
    blocks[fixture.b_entry.index()].terminator.branch.else_edge = .{ .target = fixture.b_join, .arguments = &.{fixture.v_input} };
    const absolute_blocks = [_]ir.BlockId{ fixture.b_join, fixture.b_negative, fixture.b_entry, fixture.b_nonnegative, b_relay };
    var functions = fixture.functions;
    functions[fixture.f_absolute.index()].blocks = &absolute_blocks;
    var rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = fixture.b_entry,
            .kind = .branch_else,
            .from = .{ .target = fixture.b_nonnegative },
            .to = .{ .target = b_relay },
            .rule = .forwarding_jump,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = fixture.b_entry,
            .kind = .branch_else,
            .from = .{ .target = b_relay },
            .to = .{ .target = fixture.b_join, .arguments = &.{fixture.v_input} },
            .rule = .forwarding_jump,
        },
    };
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.edge_rewrites = &rewrites;

    for (profiles) |profile| {
        var report = try validation.validate(std.testing.allocator, &program, profile);
        defer report.deinit();
        try std.testing.expect(report.isClean());
    }

    // Every position whose id differs from the position is reported, in position order.
    const Case = struct {
        ids: [2]usize,
        entities: []const u32,
    };
    const cases = [_]Case{
        .{ .ids = .{ 0, 0 }, .entities = &.{1} },
        .{ .ids = .{ 1, 0 }, .entities = &.{ 0, 1 } },
        .{ .ids = .{ 0, 2 }, .entities = &.{1} },
    };
    for (cases) |case| {
        for (case.ids, 0..) |id, position| rewrites[position].id = ir.EdgeRewriteId.fromIndex(id);
        for (profiles) |profile| {
            var report = try validation.validate(std.testing.allocator, &program, profile);
            defer report.deinit();
            try std.testing.expect(report.contains(.noncanonical_edge_rewrite_id));
            var reported: usize = 0;
            for (report.diagnostics.items) |diagnostic| {
                if (diagnostic.code != .noncanonical_edge_rewrite_id) continue;
                try std.testing.expect(reported < case.entities.len);
                try std.testing.expectEqual(@as(?u32, case.entities[reported]), diagnostic.entity_index);
                reported += 1;
            }
            try std.testing.expectEqual(case.entities.len, reported);
        }
    }
}

test "SSA uses must follow and be dominated by their definitions" {
    const fixtures = lifter.fixtures;

    {
        const reordered = [_]ir.InstructionId{
            fixtures.arithmetic_module.i_result,
            fixtures.arithmetic_module.i_sum,
            fixtures.arithmetic_module.i_factor,
        };
        var blocks = fixtures.arithmetic_module.blocks;
        blocks[1].instructions = &reordered;
        var program = fixtures.arithmetic_module.program;
        program.blocks = &blocks;
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(report.contains(.value_used_before_definition));
    }

    {
        const sibling_value = [_]ir.ValueId{fixtures.absolute_value_module.v_negated};
        var blocks = fixtures.absolute_value_module.blocks;
        blocks[3].terminator = .{ .jump = .{
            .target = fixtures.absolute_value_module.b_join,
            .arguments = &sibling_value,
        } };
        var program = fixtures.absolute_value_module.program;
        program.blocks = &blocks;
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(report.contains(.non_dominating_value_use));
    }

    {
        var blocks = fixtures.absolute_value_module.blocks;
        blocks[fixtures.absolute_value_module.b_nonnegative.index()].terminator = .{ .throw_error = .{
            .value = fixtures.absolute_value_module.v_input,
            .level = 0,
            .dynamic_level = fixtures.absolute_value_module.v_negated,
        } };
        var program = fixtures.absolute_value_module.program;
        program.blocks = &blocks;
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(report.contains(.non_dominating_value_use));
    }
}

test "unreachable valid blocks can be omitted from readable emission" {
    const fixtures = lifter.fixtures;
    var blocks = fixtures.absolute_value_module.blocks;
    var branch = blocks[1].terminator.branch;
    branch.else_edge.target = fixtures.absolute_value_module.b_negative;
    blocks[1].terminator = .{ .branch = branch };
    var program = fixtures.absolute_value_module.program;
    program.blocks = &blocks;

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());
}

test "readable admission blocks unbound entry, error, and bit-operation semantics" {
    const fixtures = lifter.fixtures;

    {
        const entry_parameters = [_]ir.ValueId{fixtures.arithmetic_module.v_export};
        var blocks = fixtures.arithmetic_module.blocks;
        blocks[0].parameters = &entry_parameters;
        var program = fixtures.arithmetic_module.program;
        program.blocks = &blocks;
        var report = try validation.validate(std.testing.allocator, &program, .core);
        defer report.deinit();
        try std.testing.expect(report.contains(.entry_block_has_parameters));
    }

    {
        var blocks = fixtures.absolute_value_module.blocks;
        blocks[4].terminator = .{ .unreachable_block = {} };
        var program = fixtures.absolute_value_module.program;
        program.blocks = &blocks;
        var core_report = try validation.validate(std.testing.allocator, &program, .core);
        defer core_report.deinit();
        try std.testing.expect(core_report.isClean());
        var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
        defer readable_report.deinit();
        try std.testing.expect(readable_report.contains(.unsupported_readable_terminator));
    }

    {
        var instructions = fixtures.arithmetic_module.instructions;
        instructions[1].operation.binary.operator = .bit_and;
        var program = fixtures.arithmetic_module.program;
        program.instructions = &instructions;
        var core_report = try validation.validate(std.testing.allocator, &program, .core);
        defer core_report.deinit();
        try std.testing.expect(core_report.isClean());
        var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
        defer readable_report.deinit();
        try std.testing.expect(readable_report.contains(.unsupported_readable_bit_operation));
    }

    {
        const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32, .signed = false };
        var values = fixtures.arithmetic_module.values;
        values[1].type = u32_type;
        values[2].type = u32_type;
        values[3].type = u32_type;
        var instructions = fixtures.arithmetic_module.instructions;
        instructions[1].operation = .{ .binary = .{
            .operator = .bit_and,
            .left = fixtures.arithmetic_module.v_left,
            .right = fixtures.arithmetic_module.v_right,
            .mode = .primitive,
        } };
        var program = fixtures.arithmetic_module.program;
        program.values = &values;
        program.instructions = &instructions;
        var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
        defer readable_report.deinit();
        try std.testing.expect(readable_report.isClean());
    }
}

test "shift behavior is required only on runtime shift operations" {
    const fixture = lifter.fixtures.arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32, .signed = false };
    var values = fixture.values;
    values[fixture.v_left.index()].type = u32_type;
    values[fixture.v_right.index()].type = u32_type;
    values[fixture.v_sum.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation = .{ .binary = .{
        .operator = .shift_left,
        .left = fixture.v_left,
        .right = fixture.v_right,
        .mode = .primitive,
    } };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;

    var missing = try validation.validate(std.testing.allocator, &program, .core);
    defer missing.deinit();
    try std.testing.expect(missing.contains(.missing_shift_behavior));
    try std.testing.expect(!missing.contains(.unexpected_shift_behavior));

    instructions[fixture.i_sum.index()].operation.binary.shift_behavior = .zero_saturating;
    var explicit = try validation.validate(std.testing.allocator, &program, .core);
    defer explicit.deinit();
    try std.testing.expect(explicit.isClean());

    instructions[fixture.i_sum.index()].operation.binary.operator = .bit_and;
    var unexpected = try validation.validate(std.testing.allocator, &program, .core);
    defer unexpected.deinit();
    try std.testing.expect(unexpected.contains(.unexpected_shift_behavior));
    try std.testing.expect(!unexpected.contains(.missing_shift_behavior));
}

test "numeric type descriptors are canonical" {
    const fixtures = lifter.fixtures;
    var values = fixtures.arithmetic_module.values;
    values[1].type = .{ .kind = .integer, .bit_width = 0, .signed = false };
    var program = fixtures.arithmetic_module.program;
    program.values = &values;
    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.invalid_value_type));
}

test "operation results cannot claim contradictory semantic types" {
    const fixtures = lifter.fixtures;
    var values = fixtures.arithmetic_module.values;
    values[fixtures.arithmetic_module.v_sum.index()].type = .{ .kind = .string };
    var program = fixtures.arithmetic_module.program;
    program.values = &values;
    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.operation_result_type_mismatch));
}

test "fixed-width integer constants must fit their declared result type" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_factor.index()].type = .{ .kind = .integer, .bit_width = 8, .signed = false };
    var instructions = fixture.instructions;
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;

    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = "-1" } };
    var negative_report = try validation.validate(std.testing.allocator, &program, .core);
    defer negative_report.deinit();
    try std.testing.expect(negative_report.contains(.operation_result_type_mismatch));

    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = "256" } };
    var overflow_report = try validation.validate(std.testing.allocator, &program, .core);
    defer overflow_report.deinit();
    try std.testing.expect(overflow_report.contains(.operation_result_type_mismatch));

    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = "255" } };
    var boundary_report = try validation.validate(std.testing.allocator, &program, .core);
    defer boundary_report.deinit();
    try std.testing.expect(!boundary_report.contains(.operation_result_type_mismatch));
}

test "core integer constants support declared widths beyond host integers and refuse text beyond 2^53" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_factor.index()].type = .{ .kind = .integer, .bit_width = 128, .signed = false };
    var instructions = fixture.instructions;
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = "9007199254740992" } };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;

    var exact_report = try validation.validate(std.testing.allocator, &program, .core);
    defer exact_report.deinit();
    try std.testing.expect(exact_report.isClean());

    instructions[fixture.i_factor.index()].operation = .{ .constant = .{
        .integer = "340282366920938463463374607431768211455",
    } };
    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(!core_report.contains(.invalid_integer_literal));
    try std.testing.expect(!core_report.contains(.operation_result_type_mismatch));
    try std.testing.expect(core_report.contains(.inexact_luau_integer_literal));

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.contains(.inexact_luau_integer_literal));
}

test "place writes must preserve the place value type" {
    const fixture = lifter.fixtures.shared_place_closure_module;
    var values = fixture.values;
    values[fixture.v_start.index()].type = .string;
    var program = fixture.program;
    program.values = &values;

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.place_value_type_mismatch));
}

test "obligation queries cover only referenced external bindings" {
    const fixture = entry_binding_fixture;
    const constant_terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const constant_queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    }};
    var obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .unresolved_identity,
        .subject = .{ .external_binding = fixture.external_value },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "the query must depend on this entry binding",
        .evidence = &.{fixture.proof},
        .requirement = ir.ObligationRequirement.fromQuery(constant_queries[0]),
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &constant_terms;
    program.queries = &constant_queries;
    program.obligations = &obligations;

    var unrelated = try validation.validate(std.testing.allocator, &program, .core);
    defer unrelated.deinit();
    try std.testing.expect(unrelated.contains(.obligation_query_subject_mismatch));

    const dependent_terms = [_]ir.SolverTerm{
        .{
            .id = ir.SolverTermId.fromIndex(0),
            .sort = .{ .kind = .integer },
            .operation = .{ .value = fixture.captured_first },
        },
        .{
            .id = ir.SolverTermId.fromIndex(1),
            .sort = .{ .kind = .integer },
            .operation = .{ .integer_literal = "0" },
        },
        .{
            .id = ir.SolverTermId.fromIndex(2),
            .sort = .{ .kind = .boolean },
            .operation = .{ .binary = .{
                .operator = .equal,
                .left = ir.SolverTermId.fromIndex(0),
                .right = ir.SolverTermId.fromIndex(1),
            } },
        },
    };
    const dependent_queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(2),
    }};
    obligations[0].requirement = ir.ObligationRequirement.fromQuery(dependent_queries[0]);
    program.solver_terms = &dependent_terms;
    program.queries = &dependent_queries;

    var related = try validation.validate(std.testing.allocator, &program, .core);
    defer related.deinit();
    try std.testing.expect(!related.contains(.obligation_query_subject_mismatch));
    try std.testing.expect(related.isClean());
}

test "entry external bindings admit explicit value and place aliases" {
    const fixture = entry_binding_fixture;
    var report = try validation.validate(std.testing.allocator, &fixture.program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
    try std.testing.expectEqual(fixture.entry_bindings[0], fixture.entry_bindings[1]);
    try std.testing.expectEqual(fixture.entry_bindings[2], fixture.entry_bindings[3]);
}

test "entry capture mappings report missing invalid and unused external slots" {
    const fixture = entry_binding_fixture;

    var missing_program = fixture.program;
    missing_program.entry_bindings = &.{};
    var missing = try validation.validate(std.testing.allocator, &missing_program, .core);
    defer missing.deinit();
    try std.testing.expect(missing.contains(.entry_capture_binding_arity_mismatch));
    try std.testing.expect(missing.contains(.unlisted_external_binding));
    try std.testing.expect(!missing.contains(.capture_without_lexical_parent));

    const invalid_bindings = [_]ir.ExternalBindingId{
        fixture.external_value,
        fixture.external_value,
        fixture.external_place,
        ir.ExternalBindingId.fromIndex(9),
    };
    var invalid_program = fixture.program;
    invalid_program.entry_bindings = &invalid_bindings;
    var invalid = try validation.validate(std.testing.allocator, &invalid_program, .core);
    defer invalid.deinit();
    try std.testing.expect(invalid.contains(.invalid_entry_capture_binding));

    const bindings_with_unused = fixture.external_bindings ++ [_]ir.ExternalBinding{.{
        .id = ir.ExternalBindingId.fromIndex(2),
        .kind = .immutable_value,
        .type = .integer,
        .evidence = &.{fixture.proof},
    }};
    var unused_program = fixture.program;
    unused_program.external_bindings = &bindings_with_unused;
    var unused = try validation.validate(std.testing.allocator, &unused_program, .core);
    defer unused.deinit();
    try std.testing.expect(unused.contains(.unlisted_external_binding));
}

test "entry capture mappings enforce kind and directional type contracts" {
    const fixture = entry_binding_fixture;
    const wrong_kind = [_]ir.ExternalBindingId{
        fixture.external_place,
        fixture.external_value,
        fixture.external_place,
        fixture.external_place,
    };
    var wrong_kind_program = fixture.program;
    wrong_kind_program.entry_bindings = &wrong_kind;
    var kind_report = try validation.validate(std.testing.allocator, &wrong_kind_program, .core);
    defer kind_report.deinit();
    try std.testing.expect(kind_report.contains(.entry_capture_binding_kind_mismatch));

    var wrong_types = fixture.external_bindings;
    wrong_types[fixture.external_value.index()].type = .dynamic;
    wrong_types[fixture.external_place.index()].type = .number;
    var wrong_type_program = fixture.program;
    wrong_type_program.external_bindings = &wrong_types;
    var type_report = try validation.validate(std.testing.allocator, &wrong_type_program, .core);
    defer type_report.deinit();
    try std.testing.expect(type_report.contains(.entry_capture_binding_type_mismatch));

    var malformed = fixture.external_bindings;
    malformed[0].id = ir.ExternalBindingId.fromIndex(1);
    malformed[0].type = .{ .kind = .integer };
    var malformed_program = fixture.program;
    malformed_program.external_bindings = &malformed;
    var malformed_report = try validation.validate(std.testing.allocator, &malformed_program, .core);
    defer malformed_report.deinit();
    try std.testing.expect(malformed_report.contains(.noncanonical_external_binding_id));
    try std.testing.expect(malformed_report.contains(.invalid_external_binding_type));
}

test "nonentry root captures remain ownerless" {
    const fixture = entry_binding_fixture;
    const second_function = ir.FunctionId.fromIndex(1);
    const second_block = ir.BlockId.fromIndex(1);
    const blocks = fixture.blocks ++ [_]ir.Block{.{
        .id = second_block,
        .function = second_function,
        .terminator = .{ .return_values = &.{} },
        .evidence = &.{fixture.proof},
    }};
    const functions = fixture.functions ++ [_]ir.Function{.{
        .id = second_function,
        .blocks = &.{second_block},
        .entry_block = second_block,
        .evidence = &.{fixture.proof},
    }};
    var program = fixture.program;
    program.entry_function = second_function;
    program.entry_bindings = &.{};
    program.external_bindings = &.{};
    program.functions = &functions;
    program.blocks = &blocks;

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.capture_without_lexical_parent));
}

test "immutable closure bindings must match captured slot types" {
    const fixture = lifter.fixtures.immutable_closure_module;
    var values = fixture.values;
    values[fixture.v_base.index()].type = .string;
    var program = fixture.program;
    program.values = &values;

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.closure_binding_type_mismatch));
}

test "shared-place closure bindings must match captured place types" {
    const fixture = lifter.fixtures.shared_place_closure_module;
    var values = fixture.values;
    values[fixture.v_start.index()].type = .number;
    var places = fixture.places;
    places[fixture.p_state.index()].type = .number;
    var program = fixture.program;
    program.values = &values;
    program.places = &places;

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(!report.contains(.place_value_type_mismatch));
    try std.testing.expect(report.contains(.closure_binding_type_mismatch));
}

test "shared-place closure bindings are invariant rather than covariant" {
    const fixture = lifter.fixtures.shared_place_closure_module;
    var places = fixture.places;
    places[fixture.p_captured_state.index()].type = .number;
    var values = fixture.values;
    values[fixture.v_current.index()].type = .number;
    values[fixture.v_next.index()].type = .number;
    var program = fixture.program;
    program.places = &places;
    program.values = &values;

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.closure_binding_type_mismatch));
}

test "copy and place reads allow only directional type widening" {
    const arithmetic = lifter.fixtures.arithmetic_module;
    var arithmetic_values = arithmetic.values;
    arithmetic_values[arithmetic.v_sum.index()].type = .number;
    arithmetic_values[arithmetic.v_result.index()].type = .number;
    var arithmetic_instructions = arithmetic.instructions;
    arithmetic_instructions[arithmetic.i_sum.index()].operation = .{ .copy = arithmetic.v_left };
    var arithmetic_program = arithmetic.program;
    arithmetic_program.values = &arithmetic_values;
    arithmetic_program.instructions = &arithmetic_instructions;
    var copy_report = try validation.validate(std.testing.allocator, &arithmetic_program, .core);
    defer copy_report.deinit();
    try std.testing.expect(!copy_report.contains(.operation_result_type_mismatch));

    const shared = lifter.fixtures.shared_place_closure_module;
    var shared_values = shared.values;
    shared_values[shared.v_current.index()].type = .number;
    shared_values[shared.v_next.index()].type = .number;
    var shared_program = shared.program;
    shared_program.values = &shared_values;
    var read_report = try validation.validate(std.testing.allocator, &shared_program, .core);
    defer read_report.deinit();
    try std.testing.expect(!read_report.contains(.operation_result_type_mismatch));
}

test "CFG edge values must match their block parameter types" {
    const fixture = lifter.fixtures.absolute_value_module;
    var values = fixture.values;
    values[fixture.v_absolute.index()].type = .{ .kind = .string };
    var program = fixture.program;
    program.values = &values;
    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.edge_argument_type_mismatch));
}

test "solver sorts and certificates are independently auditable" {
    const fixtures = lifter.fixtures;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "1" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .integer }, .operation = .{ .binary = .{
            .operator = .add,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    }};
    const certificates = [_]ir.SolverCertificate{
        .{
            .id = ir.CertificateId.fromIndex(0),
            .query = ir.QueryId.fromIndex(0),
            .engine = .internal_facts,
            .resolution = .disproved,
        },
        .{
            .id = ir.CertificateId.fromIndex(1),
            .query = ir.QueryId.fromIndex(0),
            .engine = .z3,
            .resolution = .proved,
        },
    };
    var program = fixtures.arithmetic_module.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.certificates = &certificates;

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.solver_sort_mismatch));
    try std.testing.expect(report.contains(.certificate_replay_mismatch));
    try std.testing.expect(report.contains(.certificate_without_proof));
}

test "solver models and unsat cores are typed query-bound artifacts" {
    const fixture = lifter.fixtures.arithmetic_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = fixture.v_left } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "0" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .greater, .left = ir.SolverTermId.fromIndex(0), .right = ir.SolverTermId.fromIndex(1) } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "9" } },
    };
    var constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(2),
        .evidence = &.{fixture.proof},
    }};
    var queries = [_]ir.SolverQuery{
        .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .assumptions = &.{ir.ConstraintId.fromIndex(0)},
            .goal = ir.SolverTermId.fromIndex(2),
        },
        .{
            .id = ir.QueryId.fromIndex(1),
            .kind = .prove_true,
            .goal = ir.SolverTermId.fromIndex(2),
        },
    };
    var model_bindings = [_]ir.SolverModelBinding{.{
        .term = ir.SolverTermId.fromIndex(0),
        .value = .{ .integer = "-1" },
    }};
    var models = [_]ir.SolverModel{.{
        .id = ir.SolverModelId.fromIndex(0),
        .query = ir.QueryId.fromIndex(1),
        .bindings = &model_bindings,
        .evidence = &.{fixture.proof},
    }};
    var core_constraints = [_]ir.ConstraintId{ir.ConstraintId.fromIndex(0)};
    var cores = [_]ir.UnsatCore{.{
        .id = ir.UnsatCoreId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .constraints = &core_constraints,
        .evidence = &.{fixture.proof},
    }};
    var certificates = [_]ir.SolverCertificate{
        .{
            .id = ir.CertificateId.fromIndex(0),
            .query = ir.QueryId.fromIndex(0),
            .engine = .z3,
            .resolution = .proved,
            .evidence = &.{fixture.proof},
            .certificate_digest = "fixture:unsat-core",
            .unsat_core = ir.UnsatCoreId.fromIndex(0),
        },
        .{
            .id = ir.CertificateId.fromIndex(1),
            .query = ir.QueryId.fromIndex(1),
            .engine = .z3,
            .resolution = .disproved,
            .evidence = &.{fixture.proof},
            .certificate_digest = "fixture:model",
            .model = ir.SolverModelId.fromIndex(0),
        },
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    program.queries = &queries;
    program.solver_models = &models;
    program.unsat_cores = &cores;
    program.certificates = &certificates;

    var valid_report = try validation.validate(std.testing.allocator, &program, .core);
    defer valid_report.deinit();
    try std.testing.expect(!valid_report.contains(.invalid_solver_model_value));
    try std.testing.expect(!valid_report.contains(.irrelevant_solver_model_term));
    try std.testing.expect(!valid_report.contains(.contradictory_solver_model));
    try std.testing.expect(!valid_report.contains(.incomplete_solver_model));
    try std.testing.expect(!valid_report.contains(.invalid_unsat_core_constraint));
    try std.testing.expect(!valid_report.contains(.certificate_artifact_mismatch));
    try std.testing.expect(valid_report.contains(.certificate_without_proof));

    certificates[0].engine = .internal_facts;
    cores[0].constraints = &.{};
    var incomplete_core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer incomplete_core_report.deinit();
    try std.testing.expect(incomplete_core_report.contains(.incomplete_unsat_core));
    var found_core_index = false;
    for (incomplete_core_report.diagnostics.items) |diagnostic| {
        if (diagnostic.code != .incomplete_unsat_core) continue;
        try std.testing.expectEqual(@as(?u32, 0), diagnostic.entity_index);
        found_core_index = true;
    }
    try std.testing.expect(found_core_index);
    cores[0].constraints = &core_constraints;
    certificates[0].engine = .z3;

    models[0].evidence = &.{};
    var model_evidence_report = try validation.validate(std.testing.allocator, &program, .core);
    defer model_evidence_report.deinit();
    try std.testing.expect(model_evidence_report.contains(.certificate_artifact_mismatch));
    models[0].evidence = &.{fixture.proof};

    model_bindings[0].value = .{ .integer = "-01" };
    var numeral_report = try validation.validate(std.testing.allocator, &program, .core);
    defer numeral_report.deinit();
    try std.testing.expect(numeral_report.contains(.invalid_solver_model_value));
    model_bindings[0].value = .{ .integer = "-1" };

    model_bindings[0].value = .{ .integer = "7" };
    var contradictory_model_report = try validation.validate(std.testing.allocator, &program, .core);
    defer contradictory_model_report.deinit();
    try std.testing.expect(contradictory_model_report.contains(.contradictory_solver_model));
    model_bindings[0].value = .{ .integer = "-1" };

    models[0].bindings = &.{};
    var incomplete_model_report = try validation.validate(std.testing.allocator, &program, .core);
    defer incomplete_model_report.deinit();
    try std.testing.expect(incomplete_model_report.contains(.incomplete_solver_model));
    models[0].bindings = &model_bindings;

    const duplicate_bindings = [_]ir.SolverModelBinding{ model_bindings[0], model_bindings[0] };
    models[0].bindings = &duplicate_bindings;
    var duplicate_model_report = try validation.validate(std.testing.allocator, &program, .core);
    defer duplicate_model_report.deinit();
    try std.testing.expect(duplicate_model_report.contains(.duplicate_solver_model_term));
    models[0].bindings = &model_bindings;

    const irrelevant_bindings = [_]ir.SolverModelBinding{.{
        .term = ir.SolverTermId.fromIndex(3),
        .value = .{ .integer = "9" },
    }};
    models[0].bindings = &irrelevant_bindings;
    var irrelevant_model_report = try validation.validate(std.testing.allocator, &program, .core);
    defer irrelevant_model_report.deinit();
    try std.testing.expect(irrelevant_model_report.contains(.irrelevant_solver_model_term));
    try std.testing.expect(!irrelevant_model_report.contains(.invalid_solver_model_reference));
    var found_model_index = false;
    for (irrelevant_model_report.diagnostics.items) |diagnostic| {
        if (diagnostic.code != .irrelevant_solver_model_term) continue;
        try std.testing.expectEqual(@as(?u32, 0), diagnostic.entity_index);
        found_model_index = true;
    }
    try std.testing.expect(found_model_index);
    models[0].bindings = &model_bindings;

    const duplicate_core = [_]ir.ConstraintId{ ir.ConstraintId.fromIndex(0), ir.ConstraintId.fromIndex(0) };
    cores[0].constraints = &duplicate_core;
    var duplicate_core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer duplicate_core_report.deinit();
    try std.testing.expect(duplicate_core_report.contains(.duplicate_unsat_core_constraint));
    cores[0].constraints = &core_constraints;

    core_constraints[0] = ir.ConstraintId.fromIndex(99);
    var foreign_core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer foreign_core_report.deinit();
    try std.testing.expect(foreign_core_report.contains(.invalid_unsat_core_constraint));
    core_constraints[0] = ir.ConstraintId.fromIndex(0);

    const duplicate_assumptions = [_]ir.ConstraintId{ ir.ConstraintId.fromIndex(0), ir.ConstraintId.fromIndex(0) };
    queries[0].assumptions = &duplicate_assumptions;
    var duplicate_assumption_report = try validation.validate(std.testing.allocator, &program, .core);
    defer duplicate_assumption_report.deinit();
    try std.testing.expect(duplicate_assumption_report.contains(.duplicate_query_assumption));
    queries[0].assumptions = &.{ir.ConstraintId.fromIndex(0)};

    constraints[0].evidence = &.{};
    var core_evidence_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_evidence_report.deinit();
    try std.testing.expect(core_evidence_report.contains(.unsat_core_constraint_without_evidence));
    constraints[0].evidence = &.{fixture.proof};

    certificates[0].model = ir.SolverModelId.fromIndex(0);
    var artifact_report = try validation.validate(std.testing.allocator, &program, .core);
    defer artifact_report.deinit();
    try std.testing.expect(artifact_report.contains(.certificate_artifact_mismatch));
}

test "solver real literals use exact canonical rationals" {
    const fixture = lifter.fixtures.arithmetic_module;
    var terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .real },
        .operation = .{ .real_literal = .{ .numerator = "1", .denominator = "0" } },
    }};
    var program = fixture.program;
    program.solver_terms = &terms;

    var zero_report = try validation.validate(std.testing.allocator, &program, .core);
    defer zero_report.deinit();
    try std.testing.expect(zero_report.contains(.invalid_solver_numeral));

    terms[0].operation = .{ .real_literal = .{ .numerator = "-3", .denominator = "2" } };
    var valid_report = try validation.validate(std.testing.allocator, &program, .core);
    defer valid_report.deinit();
    try std.testing.expect(!valid_report.contains(.invalid_solver_numeral));
    try std.testing.expect(!valid_report.contains(.solver_sort_mismatch));
}

test "instruction-scoped places require a matching allocation write" {
    const fixture = lifter.fixtures.shared_place_closure_module;
    var places = fixture.places;
    places[fixture.p_state.index()].origin = .{ .instruction = fixture.i_initialize };
    var program = fixture.program;
    program.places = &places;

    var valid_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer valid_report.deinit();
    try std.testing.expect(valid_report.isClean());

    places[fixture.p_state.index()].origin = .{ .instruction = fixture.i_make_counter };
    var malformed_report = try validation.validate(std.testing.allocator, &program, .core);
    defer malformed_report.deinit();
    try std.testing.expect(malformed_report.contains(.invalid_place_allocation));
}

test "edge-scoped constraints reject unauthenticated stale targets" {
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
        .scope = .{ .edge = .{
            .source = fixture.b_entry,
            .kind = .branch_then,
            .target = fixture.b_nonnegative,
        } },
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.invalid_constraint_scope));
}

test "instruction-scoped place use must follow its allocation" {
    const fixture = lifter.fixtures.shared_place_closure_module;
    var places = fixture.places;
    places[fixture.p_state.index()].origin = .{ .instruction = fixture.i_initialize };
    const reversed = [_]ir.InstructionId{ fixture.i_make_counter, fixture.i_initialize };
    var blocks = fixture.blocks;
    blocks[fixture.b_factory.index()].instructions = &reversed;
    var program = fixture.program;
    program.places = &places;
    program.blocks = &blocks;

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.place_used_before_allocation));
}

test "instruction-scoped place allocation must dominate every use" {
    const f = ir.FunctionId.fromIndex(0);
    const b_entry = ir.BlockId.fromIndex(0);
    const b_allocate = ir.BlockId.fromIndex(1);
    const b_use = ir.BlockId.fromIndex(2);
    const b_exit = ir.BlockId.fromIndex(3);
    const i_condition = ir.InstructionId.fromIndex(0);
    const i_initial = ir.InstructionId.fromIndex(1);
    const i_allocate = ir.InstructionId.fromIndex(2);
    const i_read = ir.InstructionId.fromIndex(3);
    const v_condition = ir.ValueId.fromIndex(0);
    const v_initial = ir.ValueId.fromIndex(1);
    const v_read = ir.ValueId.fromIndex(2);
    const p_state = ir.PlaceId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = v_condition, .function = f, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_condition, .index = 0 } } },
        .{ .id = v_initial, .function = f, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = i_initial, .index = 0 } } },
        .{ .id = v_read, .function = f, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = i_read, .index = 0 } } },
    };
    const places = [_]ir.Place{.{
        .id = p_state,
        .function = f,
        .type = .integer,
        .origin = .{ .instruction = i_allocate },
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = i_condition, .block = b_entry, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{v_condition}, .effects = .pure },
        .{ .id = i_initial, .block = b_entry, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_initial}, .effects = .pure },
        .{ .id = i_allocate, .block = b_allocate, .operation = .{ .place_write = .{ .place = p_state, .value = v_initial } }, .results = &.{}, .effects = .place_write },
        .{ .id = i_read, .block = b_use, .operation = .{ .place_read = p_state }, .results = &.{v_read}, .effects = .place_read },
    };
    const blocks = [_]ir.Block{
        .{
            .id = b_entry,
            .function = f,
            .instructions = &.{ i_condition, i_initial },
            .terminator = .{ .branch = .{
                .condition = v_condition,
                .then_edge = .{ .target = b_allocate },
                .else_edge = .{ .target = b_use },
            } },
        },
        .{ .id = b_allocate, .function = f, .instructions = &.{i_allocate}, .terminator = .{ .jump = .{ .target = b_exit } } },
        .{ .id = b_use, .function = f, .instructions = &.{i_read}, .terminator = .{ .jump = .{ .target = b_exit } } },
        .{ .id = b_exit, .function = f, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = f,
        .local_places = &.{p_state},
        .blocks = &.{ b_entry, b_allocate, b_use, b_exit },
        .entry_block = b_entry,
    }};
    const program: ir.Program = .{
        .program_id = "non-dominating-place-allocation",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.non_dominating_place_allocation));
}

test "table tail packs store a producer across an observable gap" {
    const fixture = lifter.fixtures.open_pack_adjust_module;
    var values = fixture.values;
    values[fixture.v_first.index()].type = .{ .kind = .table };
    var instructions = fixture.instructions;
    instructions[fixture.i_adjust.index()].operation = .{ .make_table_literal = .{
        .fields = &.{},
        .tail_pack = fixture.p_results,
    } };
    instructions[fixture.i_adjust.index()].effects = .table_constructor;
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;

    var valid_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer valid_report.deinit();
    try std.testing.expect(valid_report.isClean());

    const gap_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const delayed_instructions = fixture.instructions ++ [_]ir.Instruction{.{
        .id = gap_id,
        .block = fixture.b_entry,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "after_producer",
            .value = fixture.v_callee,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
        .evidence = &.{fixture.proof},
    }};
    const nonadjacent = [_]ir.InstructionId{ fixture.i_get, fixture.i_call, gap_id, fixture.i_adjust };
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].instructions = &nonadjacent;
    program.blocks = &blocks;
    program.instructions = &delayed_instructions;
    var stored_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer stored_report.deinit();
    try std.testing.expect(stored_report.isClean());
}

test "table pack writes validate effects and pack ownership" {
    const fixture = lifter.fixtures.ordered_table_vararg_module;

    var valid_report = try validation.validate(std.testing.allocator, &fixture.program, .readable_luau);
    defer valid_report.deinit();
    try std.testing.expect(valid_report.isClean());

    var instructions = fixture.instructions;
    instructions[fixture.i_append.index()].effects = .pure;
    var effect_program = fixture.program;
    effect_program.instructions = &instructions;
    var effect_report = try validation.validate(std.testing.allocator, &effect_program, .core);
    defer effect_report.deinit();
    try std.testing.expect(effect_report.contains(.invalid_table_set_pack_effects));

    const f_other = ir.FunctionId.fromIndex(1);
    const b_other = ir.BlockId.fromIndex(1);
    const blocks = fixture.blocks ++ [_]ir.Block{.{
        .id = b_other,
        .function = f_other,
        .terminator = .{ .return_values = &.{} },
        .evidence = &.{fixture.proof},
    }};
    var functions = fixture.functions ++ [_]ir.Function{.{
        .id = f_other,
        .blocks = &.{b_other},
        .entry_block = b_other,
        .is_variadic = true,
        .vararg_pack = fixture.p_varargs,
        .evidence = &.{fixture.proof},
    }};
    functions[fixture.f_entry.index()].is_variadic = false;
    functions[fixture.f_entry.index()].vararg_pack = null;
    var packs = fixture.value_packs;
    packs[fixture.p_varargs.index()].function = f_other;
    packs[fixture.p_varargs.index()].origin = .{ .varargs = f_other };
    var ownership_program = fixture.program;
    ownership_program.functions = &functions;
    ownership_program.blocks = &blocks;
    ownership_program.value_packs = &packs;
    var ownership_report = try validation.validate(std.testing.allocator, &ownership_program, .core);
    defer ownership_report.deinit();
    try std.testing.expect(ownership_report.contains(.cross_function_value_pack));
}

test "all table constructors require allocation effects" {
    const fixture = lifter.fixtures.fresh_reference_module;
    var instructions = fixture.instructions;
    var program = fixture.program;
    program.instructions = &instructions;

    var valid_report = try validation.validate(std.testing.allocator, &program, .core);
    defer valid_report.deinit();
    try std.testing.expect(valid_report.isClean());

    instructions[fixture.i_table_a.index()].effects = .pure;
    var empty_report = try validation.validate(std.testing.allocator, &program, .core);
    defer empty_report.deinit();
    try std.testing.expect(empty_report.contains(.invalid_table_constructor_effects));

    instructions[fixture.i_table_a.index()].effects = .table_constructor;
    instructions[fixture.i_table_b.index()].effects = .pure;
    var literal_report = try validation.validate(std.testing.allocator, &program, .core);
    defer literal_report.deinit();
    try std.testing.expect(literal_report.contains(.invalid_table_constructor_effects));
}

test "string interpolation validates segment arity and dynamic effects" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_result.index()].type = .string;
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .string_interpolate = .{
        .segments = &.{"only-one-segment"},
        .values = &.{fixture.v_left},
    } };
    instructions[fixture.i_result.index()].effects = .string_interpolation;
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;

    var shape_report = try validation.validate(std.testing.allocator, &program, .core);
    defer shape_report.deinit();
    try std.testing.expect(shape_report.contains(.invalid_string_interpolation_shape));

    instructions[fixture.i_result.index()].operation.string_interpolate.segments = &.{ "left=", "" };
    instructions[fixture.i_result.index()].effects = .pure;
    var effect_report = try validation.validate(std.testing.allocator, &program, .core);
    defer effect_report.deinit();
    try std.testing.expect(effect_report.contains(.invalid_string_interpolation_effects));
}
