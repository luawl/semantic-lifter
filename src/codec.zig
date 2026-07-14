const std = @import("std");
const ir = @import("ir.zig");
const fixtures = @import("fixtures.zig");
const validate = @import("validate.zig");

pub const ParsedProgram = std.json.Parsed(ir.Program);

pub fn encodeAlloc(allocator: std.mem.Allocator, program: *const ir.Program) ![]u8 {
    return std.json.Stringify.valueAlloc(allocator, program.*, .{ .whitespace = .indent_2 });
}

pub fn encodeCompactAlloc(allocator: std.mem.Allocator, program: *const ir.Program) ![]u8 {
    return std.json.Stringify.valueAlloc(allocator, program.*, .{});
}

pub fn parse(allocator: std.mem.Allocator, source: []const u8) !ParsedProgram {
    return std.json.parseFromSlice(ir.Program, allocator, source, .{
        .allocate = .alloc_always,
        .ignore_unknown_fields = true,
    });
}

test "serialized semantic IR round trips and remains readable-admissible" {
    const encoded = try encodeAlloc(std.testing.allocator, &fixtures.arithmetic_module.program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"integer\": \"2\"") != null);

    var parsed = try parse(std.testing.allocator, encoded);
    defer parsed.deinit();

    try std.testing.expectEqualStrings("generic-arithmetic-module", parsed.value.program_id);
    try std.testing.expectEqual(@as(usize, 2), parsed.value.functions.len);
    try std.testing.expectEqual(@as(usize, 4), parsed.value.instructions.len);

    var report = try validate.validate(std.testing.allocator, &parsed.value, .readable_luau);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "numeric transition mode is explicit only for semantic normalization" {
    const native: ir.NumericForNext = .{
        .control = ir.ValueId.fromIndex(0),
        .limit = ir.ValueId.fromIndex(1),
        .step = ir.ValueId.fromIndex(2),
        .initial = ir.ValueId.fromIndex(3),
    };
    const encoded_native = try std.json.Stringify.valueAlloc(std.testing.allocator, native, .{});
    defer std.testing.allocator.free(encoded_native);
    try std.testing.expectEqualStrings("{\"control\":0,\"limit\":1,\"step\":2,\"initial\":3}", encoded_native);

    const semantic: ir.NumericForNext = .{
        .control = ir.ValueId.fromIndex(0),
        .limit = ir.ValueId.fromIndex(1),
        .step = ir.ValueId.fromIndex(2),
        .initial = ir.ValueId.fromIndex(3),
        .mode = .semantic_normalized,
    };
    const encoded_semantic = try std.json.Stringify.valueAlloc(std.testing.allocator, semantic, .{});
    defer std.testing.allocator.free(encoded_semantic);
    try std.testing.expectEqualStrings(
        "{\"control\":0,\"limit\":1,\"step\":2,\"initial\":3,\"mode\":\"semantic_normalized\"}",
        encoded_semantic,
    );

    var parsed_native = try std.json.parseFromSlice(ir.NumericForNext, std.testing.allocator, encoded_native, .{});
    defer parsed_native.deinit();
    try std.testing.expectEqual(ir.NumericForMode.luau_numeric, parsed_native.value.mode);
    var parsed_semantic = try std.json.parseFromSlice(ir.NumericForNext, std.testing.allocator, encoded_semantic, .{});
    defer parsed_semantic.deinit();
    try std.testing.expectEqual(ir.NumericForMode.semantic_normalized, parsed_semantic.value.mode);
}

test "node split group provenance is explicit only for grouped rewrites" {
    const legacy: ir.CfgEdgeRewrite = .{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = ir.BlockId.fromIndex(0),
        .kind = .jump,
        .from = .{ .target = ir.BlockId.fromIndex(1) },
        .to = .{ .target = ir.BlockId.fromIndex(2) },
        .rule = .node_split,
    };
    const encoded_legacy = try std.json.Stringify.valueAlloc(std.testing.allocator, legacy, .{});
    defer std.testing.allocator.free(encoded_legacy);
    try std.testing.expect(std.mem.indexOf(u8, encoded_legacy, "node_split_group") == null);

    var grouped = legacy;
    grouped.node_split_group = ir.NodeSplitGroupId.fromIndex(0);
    const encoded_grouped = try std.json.Stringify.valueAlloc(std.testing.allocator, grouped, .{});
    defer std.testing.allocator.free(encoded_grouped);
    try std.testing.expect(std.mem.indexOf(u8, encoded_grouped, "\"node_split_group\":0") != null);

    var parsed_grouped = try std.json.parseFromSlice(ir.CfgEdgeRewrite, std.testing.allocator, encoded_grouped, .{});
    defer parsed_grouped.deinit();
    try std.testing.expectEqual(ir.NodeSplitGroupId.fromIndex(0), parsed_grouped.value.node_split_group.?);
}

test "obligation proof requirements survive JSON round trip" {
    const fixture = fixtures.arithmetic_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = fixture.v_result } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .find_model,
        .goal = ir.SolverTermId.fromIndex(1),
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .numeric_domain,
        .subject = .{ .program = {} },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "retain an exact model requirement",
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.obligations = &obligations;

    const encoded = try encodeAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"requirement\": {") != null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"kind\": \"find_model\"") != null);

    var parsed = try parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    const requirement = parsed.value.obligations[0].requirement.?;
    try std.testing.expectEqual(ir.QueryKind.find_model, requirement.kind);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(1), requirement.predicate);
    var report = try validate.validate(std.testing.allocator, &parsed.value, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "absent obligation proof requirements remain omitted" {
    const fixture = fixtures.arithmetic_module;
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .unresolved_identity,
        .subject = .{ .instruction = fixture.i_export },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "target identity remains unresolved",
        .evidence = &.{fixture.proof},
    }};
    var program = fixture.program;
    program.obligations = &obligations;

    const encoded = try encodeAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"requirement\"") == null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"query\": null") != null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"certificate\": null") != null);

    var parsed = try parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    try std.testing.expect(parsed.value.obligations[0].requirement == null);
}

test "special numeric literals round trip without non-finite JSON numbers" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = ir.ValueId.fromIndex(0), .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = ir.ValueId.fromIndex(1), .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = ir.ValueId.fromIndex(2), .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = block_id, .operation = .{ .constant = .{ .special_number = .nan } }, .results = &.{ir.ValueId.fromIndex(0)}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = ir.InstructionId.fromIndex(1), .block = block_id, .operation = .{ .constant = .{ .special_number = .positive_infinity } }, .results = &.{ir.ValueId.fromIndex(1)}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = ir.InstructionId.fromIndex(2), .block = block_id, .operation = .{ .constant = .{ .special_number = .negative_infinity } }, .results = &.{ir.ValueId.fromIndex(2)}, .effects = .pure, .evidence = &.{proof} },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ ir.InstructionId.fromIndex(0), ir.InstructionId.fromIndex(1), ir.InstructionId.fromIndex(2) },
        .terminator = .{ .return_values = &.{ ir.ValueId.fromIndex(0), ir.ValueId.fromIndex(1), ir.ValueId.fromIndex(2) } },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:special-number-codec" }};
    const program: ir.Program = .{
        .program_id = "special-number-codec",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    const encoded = try encodeAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"special_number\": \"nan\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"special_number\": \"positive_infinity\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"special_number\": \"negative_infinity\"") != null);

    var parsed = try parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    try std.testing.expectEqual(ir.SpecialNumber.nan, parsed.value.instructions[0].operation.constant.special_number);
    try std.testing.expectEqual(ir.SpecialNumber.positive_infinity, parsed.value.instructions[1].operation.constant.special_number);
    try std.testing.expectEqual(ir.SpecialNumber.negative_infinity, parsed.value.instructions[2].operation.constant.special_number);
    var report = try validate.validate(std.testing.allocator, &parsed.value, .readable_luau);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "arbitrary Luau string bytes use canonical JSON transport" {
    const literal: ir.Literal = .{ .string = "\xff\x00" };
    const encoded_literal = try std.json.Stringify.valueAlloc(std.testing.allocator, literal, .{});
    defer std.testing.allocator.free(encoded_literal);
    try std.testing.expectEqualStrings("{\"string_bytes\":\"ff00\"}", encoded_literal);

    var parsed_literal = try std.json.parseFromSlice(ir.Literal, std.testing.allocator, encoded_literal, .{});
    defer parsed_literal.deinit();
    try std.testing.expectEqualSlices(u8, "\xff\x00", parsed_literal.value.string);

    const interpolation: ir.StringInterpolation = .{
        .segments = &.{ "\xfe", "\xc3\xa9" },
        .values = &.{ir.ValueId.fromIndex(0)},
    };
    const encoded_interpolation = try std.json.Stringify.valueAlloc(std.testing.allocator, interpolation, .{});
    defer std.testing.allocator.free(encoded_interpolation);
    try std.testing.expectEqualStrings(
        "{\"segments\":[{\"string_bytes\":\"fe\"},\"\xc3\xa9\"],\"values\":[0]}",
        encoded_interpolation,
    );

    var parsed_interpolation = try std.json.parseFromSlice(
        ir.StringInterpolation,
        std.testing.allocator,
        encoded_interpolation,
        .{},
    );
    defer parsed_interpolation.deinit();
    try std.testing.expectEqualSlices(u8, "\xfe", parsed_interpolation.value.segments[0]);
    try std.testing.expectEqualSlices(u8, "\xc3\xa9", parsed_interpolation.value.segments[1]);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ir.ValueId.fromIndex(0)}, parsed_interpolation.value.values);

    for ([_][]const u8{
        "{\"string_bytes\":\"FF\"}",
        "{\"string_bytes\":\"f\"}",
        "{\"string_bytes\":\"c3a9\"}",
        "{\"string_bytes\":\"fg\"}",
    }) |malformed| {
        try std.testing.expectError(
            error.UnexpectedToken,
            std.json.parseFromSlice(ir.Literal, std.testing.allocator, malformed, .{}),
        );
    }
    try std.testing.expectError(
        error.UnexpectedToken,
        std.json.parseFromSlice(
            ir.StringInterpolation,
            std.testing.allocator,
            "{\"segments\":[{\"string_bytes\":\"c3a9\"}],\"values\":[]}",
            .{},
        ),
    );
    try std.testing.expectError(
        error.SyntaxError,
        std.json.parseFromSlice(ir.Literal, std.testing.allocator, "{\"string\":\"\xff\"}", .{}),
    );
}

test "entry external binding identity survives JSON round trip" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const value_id = ir.ValueId.fromIndex(0);
    const capture_id = ir.CaptureId.fromIndex(0);
    const binding_id = ir.ExternalBindingId.fromIndex(0);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = value_id,
        .function = function_id,
        .type = .integer,
        .origin = .{ .capture = capture_id },
    }};
    const captures = [_]ir.Capture{.{
        .id = capture_id,
        .function = function_id,
        .kind = .{ .immutable_value = value_id },
        .evidence = &.{evidence_id},
    }};
    const external_bindings = [_]ir.ExternalBinding{.{
        .id = binding_id,
        .kind = .immutable_value,
        .type = .integer,
        .evidence = &.{evidence_id},
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .terminator = .{ .return_values = &.{value_id} },
        .evidence = &.{evidence_id},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .captures = &.{capture_id},
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .source_span, .locator = "fixture:external-binding-codec" }};
    const program: ir.Program = .{
        .program_id = "external-binding-codec",
        .entry_function = function_id,
        .entry_bindings = &.{binding_id},
        .external_bindings = &external_bindings,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .captures = &captures,
        .evidence = &evidence,
    };

    const encoded = try encodeAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"entry_bindings\": [") != null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"external_bindings\": [") != null);

    var parsed = try parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    try std.testing.expectEqual(binding_id, parsed.value.entry_bindings[0]);
    try std.testing.expectEqual(ir.ExternalBindingKind.immutable_value, parsed.value.external_bindings[0].kind);
    try std.testing.expectEqual(ir.ValueType.integer, parsed.value.external_bindings[0].type);

    var report = try validate.validate(std.testing.allocator, &parsed.value, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "value-pack identity and origins survive JSON round trip" {
    const encoded = try encodeAlloc(std.testing.allocator, &fixtures.variadic_identity_module.program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"return_pack\": 0") != null);

    var parsed = try parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    try std.testing.expectEqual(@as(usize, 1), parsed.value.value_packs.len);
    try std.testing.expectEqual(fixtures.variadic_identity_module.p_varargs, parsed.value.functions[1].vararg_pack.?);
    try std.testing.expect(parsed.value.value_packs[0].origin == .varargs);

    var report = try validate.validate(std.testing.allocator, &parsed.value, .readable_luau);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "dynamic error levels survive JSON round trip" {
    var blocks = fixtures.absolute_value_module.blocks;
    blocks[fixtures.absolute_value_module.b_join.index()].terminator = .{ .throw_error = .{
        .value = fixtures.absolute_value_module.v_absolute,
        .level = 0,
        .dynamic_level = fixtures.absolute_value_module.v_absolute,
    } };
    var program = fixtures.absolute_value_module.program;
    program.blocks = &blocks;

    const encoded = try encodeAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"dynamic_level\": 5") != null);

    var parsed = try parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    const throw_error = parsed.value.blocks[fixtures.absolute_value_module.b_join.index()].terminator.throw_error;
    try std.testing.expectEqual(@as(u32, 0), throw_error.level);
    try std.testing.expectEqual(fixtures.absolute_value_module.v_absolute, throw_error.dynamic_level.?);

    var core_report = try validate.validate(std.testing.allocator, &parsed.value, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try validate.validate(std.testing.allocator, &parsed.value, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.contains(.unsupported_readable_error_location));
}

test "solver conditional selection survives JSON round trip" {
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "11" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "22" } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .integer }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(0),
            .then_term = ir.SolverTermId.fromIndex(1),
            .else_term = ir.SolverTermId.fromIndex(2),
        } } },
    };
    var program = fixtures.arithmetic_module.program;
    program.solver_terms = &terms;
    const encoded = try encodeAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"if_then_else\"") != null);

    var parsed = try parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    try std.testing.expect(parsed.value.solver_terms[3].operation == .if_then_else);
    const selection = parsed.value.solver_terms[3].operation.if_then_else;
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(0), selection.condition);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(1), selection.then_term);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(2), selection.else_term);

    var report = try validate.validate(std.testing.allocator, &parsed.value, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "opaque dynamic model identities survive JSON round trip" {
    const fixture = fixtures.immutable_closure_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_export } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .find_model,
        .goal = ir.SolverTermId.fromIndex(1),
    }};
    const bindings = [_]ir.SolverModelBinding{.{
        .term = ir.SolverTermId.fromIndex(0),
        .value = .{ .dynamic_identity = 0 },
    }};
    const models = [_]ir.SolverModel{.{
        .id = ir.SolverModelId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .bindings = &bindings,
        .evidence = &.{fixture.proof},
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.solver_models = &models;

    const encoded = try encodeAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"dynamic_identity\": 0") != null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "lifter_dynamic_value") == null);

    var parsed = try parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    try std.testing.expect(parsed.value.solver_models[0].bindings[0].value == .dynamic_identity);
    try std.testing.expectEqual(@as(u32, 0), parsed.value.solver_models[0].bindings[0].value.dynamic_identity);
}

test "validated solver value definitions survive JSON round trip" {
    const fixture = fixtures.arithmetic_module;
    const integer: ir.SolverSort = .{ .kind = .integer };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = integer, .operation = .{ .value = fixture.v_sum } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = integer, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = integer, .operation = .{ .binary = .{
            .operator = .multiply,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = integer, .operation = .{ .value_definition = .{
            .value = fixture.v_result,
            .expression = ir.SolverTermId.fromIndex(2),
        } } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    const encoded = try encodeAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"value_definition\"") != null);

    var parsed = try parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    const definition = parsed.value.solver_terms[3].operation.value_definition;
    try std.testing.expectEqual(fixture.v_result, definition.value);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(2), definition.expression);

    var report = try validate.validate(std.testing.allocator, &parsed.value, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "guarded solver value definitions survive JSON round trip" {
    const fixture = fixtures.arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };
    const bv32: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 32 };
    var values = fixture.values;
    values[fixture.v_right.index()].type = u32_type;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .shift_left,
        .left = fixture.v_sum,
        .right = fixture.v_right,
        .mode = .primitive,
        .shift_behavior = .luau_bit32,
    } };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv32, .operation = .{ .value = fixture.v_sum } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv32, .operation = .{ .value = fixture.v_right } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = bv32, .operation = .{ .bit_vector_literal = .{
            .value = "32",
            .bit_width = 32,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .less,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = bv32, .operation = .{ .binary = .{
            .operator = .shift_left,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = bv32, .operation = .{ .value_definition = .{
            .value = fixture.v_result,
            .expression = ir.SolverTermId.fromIndex(4),
            .valid_when = ir.SolverTermId.fromIndex(3),
        } } },
    };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;

    const encoded = try encodeAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"valid_when\": 3") != null);

    var parsed = try parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    const definition = parsed.value.solver_terms[5].operation.value_definition;
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(3), definition.valid_when.?);

    var report = try validate.validate(std.testing.allocator, &parsed.value, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

test "runtime shift behavior survives JSON round trip" {
    const fixture = fixtures.arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };
    var values = fixture.values;
    values[fixture.v_right.index()].type = u32_type;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;

    for ([_]ir.ShiftBehavior{ .luau_bit32, .zero_saturating }) |behavior| {
        var instructions = fixture.instructions;
        instructions[fixture.i_result.index()].operation = .{ .binary = .{
            .operator = .shift_right,
            .left = fixture.v_sum,
            .right = fixture.v_right,
            .mode = .primitive,
            .shift_behavior = behavior,
        } };
        var program = fixture.program;
        program.values = &values;
        program.instructions = &instructions;

        const encoded = try encodeAlloc(std.testing.allocator, &program);
        defer std.testing.allocator.free(encoded);
        const expected = try std.fmt.allocPrint(std.testing.allocator, "\"shift_behavior\": \"{s}\"", .{@tagName(behavior)});
        defer std.testing.allocator.free(expected);
        try std.testing.expect(std.mem.indexOf(u8, encoded, expected) != null);

        var parsed = try parse(std.testing.allocator, encoded);
        defer parsed.deinit();
        try std.testing.expectEqual(
            behavior,
            parsed.value.instructions[fixture.i_result.index()].operation.binary.shift_behavior.?,
        );
    }
}

test "dynamic numeric domain predicates survive JSON round trip" {
    const fixture = fixtures.arithmetic_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_number_is_nan = ir.SolverTermId.fromIndex(0) } },
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    const encoded = try encodeAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"dynamic_number_is_nan\": 0") != null);

    var parsed = try parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(0), parsed.value.solver_terms[1].operation.dynamic_number_is_nan);

    var report = try validate.validate(std.testing.allocator, &parsed.value, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}
