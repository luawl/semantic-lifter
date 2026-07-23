const std = @import("std");
const lifter = @import("semantic_lifter");
const ir = lifter.ir;
const defaultBackend = lifter.z3_backend.defaultBackend;

fn expectTruth(program: *const ir.Program, goal: ir.SolverTermId, truth: bool) !void {
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = if (truth) .prove_true else .prove_false,
        .goal = goal,
    };
    try std.testing.expectEqual(ir.SolverResolution.proved, lifter.solver.solve(program, query));
    var result = try defaultBackend().solve(std.testing.allocator, program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqual(@as(usize, 0), result.model.items.len);
}

fn bindingFor(bindings: []const ir.SolverModelBinding, term: ir.SolverTermId) ?ir.SolverModelValue {
    for (bindings) |binding| if (binding.term == term) return binding.value;
    return null;
}

test "Z3 and internal facts agree on promoted dynamic logical not definitions" {
    const fixture = lifter.fixtures.dynamic_truthiness_module;
    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(std.testing.allocator);
    const truthy_not = (try lifter.solver_promotion.ensureDefinition(
        std.testing.allocator,
        &fixture.program,
        &terms,
        fixture.v_truthy_not,
    )).?;
    const falsy_not = (try lifter.solver_promotion.ensureDefinition(
        std.testing.allocator,
        &fixture.program,
        &terms,
        fixture.v_falsy_not,
    )).?;
    var program = fixture.program;
    program.solver_terms = terms.items;
    try expectTruth(&program, truthy_not, false);
    try expectTruth(&program, falsy_not, true);
}

test "Z3 dynamic logical not countermodels replay unknown truthiness" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const source = ir.ValueId.fromIndex(0);
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = source } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .logical_not = ir.SolverTermId.fromIndex(1) } },
    };
    const program: ir.Program = .{
        .program_id = "z3-dynamic-logical-not-countermodel",
        .entry_function = function_id,
        .functions = &.{.{ .id = function_id, .parameters = &.{source}, .entry_block = block_id, .blocks = &.{block_id} }},
        .blocks = &.{.{ .id = block_id, .function = function_id, .terminator = .{ .return_values = &.{} } }},
        .instructions = &.{},
        .values = &.{.{ .id = source, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 0 } }},
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(2),
    };
    try std.testing.expectEqual(ir.SolverResolution.unknown, lifter.solver.solve(&program, query));
    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.disproved, result.resolution);
    try std.testing.expectEqual(true, bindingFor(result.model.items, ir.SolverTermId.fromIndex(1)).?.boolean);
    try std.testing.expectEqual(
        lifter.solver_model.Replay.satisfied,
        try lifter.solver_model.replayAlloc(std.testing.allocator, &program, query, result.model.items),
    );
}

test "Z3 and internal facts agree on every known dynamic truthiness category" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const v_nil = ir.ValueId.fromIndex(0);
    const v_false = ir.ValueId.fromIndex(1);
    const v_number = ir.ValueId.fromIndex(2);
    const v_string = ir.ValueId.fromIndex(3);
    const v_table = ir.ValueId.fromIndex(4);
    const v_function = ir.ValueId.fromIndex(5);
    const v_thread = ir.ValueId.fromIndex(6);
    const v_userdata = ir.ValueId.fromIndex(7);
    const v_tuple = ir.ValueId.fromIndex(8);
    const v_copy = ir.ValueId.fromIndex(9);
    const values = [_]ir.Value{
        .{ .id = v_nil, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = v_false, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = v_number, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = v_string, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = v_table, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(4), .index = 0 } } },
        .{ .id = v_function, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = v_thread, .function = function_id, .type = .{ .kind = .thread }, .origin = .{ .parameter = 1 } },
        .{ .id = v_userdata, .function = function_id, .type = .{ .kind = .userdata }, .origin = .{ .parameter = 2 } },
        .{ .id = v_tuple, .function = function_id, .type = .{ .kind = .tuple }, .origin = .{ .parameter = 3 } },
        .{ .id = v_copy, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(5), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = block_id, .operation = .{ .constant = .{ .nil_value = {} } }, .results = &.{v_nil}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(1), .block = block_id, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{v_false}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(2), .block = block_id, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{v_number}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(3), .block = block_id, .operation = .{ .constant = .{ .string = "" } }, .results = &.{v_string}, .effects = .pure },
        .{ .id = ir.InstructionId.fromIndex(4), .block = block_id, .operation = .{ .make_table = {} }, .results = &.{v_table}, .effects = .table_constructor },
        .{ .id = ir.InstructionId.fromIndex(5), .block = block_id, .operation = .{ .copy = v_string }, .results = &.{v_copy}, .effects = .pure },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_nil } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_false } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(2) } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_number } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(4) } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_string } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(6) } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_table } },
        .{ .id = ir.SolverTermId.fromIndex(9), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(8) } },
        .{ .id = ir.SolverTermId.fromIndex(10), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_function } },
        .{ .id = ir.SolverTermId.fromIndex(11), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(10) } },
        .{ .id = ir.SolverTermId.fromIndex(12), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_thread } },
        .{ .id = ir.SolverTermId.fromIndex(13), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(12) } },
        .{ .id = ir.SolverTermId.fromIndex(14), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_userdata } },
        .{ .id = ir.SolverTermId.fromIndex(15), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(14) } },
        .{ .id = ir.SolverTermId.fromIndex(16), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_tuple } },
        .{ .id = ir.SolverTermId.fromIndex(17), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(16) } },
        .{ .id = ir.SolverTermId.fromIndex(18), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = v_copy } },
        .{ .id = ir.SolverTermId.fromIndex(19), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(18) } },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ ir.InstructionId.fromIndex(0), ir.InstructionId.fromIndex(1), ir.InstructionId.fromIndex(2), ir.InstructionId.fromIndex(3), ir.InstructionId.fromIndex(4), ir.InstructionId.fromIndex(5) },
        .terminator = .{ .return_values = &.{} },
    }};
    const program: ir.Program = .{
        .program_id = "z3-known-dynamic-truthiness",
        .entry_function = function_id,
        .functions = &.{.{
            .id = function_id,
            .parameters = &.{ v_function, v_thread, v_userdata, v_tuple },
            .entry_block = block_id,
            .blocks = &.{block_id},
        }},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .solver_terms = &terms,
    };
    try expectTruth(&program, ir.SolverTermId.fromIndex(1), false);
    try expectTruth(&program, ir.SolverTermId.fromIndex(3), false);
    inline for (.{ 5, 7, 9, 11, 13, 15, 17, 19 }) |goal| {
        try expectTruth(&program, ir.SolverTermId.fromIndex(goal), true);
    }
}

test "Z3 persists replayable symbolic Boolean truthiness and authenticates it" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const source = ir.ValueId.fromIndex(0);
    const symbolic_boolean = ir.ValueId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = source, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = symbolic_boolean, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = ir.InstructionId.fromIndex(0),
        .block = block_id,
        .operation = .{ .unary = .{ .operator = .logical_not, .operand = source } },
        .results = &.{symbolic_boolean},
        .effects = .pure,
    }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = symbolic_boolean } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(0) } },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ir.InstructionId.fromIndex(0)},
        .terminator = .{ .return_values = &.{} },
    }};
    const query_id = ir.QueryId.fromIndex(0);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .dynamic_fixture,
        .locator = "fixture:z3-symbolic-boolean-truthiness",
    }};
    const queries = [_]ir.SolverQuery{.{ .id = query_id, .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(1) }};
    const claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(1),
        .status = .unproven,
        .required_for_emission = true,
        .evidence = &.{evidence_id},
        .query = query_id,
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .missing_semantics,
        .subject = .{ .program = {} },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "symbolic dynamic truthiness requires a model",
        .evidence = &.{evidence_id},
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = query_id,
    }};
    const program: ir.Program = .{
        .program_id = "z3-symbolic-boolean-truthiness",
        .entry_function = function_id,
        .functions = &.{.{ .id = function_id, .parameters = &.{source}, .entry_block = block_id, .blocks = &.{block_id} }},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
        .solver_terms = &terms,
        .queries = &queries,
        .claims = &claims,
        .obligations = &obligations,
    };

    var result = try defaultBackend().solve(std.testing.allocator, &program, queries[0]);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.disproved, result.resolution);
    try std.testing.expectEqual(@as(u32, 0), bindingFor(result.model.items, ir.SolverTermId.fromIndex(0)).?.dynamic_identity);
    try std.testing.expectEqual(false, bindingFor(result.model.items, ir.SolverTermId.fromIndex(1)).?.boolean);
    try std.testing.expectEqual(
        lifter.solver_model.Replay.satisfied,
        try lifter.solver_model.replayAlloc(std.testing.allocator, &program, queries[0], result.model.items),
    );

    var resolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &program, defaultBackend());
    defer resolved.deinit();
    try std.testing.expectEqual(@as(usize, 1), resolved.program.solver_models.len);
    try std.testing.expectEqual(ir.SolverResolution.disproved, resolved.program.certificates[0].resolution);
    const encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &resolved.program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "dynamic_truthiness") != null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "lifter_dynamic_value") == null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "dynamic_boolean_false") == null);

    const tampered_bindings = try std.testing.allocator.dupe(ir.SolverModelBinding, resolved.program.solver_models[0].bindings);
    defer std.testing.allocator.free(tampered_bindings);
    for (tampered_bindings) |*binding| {
        if (binding.term == ir.SolverTermId.fromIndex(1)) binding.value = .{ .boolean = true };
    }
    const tampered_models = try std.testing.allocator.dupe(ir.SolverModel, resolved.program.solver_models);
    defer std.testing.allocator.free(tampered_models);
    tampered_models[0].bindings = tampered_bindings;
    var tampered = resolved.program;
    tampered.solver_models = tampered_models;
    var report = try lifter.validate.validate(std.testing.allocator, &tampered, .core);
    defer report.deinit();
    try std.testing.expect(report.contains(.contradictory_solver_model));
    try std.testing.expect(report.contains(.certificate_digest_mismatch));
}
