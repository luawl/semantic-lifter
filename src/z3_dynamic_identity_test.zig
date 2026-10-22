const std = @import("std");
const lifter = @import("semantic_lifter");
const ir = lifter.ir;
const defaultBackend = lifter.z3_backend.defaultBackend;

fn dynamicIdentity(binding: ir.SolverModelBinding) u32 {
    return switch (binding.value) {
        .dynamic_identity => |identity| identity,
        else => unreachable,
    };
}

test "Z3 ignores unsupported terms outside the active query closure" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_left.index()].type = .dynamic;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_left } },
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    };
    var program = fixture.program;
    program.values = &values;
    program.solver_terms = &terms;

    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqual(@as(usize, 0), result.model.items.len);
}

test "Z3 proves reflexive equality over an active dynamic identity" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_left.index()].type = .dynamic;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_left } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    var program = fixture.program;
    program.values = &values;
    program.solver_terms = &terms;
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(1) };

    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqual(@as(usize, 0), result.model.items.len);
    try std.testing.expectEqual(@as(usize, 0), result.unsat_core.items.len);
}

test "Z3 returns canonical distinct classes for a dynamic equality disproof" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_left.index()].type = .dynamic;
    values[fixture.v_right.index()].type = .dynamic;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_left } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_right } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    var program = fixture.program;
    program.values = &values;
    program.solver_terms = &terms;
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) };

    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.disproved, result.resolution);
    try std.testing.expectEqual(@as(usize, 2), result.model.items.len);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(0), result.model.items[0].term);
    try std.testing.expectEqual(ir.SolverTermId.fromIndex(1), result.model.items[1].term);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(result.model.items[0]));
    try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(result.model.items[1]));
    try std.testing.expectEqual(@as(usize, 0), result.unsat_core.items.len);
    try std.testing.expectEqual(
        lifter.solver_model.Replay.satisfied,
        try lifter.solver_model.replayAlloc(std.testing.allocator, &program, query, result.model.items),
    );

    var repeated = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer repeated.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.disproved, repeated.resolution);
    try std.testing.expectEqual(@as(usize, 2), repeated.model.items.len);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(repeated.model.items[0]));
    try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(repeated.model.items[1]));
}

test "Z3 returns one canonical class for a required dynamic equality" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_left.index()].type = .dynamic;
    values[fixture.v_right.index()].type = .dynamic;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_left } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_right } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    var program = fixture.program;
    program.values = &values;
    program.solver_terms = &terms;
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };

    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqual(@as(usize, 2), result.model.items.len);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(result.model.items[0]));
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(result.model.items[1]));
    try std.testing.expectEqual(
        lifter.solver_model.Replay.satisfied,
        try lifter.solver_model.replayAlloc(std.testing.allocator, &program, query, result.model.items),
    );
}

test "Z3 dynamic models replay conditional selection" {
    const condition_value = ir.ValueId.fromIndex(0);
    const left_value = ir.ValueId.fromIndex(1);
    const right_value = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = condition_value, .function = ir.FunctionId.fromIndex(0), .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = left_value, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = right_value, .function = ir.FunctionId.fromIndex(0), .type = .dynamic, .origin = .{ .parameter = 2 } },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = left_value } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = right_value } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .value = condition_value } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .dynamic_value }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(2),
            .then_term = ir.SolverTermId.fromIndex(0),
            .else_term = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(4),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    const constraints = [_]ir.Constraint{
        .{ .id = ir.ConstraintId.fromIndex(0), .predicate = ir.SolverTermId.fromIndex(2) },
        .{ .id = ir.ConstraintId.fromIndex(1), .predicate = ir.SolverTermId.fromIndex(3) },
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .find_model,
        .assumptions = &.{ ir.ConstraintId.fromIndex(0), ir.ConstraintId.fromIndex(1) },
        .goal = ir.SolverTermId.fromIndex(5),
    };
    const program: ir.Program = .{
        .program_id = "z3-dynamic-conditional-model",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
        .constraints = &constraints,
    };

    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqual(@as(usize, 3), result.model.items.len);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(result.model.items[0]));
    try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(result.model.items[1]));
    try std.testing.expect(result.model.items[2].value.boolean);
    try std.testing.expectEqual(
        lifter.solver_model.Replay.satisfied,
        try lifter.solver_model.replayAlloc(std.testing.allocator, &program, query, result.model.items),
    );
}

test "Z3 proves assumed dynamic identity equality with an exact unsat core" {
    const fixture = lifter.fixtures.arithmetic_module;
    var values = fixture.values;
    values[fixture.v_left.index()].type = .dynamic;
    values[fixture.v_right.index()].type = .dynamic;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_left } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_right } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const constraint_id = ir.ConstraintId.fromIndex(0);
    const constraints = [_]ir.Constraint{.{ .id = constraint_id, .predicate = ir.SolverTermId.fromIndex(2) }};
    var program = fixture.program;
    program.values = &values;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{constraint_id},
        .goal = ir.SolverTermId.fromIndex(2),
    };

    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqualSlices(ir.ConstraintId, &.{constraint_id}, result.unsat_core.items);
    try std.testing.expectEqual(@as(usize, 0), result.model.items.len);
}

test "Z3 orchestration certifies a dynamic identity claim" {
    const fixture = lifter.fixtures.arithmetic_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_export } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    const query_id = ir.QueryId.fromIndex(0);
    const claim_id = ir.ClaimId.fromIndex(0);
    const obligation_id = ir.ObligationId.fromIndex(0);
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(1),
    }};
    const claims = [_]ir.Claim{.{
        .id = claim_id,
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(1),
        .status = .unproven,
        .required_for_emission = true,
        .evidence = &.{fixture.proof},
        .query = query_id,
    }};
    const obligations = [_]ir.Obligation{.{
        .id = obligation_id,
        .kind = .unresolved_identity,
        .subject = .{ .program = {} },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "dynamic identity equality must be proved",
        .evidence = &.{fixture.proof},
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = query_id,
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;
    program.obligations = &obligations;

    var resolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &program, defaultBackend());
    defer resolved.deinit();
    try std.testing.expectEqual(ir.ClaimStatus.proved, resolved.program.claims[claim_id.index()].status);
    try std.testing.expectEqual(ir.ObligationStatus.discharged, resolved.program.obligations[obligation_id.index()].status);
    try std.testing.expectEqual(@as(usize, 1), resolved.program.certificates.len);
    try std.testing.expectEqual(ir.SolverEngine.z3, resolved.program.certificates[0].engine);
    try std.testing.expectEqual(ir.SolverResolution.proved, resolved.program.certificates[0].resolution);
    try std.testing.expect(resolved.program.certificates[0].model == null);

    const encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &resolved.program);
    defer std.testing.allocator.free(encoded);
    var parsed = try lifter.codec.parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    var report = try lifter.validate.validate(std.testing.allocator, &parsed.value, .readable_luau);
    defer report.deinit();
    try std.testing.expect(report.isClean());
    var reresolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &parsed.value, defaultBackend());
    defer reresolved.deinit();
    const reresolved_encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &reresolved.program);
    defer std.testing.allocator.free(reresolved_encoded);
    try std.testing.expectEqualStrings(encoded, reresolved_encoded);
}

test "Z3 orchestration records a dynamic disproof model and retains the typed obligation" {
    const fixture = lifter.fixtures.immutable_closure_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_export } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_adder } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const query_id = ir.QueryId.fromIndex(0);
    const claim_id = ir.ClaimId.fromIndex(0);
    const obligation_id = ir.ObligationId.fromIndex(0);
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(2),
    }};
    const claims = [_]ir.Claim{.{
        .id = claim_id,
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(2),
        .status = .unproven,
        .required_for_emission = true,
        .evidence = &.{fixture.proof},
        .query = query_id,
    }};
    const obligations = [_]ir.Obligation{.{
        .id = obligation_id,
        .kind = .unresolved_identity,
        .subject = .{ .program = {} },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "dynamic identity equality was disproved",
        .evidence = &.{fixture.proof},
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = query_id,
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;
    program.obligations = &obligations;

    var resolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &program, defaultBackend());
    defer resolved.deinit();
    try std.testing.expectEqual(ir.ClaimStatus.disproved, resolved.program.claims[claim_id.index()].status);
    try std.testing.expectEqual(ir.ObligationStatus.open, resolved.program.obligations[obligation_id.index()].status);
    try std.testing.expectEqual(@as(usize, 1), resolved.program.certificates.len);
    try std.testing.expectEqual(@as(usize, 1), resolved.program.solver_models.len);
    try std.testing.expectEqual(ir.SolverResolution.disproved, resolved.program.certificates[0].resolution);
    try std.testing.expectEqual(resolved.program.solver_models[0].id, resolved.program.certificates[0].model.?);
    try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(resolved.program.solver_models[0].bindings[0]));
    try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(resolved.program.solver_models[0].bindings[1]));

    var core_report = try lifter.validate.validate(std.testing.allocator, &resolved.program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try lifter.validate.validate(std.testing.allocator, &resolved.program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.contains(.open_profile_obligation));

    const encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &resolved.program);
    defer std.testing.allocator.free(encoded);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "\"dynamic_identity\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "lifter_dynamic_value") == null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "dynamic_string_literal_") == null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "dynamic_nil_value") == null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "value_0") == null);
    try std.testing.expect(std.mem.indexOf(u8, encoded, "!val!") == null);
    var parsed = try lifter.codec.parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    var reresolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &parsed.value, defaultBackend());
    defer reresolved.deinit();
    const reresolved_encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &reresolved.program);
    defer std.testing.allocator.free(reresolved_encoded);
    try std.testing.expectEqualStrings(encoded, reresolved_encoded);

    const tampered_bindings = try std.testing.allocator.dupe(ir.SolverModelBinding, parsed.value.solver_models[0].bindings);
    defer std.testing.allocator.free(tampered_bindings);
    tampered_bindings[1].value = .{ .dynamic_identity = 0 };
    const tampered_models = try std.testing.allocator.dupe(ir.SolverModel, parsed.value.solver_models);
    defer std.testing.allocator.free(tampered_models);
    tampered_models[0].bindings = tampered_bindings;
    var tampered = parsed.value;
    tampered.solver_models = tampered_models;
    var tampered_report = try lifter.validate.validate(std.testing.allocator, &tampered, .core);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.contradictory_solver_model));
    try std.testing.expect(tampered_report.contains(.certificate_digest_mismatch));
}

test "Z3 orchestration persists no unresolved exact numeric model" {
    const fixture = lifter.fixtures.automatic_promotion_module;
    var values = fixture.values;
    values[fixture.v_matched.index()].type = .dynamic;
    values[fixture.v_unreachable.index()].type = .dynamic;
    var instructions = fixture.instructions;
    instructions[fixture.i_matched.index()].operation = .{ .constant = .{ .integer = "9007199254740993" } };
    instructions[fixture.i_unreachable.index()].operation = .{ .constant = .{ .special_number = .nan } };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_matched } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_unreachable } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const query_id = ir.QueryId.fromIndex(0);
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(2),
    }};
    const claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(2),
        .status = .unproven,
        .required_for_emission = true,
        .evidence = &.{fixture.proof},
        .query = query_id,
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .numeric_domain,
        .subject = .{ .program = {} },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "exact dynamic numeric equality remains unresolved",
        .evidence = &.{fixture.proof},
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = query_id,
    }};
    var program = fixture.program;
    program.instructions = &instructions;
    program.values = &values;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;
    program.obligations = &obligations;

    var resolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &program, defaultBackend());
    defer resolved.deinit();
    try std.testing.expectEqual(ir.ClaimStatus.unproven, resolved.program.claims[0].status);
    try std.testing.expectEqual(ir.ObligationStatus.open, resolved.program.obligations[0].status);
    try std.testing.expectEqual(@as(usize, 0), resolved.program.solver_models.len);
    for (resolved.program.certificates) |certificate| {
        try std.testing.expect(certificate.query != query_id);
    }

    const encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &resolved.program);
    defer std.testing.allocator.free(encoded);
    for ([_][]const u8{
        "dynamic_boolean_false",
        "dynamic_boolean_true",
        "dynamic_number_literal_",
        "dynamic_string_literal_",
        "dynamic_nil_value",
        "lifter_dynamic_value",
        "value_0",
        "!val!",
    }) |forbidden| {
        try std.testing.expect(std.mem.indexOf(u8, encoded, forbidden) == null);
    }
    var core_report = try lifter.validate.validate(std.testing.allocator, &resolved.program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try lifter.validate.validate(std.testing.allocator, &resolved.program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.contains(.required_claim_unproved));
    try std.testing.expect(readable_report.contains(.open_profile_obligation));

    var parsed = try lifter.codec.parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    var reresolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &parsed.value, defaultBackend());
    defer reresolved.deinit();
    const reresolved_encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &reresolved.program);
    defer std.testing.allocator.free(reresolved_encoded);
    try std.testing.expectEqualStrings(encoded, reresolved_encoded);
}

test "Z3 authenticates exact Boolean model semantics" {
    const fixture = lifter.fixtures.automatic_promotion_module;
    var values = fixture.values;
    values[fixture.v_matched.index()].type = .dynamic;
    values[fixture.v_unreachable.index()].type = .dynamic;
    var instructions = fixture.instructions;
    instructions[fixture.i_matched.index()].operation = .{ .constant = .{ .boolean = true } };
    instructions[fixture.i_unreachable.index()].operation = .{ .constant = .{ .boolean = false } };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_matched } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_unreachable } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const query_id = ir.QueryId.fromIndex(0);
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(2),
    }};
    const claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(2),
        .status = .unproven,
        .required_for_emission = true,
        .evidence = &.{fixture.proof},
        .query = query_id,
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .numeric_domain,
        .subject = .{ .program = {} },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "the exact Boolean equality must be proved",
        .evidence = &.{fixture.proof},
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = query_id,
    }};
    var program = fixture.program;
    program.instructions = &instructions;
    program.values = &values;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;
    program.obligations = &obligations;

    var resolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &program, defaultBackend());
    defer resolved.deinit();
    try std.testing.expectEqual(ir.ClaimStatus.disproved, resolved.program.claims[0].status);
    try std.testing.expectEqual(ir.ObligationStatus.open, resolved.program.obligations[0].status);
    var query_certificate_count: usize = 0;
    for (resolved.program.certificates) |certificate| {
        if (certificate.query != query_id) continue;
        query_certificate_count += 1;
        try std.testing.expectEqual(ir.SolverResolution.disproved, certificate.resolution);
        try std.testing.expect(certificate.model != null);
        const model = resolved.program.solver_models[certificate.model.?.index()];
        try std.testing.expectEqual(@as(usize, 2), model.bindings.len);
        try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(model.bindings[0]));
        try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(model.bindings[1]));
    }
    try std.testing.expectEqual(@as(usize, 1), query_certificate_count);

    const encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &resolved.program);
    defer std.testing.allocator.free(encoded);
    var parsed = try lifter.codec.parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    const tampered_instructions = try std.testing.allocator.dupe(ir.Instruction, parsed.value.instructions);
    defer std.testing.allocator.free(tampered_instructions);
    tampered_instructions[fixture.i_unreachable.index()].operation = .{ .constant = .{ .boolean = true } };
    var tampered = parsed.value;
    tampered.instructions = tampered_instructions;
    var tampered_report = try lifter.validate.validate(std.testing.allocator, &tampered, .core);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.invalid_solver_model_value));
    try std.testing.expect(tampered_report.contains(.certificate_digest_mismatch));
}

test "Z3 authenticates fresh allocation identity models" {
    const fixture = lifter.fixtures.fresh_reference_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_table_a } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_table_b } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const query_id = ir.QueryId.fromIndex(0);
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(2),
    }};
    const claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(2),
        .status = .unproven,
        .required_for_emission = true,
        .evidence = &.{fixture.proof},
        .query = query_id,
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .alias_proof,
        .subject = .{ .program = {} },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "fresh table allocations must not alias",
        .evidence = &.{fixture.proof},
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = query_id,
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;
    program.obligations = &obligations;

    var resolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &program, defaultBackend());
    defer resolved.deinit();
    try std.testing.expectEqual(ir.ClaimStatus.disproved, resolved.program.claims[0].status);
    try std.testing.expectEqual(ir.ObligationStatus.open, resolved.program.obligations[0].status);
    var query_certificate_count: usize = 0;
    for (resolved.program.certificates) |certificate| {
        if (certificate.query != query_id) continue;
        query_certificate_count += 1;
        try std.testing.expectEqual(ir.SolverResolution.disproved, certificate.resolution);
        try std.testing.expect(certificate.model != null);
        const model = resolved.program.solver_models[certificate.model.?.index()];
        try std.testing.expectEqual(@as(usize, 2), model.bindings.len);
        try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(model.bindings[0]));
        try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(model.bindings[1]));
    }
    try std.testing.expectEqual(@as(usize, 1), query_certificate_count);

    const encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &resolved.program);
    defer std.testing.allocator.free(encoded);
    for ([_][]const u8{
        "allocation_site",
        "dynamic_boolean_",
        "dynamic_number_literal_",
        "dynamic_string_literal_",
        "dynamic_nil_value",
        "lifter_dynamic_value",
        "value_0",
        "!val!",
    }) |forbidden| {
        try std.testing.expect(std.mem.indexOf(u8, encoded, forbidden) == null);
    }

    var parsed = try lifter.codec.parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    var parsed_report = try lifter.validate.validate(std.testing.allocator, &parsed.value, .core);
    defer parsed_report.deinit();
    try std.testing.expect(parsed_report.isClean());
    var reresolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &parsed.value, defaultBackend());
    defer reresolved.deinit();
    const reresolved_encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &reresolved.program);
    defer std.testing.allocator.free(reresolved_encoded);
    try std.testing.expectEqualStrings(encoded, reresolved_encoded);

    const tampered_instructions = try std.testing.allocator.dupe(ir.Instruction, parsed.value.instructions);
    defer std.testing.allocator.free(tampered_instructions);
    const tampered_values = try std.testing.allocator.dupe(ir.Value, parsed.value.values);
    defer std.testing.allocator.free(tampered_values);
    tampered_instructions[fixture.i_table_b.index()].operation = .{ .copy = fixture.v_table_a };
    tampered_instructions[fixture.i_table_b.index()].effects = .pure;
    tampered_values[fixture.v_table_b.index()].type = .dynamic;
    var tampered = parsed.value;
    tampered.instructions = tampered_instructions;
    tampered.values = tampered_values;
    var tampered_report = try lifter.validate.validate(std.testing.allocator, &tampered, .core);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.invalid_solver_model_value));
    try std.testing.expect(tampered_report.contains(.certificate_digest_mismatch));
}

test "Z3 authenticates canonical function reference identity models" {
    const fixture = lifter.fixtures.function_reference_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_left_a } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_right } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const query_id = ir.QueryId.fromIndex(0);
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(2),
    }};
    const claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(2),
        .status = .unproven,
        .required_for_emission = true,
        .evidence = &.{fixture.proof},
        .query = query_id,
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .alias_proof,
        .subject = .{ .program = {} },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "different declared functions must not alias",
        .evidence = &.{fixture.proof},
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = query_id,
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;
    program.obligations = &obligations;

    var resolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &program, defaultBackend());
    defer resolved.deinit();
    try std.testing.expectEqual(ir.ClaimStatus.disproved, resolved.program.claims[0].status);
    try std.testing.expectEqual(ir.ObligationStatus.open, resolved.program.obligations[0].status);
    var query_certificate_count: usize = 0;
    for (resolved.program.certificates) |certificate| {
        if (certificate.query != query_id) continue;
        query_certificate_count += 1;
        try std.testing.expectEqual(ir.SolverResolution.disproved, certificate.resolution);
        try std.testing.expect(certificate.model != null);
        const model = resolved.program.solver_models[certificate.model.?.index()];
        try std.testing.expectEqual(@as(usize, 2), model.bindings.len);
        try std.testing.expectEqual(@as(u32, 0), dynamicIdentity(model.bindings[0]));
        try std.testing.expectEqual(@as(u32, 1), dynamicIdentity(model.bindings[1]));
    }
    try std.testing.expectEqual(@as(usize, 1), query_certificate_count);

    const encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &resolved.program);
    defer std.testing.allocator.free(encoded);
    for ([_][]const u8{
        "function_reference",
        "dynamic_function_reference_",
        "lifter_dynamic_value",
        "value_0",
        "!val!",
    }) |forbidden| {
        try std.testing.expect(std.mem.indexOf(u8, encoded, forbidden) == null);
    }

    var parsed = try lifter.codec.parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    var parsed_report = try lifter.validate.validate(std.testing.allocator, &parsed.value, .core);
    defer parsed_report.deinit();
    try std.testing.expect(parsed_report.isClean());
    var reresolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &parsed.value, defaultBackend());
    defer reresolved.deinit();
    const reresolved_encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &reresolved.program);
    defer std.testing.allocator.free(reresolved_encoded);
    try std.testing.expectEqualStrings(encoded, reresolved_encoded);

    const tampered_instructions = try std.testing.allocator.dupe(ir.Instruction, parsed.value.instructions);
    defer std.testing.allocator.free(tampered_instructions);
    tampered_instructions[fixture.i_right.index()].operation = .{ .function_ref = fixture.f_left };
    var tampered = parsed.value;
    tampered.instructions = tampered_instructions;
    var tampered_report = try lifter.validate.validate(std.testing.allocator, &tampered, .core);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.invalid_solver_model_value));
    try std.testing.expect(tampered_report.contains(.certificate_digest_mismatch));
}
