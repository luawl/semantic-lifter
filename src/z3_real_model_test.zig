const std = @import("std");
const lifter = @import("semantic_lifter");
const ir = lifter.ir;
const defaultBackend = lifter.z3_backend.defaultBackend;
const solverBackend = lifter.z3_backend.solverBackend;

test "Z3 returns unknown when a SAT model requires an algebraic real" {
    const integer_value = ir.ValueId.fromIndex(0);
    const real_value = ir.ValueId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = integer_value, .function = ir.FunctionId.fromIndex(0), .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = real_value, .function = ir.FunctionId.fromIndex(0), .type = .number, .origin = .{ .parameter = 1 } },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = integer_value } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .real }, .operation = .{ .value = real_value } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .real }, .operation = .{ .binary = .{
            .operator = .multiply,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .real }, .operation = .{ .real_literal = .{ .numerator = "2", .denominator = "1" } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(2),
            .right = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "7" } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(5),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .logical_and,
            .left = ir.SolverTermId.fromIndex(4),
            .right = ir.SolverTermId.fromIndex(6),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "z3-algebraic-model-refusal",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(7) };

    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.unknown, result.resolution);
    try std.testing.expectEqual(
        lifter.solver_backend.UnknownReason.model_value_unrepresentability,
        result.unknown_reason.?,
    );
    try std.testing.expectEqual(@as(usize, 0), result.model.items.len);
    try std.testing.expectEqual(@as(usize, 0), result.unsat_core.items.len);
}

test "Z3 preserves exact nonlinear rational models" {
    const real_value = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = real_value,
        .function = ir.FunctionId.fromIndex(0),
        .type = .number,
        .origin = .{ .parameter = 0 },
    }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .real }, .operation = .{ .value = real_value } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .real }, .operation = .{ .binary = .{
            .operator = .multiply,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .real }, .operation = .{ .real_literal = .{ .numerator = "4", .denominator = "1" } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
    };
    const program: ir.Program = .{
        .program_id = "z3-rational-nonlinear-model",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(3) };

    var result = try defaultBackend().solve(std.testing.allocator, &program, query);
    defer result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.proved, result.resolution);
    try std.testing.expectEqual(@as(usize, 1), result.model.items.len);
    try std.testing.expect(result.model.items[0].value == .real);
    try std.testing.expectEqual(
        lifter.solver_model.Replay.satisfied,
        try lifter.solver_model.replayAlloc(std.testing.allocator, &program, query, result.model.items),
    );
}

test "proof orchestration creates no artifact for unknown external results" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const value_id = ir.ValueId.fromIndex(0);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = value_id,
        .function = function_id,
        .type = .number,
        .origin = .{ .parameter = 0 },
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .terminator = .{ .return_values = &.{} },
        .evidence = &.{evidence_id},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{value_id},
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .frontend_proof,
        .locator = "fixture:z3-algebraic-model-refusal",
    }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .real }, .operation = .{ .value = value_id } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .real }, .operation = .{ .binary = .{
            .operator = .multiply,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .real }, .operation = .{ .real_literal = .{ .numerator = "2", .denominator = "1" } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
    };
    const query_id = ir.QueryId.fromIndex(0);
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(3),
    }};
    const claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(3),
        .status = .unproven,
        .required_for_emission = true,
        .evidence = &.{evidence_id},
        .query = query_id,
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .numeric_domain,
        .subject = .{ .program = {} },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "an exact rational countermodel is required",
        .evidence = &.{evidence_id},
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = query_id,
    }};
    const program: ir.Program = .{
        .program_id = "z3-algebraic-orchestration-refusal",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
        .solver_terms = &terms,
        .queries = &queries,
        .claims = &claims,
        .obligations = &obligations,
    };

    const limited_options: lifter.z3_backend.Options = .{
        .timeout_ms = 0,
        .resource_limit = 1,
    };
    const limited_backend = solverBackend(&limited_options);
    var limited_result = try limited_backend.solve(std.testing.allocator, &program, queries[0]);
    defer limited_result.deinit(std.testing.allocator);
    try std.testing.expectEqual(ir.SolverResolution.unknown, limited_result.resolution);
    try std.testing.expectEqual(
        lifter.solver_backend.UnknownReason.resource_exhaustion,
        limited_result.unknown_reason.?,
    );
    try std.testing.expectEqual(@as(usize, 0), limited_result.model.items.len);
    try std.testing.expectEqual(@as(usize, 0), limited_result.unsat_core.items.len);
    const limited_replay = try lifter.solver_unsat_core.replayBackendAlloc(
        std.testing.allocator,
        &program,
        queries[0],
        .proved,
        &.{},
        limited_backend,
    );
    try std.testing.expectEqual(
        lifter.solver_unsat_core.Replay{ .unresolved = .resource_exhaustion },
        limited_replay,
    );
    var invalid_query = queries[0];
    invalid_query.goal = ir.SolverTermId.fromIndex(terms.len);
    try std.testing.expectError(
        error.InvalidSolverClosure,
        limited_backend.solve(std.testing.allocator, &program, invalid_query),
    );

    const backends = [_]lifter.solver_backend.Backend{ defaultBackend(), limited_backend };
    for (backends, 0..) |selected_backend, backend_index| {
        var resolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &program, selected_backend);
        defer resolved.deinit();
        try std.testing.expectEqual(ir.ClaimStatus.unproven, resolved.program.claims[0].status);
        try std.testing.expectEqual(ir.ObligationStatus.open, resolved.program.obligations[0].status);
        try std.testing.expectEqual(@as(usize, 0), resolved.program.solver_models.len);
        try std.testing.expectEqual(@as(usize, 0), resolved.program.unsat_cores.len);
        try std.testing.expectEqual(@as(usize, 0), resolved.program.certificates.len);
        try std.testing.expect(resolved.solve_report.isClean());
        try std.testing.expect(resolved.solve_report.contains(.solver_unknown));
        try std.testing.expectEqual(@as(usize, 1), resolved.solve_report.diagnostics.items.len);
        const expected_reason: lifter.solver_backend.UnknownReason = if (backend_index == 0)
            .model_value_unrepresentability
        else
            .resource_exhaustion;
        try std.testing.expectEqual(
            expected_reason,
            resolved.solve_report.diagnostics.items[0].detail.solver_unknown.reason,
        );

        const encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &resolved.program);
        defer std.testing.allocator.free(encoded);
        try std.testing.expect(std.mem.indexOf(u8, encoded, "root-obj") == null);
        try std.testing.expect(std.mem.indexOf(u8, encoded, "!val!") == null);
        try std.testing.expect(std.mem.indexOf(u8, encoded, "resource_limit") == null);
        try std.testing.expect(std.mem.indexOf(u8, encoded, "rlimit") == null);
        try std.testing.expect(std.mem.indexOf(u8, encoded, "resource_exhaustion") == null);
        try std.testing.expect(std.mem.indexOf(u8, encoded, "model_value_unrepresentability") == null);
        var report = try lifter.validate.validate(std.testing.allocator, &resolved.program, .core);
        defer report.deinit();
        try std.testing.expect(report.isClean());
        var readable_report = try lifter.validate.validate(std.testing.allocator, &resolved.program, .readable_luau);
        defer readable_report.deinit();
        try std.testing.expect(readable_report.contains(.required_claim_unproved));
        try std.testing.expect(readable_report.contains(.open_profile_obligation));

        var parsed = try lifter.codec.parse(std.testing.allocator, encoded);
        defer parsed.deinit();
        var reresolved = try lifter.proof_orchestrator.resolveAlloc(std.testing.allocator, &parsed.value, selected_backend);
        defer reresolved.deinit();
        const reresolved_encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &reresolved.program);
        defer std.testing.allocator.free(reresolved_encoded);
        try std.testing.expectEqualStrings(encoded, reresolved_encoded);
    }
}
