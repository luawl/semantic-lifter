const std = @import("std");
const ir = @import("ir.zig");
const diagnostics = @import("diagnostics.zig");
const edge_path = @import("edge_path.zig");
const edge_facts = @import("edge_facts.zig");
const proof_validation = @import("validate_proofs.zig");
const validation = @import("validate.zig");

const f_probe = ir.FunctionId.fromIndex(0);
const b_source = ir.BlockId.fromIndex(0);
const b_first = ir.BlockId.fromIndex(1);
const b_second = ir.BlockId.fromIndex(2);
const b_true = ir.BlockId.fromIndex(3);
const b_false = ir.BlockId.fromIndex(4);

const v_input_first = ir.ValueId.fromIndex(0);
const v_input_second = ir.ValueId.fromIndex(1);
const v_first = ir.ValueId.fromIndex(2);
const v_forwarded = ir.ValueId.fromIndex(3);
const v_second = ir.ValueId.fromIndex(4);

const t_first = ir.SolverTermId.fromIndex(0);
const t_second = ir.SolverTermId.fromIndex(1);
const c_first = ir.ConstraintId.fromIndex(0);
const c_second = ir.ConstraintId.fromIndex(1);
const q_first = ir.QueryId.fromIndex(0);
const q_second = ir.QueryId.fromIndex(1);
const cert_first = ir.CertificateId.fromIndex(0);
const cert_second = ir.CertificateId.fromIndex(1);
const r_first = ir.EdgeRewriteId.fromIndex(0);
const r_second = ir.EdgeRewriteId.fromIndex(1);
const proof = ir.EvidenceId.fromIndex(0);

const functions = [_]ir.Function{.{
    .id = f_probe,
    .parameters = &.{ v_input_first, v_input_second },
    .blocks = &.{ b_source, b_first, b_second, b_true, b_false },
    .entry_block = b_source,
}};

const blocks = [_]ir.Block{
    .{ .id = b_source, .function = f_probe, .terminator = .{ .jump = .{ .target = b_true } } },
    .{
        .id = b_first,
        .function = f_probe,
        .parameters = &.{ v_first, v_forwarded },
        .terminator = .{ .branch = .{
            .condition = v_first,
            .then_edge = .{ .target = b_second, .arguments = &.{v_forwarded} },
            .else_edge = .{ .target = b_false },
        } },
    },
    .{
        .id = b_second,
        .function = f_probe,
        .parameters = &.{v_second},
        .terminator = .{ .branch = .{
            .condition = v_second,
            .then_edge = .{ .target = b_true },
            .else_edge = .{ .target = b_false },
        } },
    },
    .{ .id = b_true, .function = f_probe, .terminator = .{ .return_values = &.{} } },
    .{ .id = b_false, .function = f_probe, .terminator = .{ .return_values = &.{} } },
};

const values = [_]ir.Value{
    .{ .id = v_input_first, .function = f_probe, .type = .boolean, .origin = .{ .parameter = 0 } },
    .{ .id = v_input_second, .function = f_probe, .type = .boolean, .origin = .{ .parameter = 1 } },
    .{ .id = v_first, .function = f_probe, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_first, .index = 0 } } },
    .{ .id = v_forwarded, .function = f_probe, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_first, .index = 1 } } },
    .{ .id = v_second, .function = f_probe, .type = .boolean, .origin = .{ .block_parameter = .{ .block = b_second, .index = 0 } } },
};

const evidence = [_]ir.Evidence{.{
    .id = proof,
    .kind = .frontend_proof,
    .locator = "fixture:authenticated-edge-path",
}};

const terms = [_]ir.SolverTerm{
    .{ .id = t_first, .sort = .{ .kind = .boolean }, .operation = .{ .value = v_first } },
    .{ .id = t_second, .sort = .{ .kind = .boolean }, .operation = .{ .value = v_second } },
};

const constraints = [_]ir.Constraint{
    .{
        .id = c_first,
        .predicate = t_first,
        .evidence = &.{proof},
        .scope = .{ .edge = .{ .source = b_source, .kind = .jump, .target = b_first } },
    },
    .{
        .id = c_second,
        .predicate = t_second,
        .evidence = &.{proof},
        .scope = .{ .edge = .{ .source = b_source, .kind = .jump, .target = b_first } },
    },
};

const queries = [_]ir.SolverQuery{
    .{
        .id = q_first,
        .kind = .prove_true,
        .assumptions = &.{ c_first, c_second },
        .goal = t_first,
    },
    .{
        .id = q_second,
        .kind = .prove_true,
        .assumptions = &.{ c_first, c_second },
        .path_rewrites = &.{r_first},
        .goal = t_second,
    },
};

const certificates = [_]ir.SolverCertificate{
    .{
        .id = cert_first,
        .query = q_first,
        .engine = .imported,
        .resolution = .proved,
        .evidence = &.{proof},
        .certificate_digest = "fixture:first-edge-rewrite",
    },
    .{
        .id = cert_second,
        .query = q_second,
        .engine = .imported,
        .resolution = .proved,
        .evidence = &.{proof},
        .certificate_digest = "fixture:second-edge-rewrite",
    },
};

const rewrites = [_]ir.CfgEdgeRewrite{
    .{
        .id = r_first,
        .source = b_source,
        .kind = .jump,
        .from = .{ .target = b_first, .arguments = &.{ v_input_first, v_input_second } },
        .to = .{ .target = b_second, .arguments = &.{v_input_second} },
        .certificate = cert_first,
    },
    .{
        .id = r_second,
        .source = b_source,
        .kind = .jump,
        .from = .{ .target = b_second, .arguments = &.{v_input_second} },
        .to = .{ .target = b_true },
        .certificate = cert_second,
    },
};

const valid_program: ir.Program = .{
    .program_id = "authenticated-edge-path",
    .entry_function = f_probe,
    .functions = &functions,
    .blocks = &blocks,
    .instructions = &.{},
    .values = &values,
    .evidence = &evidence,
    .solver_terms = &terms,
    .constraints = &constraints,
    .queries = &queries,
    .certificates = &certificates,
    .edge_rewrites = &rewrites,
};

fn solverReport(program: *const ir.Program) !diagnostics.Report {
    var report = diagnostics.Report.init(std.testing.allocator);
    errdefer report.deinit();
    try proof_validation.validateSolverInputs(&report, program);
    return report;
}

test "authenticated edge paths replay an ordered multi-hop history" {
    var report = try solverReport(&valid_program);
    defer report.deinit();
    try std.testing.expect(report.isClean());

    const path = (try edge_path.pathForConstraintAlloc(
        std.testing.allocator,
        &valid_program,
        constraints[c_first.index()],
        .{ .source = b_source, .kind = .jump, .target = b_true },
    )).?;
    defer std.testing.allocator.free(path);
    try std.testing.expectEqualSlices(ir.EdgeRewriteId, &.{ r_first, r_second }, path);

    var derived = constraints[c_second.index()];
    derived.path_rewrites = &.{r_first};
    const derived_edge = edge_path.constraintEdgeValue(&valid_program, derived).?;
    try std.testing.expectEqual(b_second, derived_edge.target);
    try std.testing.expectEqualSlices(ir.ValueId, &.{v_input_second}, derived_edge.arguments);
}

test "edge rewrite validation rejects tampered before and after edges" {
    {
        var changed = rewrites;
        changed[1].from.arguments = &.{v_input_first};
        var program = valid_program;
        program.edge_rewrites = &changed;
        var report = try solverReport(&program);
        defer report.deinit();
        try std.testing.expect(report.contains(.invalid_edge_rewrite));
    }
    {
        var changed = rewrites;
        changed[1].to.target = b_false;
        var program = valid_program;
        program.edge_rewrites = &changed;
        var report = try solverReport(&program);
        defer report.deinit();
        try std.testing.expect(report.contains(.invalid_edge_rewrite));
    }
}

test "edge rewrite rules cannot exchange structural and solver authority" {
    {
        var changed = rewrites;
        changed[0].rule = .forwarding_jump;
        var program = valid_program;
        program.edge_rewrites = &changed;
        var report = try solverReport(&program);
        defer report.deinit();
        try std.testing.expect(report.contains(.invalid_edge_rewrite));
    }
    {
        var changed = rewrites;
        changed[0].certificate = null;
        var program = valid_program;
        program.edge_rewrites = &changed;
        var report = try solverReport(&program);
        defer report.deinit();
        try std.testing.expect(report.contains(.invalid_edge_rewrite));
    }
}

test "query path validation rejects future and cyclic rewrite references" {
    {
        var changed = queries;
        changed[0].path_rewrites = &.{r_second};
        var program = valid_program;
        program.queries = &changed;
        var report = try solverReport(&program);
        defer report.deinit();
        try std.testing.expect(report.contains(.invalid_query_path_rewrite));
    }
    {
        var changed = queries;
        changed[0].path_rewrites = &.{r_first};
        var program = valid_program;
        program.queries = &changed;
        var report = try solverReport(&program);
        defer report.deinit();
        try std.testing.expect(report.contains(.invalid_query_path_rewrite));
    }
}

test "constraint path validation rejects disconnected rewrite prefixes" {
    var changed = constraints;
    changed[0].path_rewrites = &.{r_second};
    var program = valid_program;
    program.constraints = &changed;
    var report = try solverReport(&program);
    defer report.deinit();
    try std.testing.expect(report.contains(.invalid_constraint_path_rewrite));
}

test "an unauthenticated stale edge scope cannot skip rewrite history" {
    var changed = queries;
    changed[1].path_rewrites = &.{};
    var program = valid_program;
    program.queries = &changed;
    var report = try solverReport(&program);
    defer report.deinit();
    try std.testing.expect(report.contains(.invalid_constraint_scope));
    try std.testing.expect(report.contains(.invalid_edge_rewrite));
}

test "authenticated edge histories reject target cycles" {
    var changed_blocks = blocks;
    changed_blocks[b_source.index()].terminator = .{ .jump = .{
        .target = b_first,
        .arguments = &.{ v_input_second, v_input_second },
    } };
    changed_blocks[b_second.index()].terminator.branch.then_edge = .{
        .target = b_first,
        .arguments = &.{ v_second, v_second },
    };
    var changed_rewrites = rewrites;
    changed_rewrites[1].to = .{
        .target = b_first,
        .arguments = &.{ v_input_second, v_input_second },
    };
    var program = valid_program;
    program.blocks = &changed_blocks;
    program.edge_rewrites = &changed_rewrites;

    var report = try solverReport(&program);
    defer report.deinit();
    try std.testing.expect(report.contains(.invalid_edge_rewrite));

    const cyclic_query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(2),
        .kind = .prove_true,
        .assumptions = &.{ c_first, c_second },
        .path_rewrites = &.{ r_first, r_second },
        .goal = t_first,
    };
    try std.testing.expect(edge_path.resolvedQueryEdge(&program, cyclic_query) == null);
}

test "structural edge facts reject forged predicates and provenance" {
    const fixture = @import("fixtures.zig").relational_dispatch_module;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var term_list: std.ArrayList(ir.SolverTerm) = .empty;
    try term_list.appendSlice(allocator, fixture.program.solver_terms);
    var constraint_list: std.ArrayList(ir.Constraint) = .empty;
    var evidence_records: std.ArrayList(ir.Evidence) = .empty;
    try evidence_records.appendSlice(allocator, fixture.program.evidence);
    var source = fixture.program;
    source.constraints = &.{};
    try edge_facts.derive(allocator, &source, &term_list, &constraint_list, &evidence_records);
    var program = source;
    program.solver_terms = term_list.items;
    program.constraints = constraint_list.items;
    program.evidence = evidence_records.items;

    var clean = try validation.validate(std.testing.allocator, &program, .core);
    defer clean.deinit();
    try std.testing.expect(clean.isClean());

    const changed_constraints = try allocator.dupe(ir.Constraint, constraint_list.items);
    changed_constraints[0].predicate = fixture.constraints[fixture.c_left.index()].predicate;
    var forged = program;
    forged.constraints = changed_constraints;
    var forged_report = try validation.validate(std.testing.allocator, &forged, .core);
    defer forged_report.deinit();
    try std.testing.expect(forged_report.contains(.invalid_structural_derivation));

    const changed_evidence = try allocator.dupe(ir.Evidence, evidence_records.items);
    changed_evidence[changed_evidence.len - 1].locator = "backend:forged-edge-fact";
    forged = program;
    forged.evidence = changed_evidence;
    var provenance_report = try validation.validate(std.testing.allocator, &forged, .core);
    defer provenance_report.deinit();
    try std.testing.expect(provenance_report.contains(.invalid_structural_derivation));
}

test "history cache matches direct authenticated edge histories" {
    const program = @import("fixtures.zig").relational_dispatch_module.program;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var cache = try edge_path.HistoryCache.init(allocator, &program);
    defer cache.deinit();

    for (program.blocks) |block| {
        const references: [2]?ir.CfgEdgeRef = switch (block.terminator) {
            .jump => |edge| .{
                .{ .source = block.id, .kind = .jump, .target = edge.target },
                null,
            },
            .branch => |branch| .{
                .{ .source = block.id, .kind = .branch_then, .target = branch.then_edge.target },
                .{ .source = block.id, .kind = .branch_else, .target = branch.else_edge.target },
            },
            else => .{ null, null },
        };
        for (references) |reference| {
            const edge = reference orelse continue;
            const cached = cache.get(edge);
            const direct = try edge_path.historyForCurrentEdgeAlloc(allocator, &program, edge);
            if (direct) |history| {
                defer allocator.free(history.rewrites);
                try std.testing.expect(cached != null);
                try std.testing.expectEqual(history.root, cached.?.root);
                try std.testing.expectEqualSlices(ir.EdgeRewriteId, history.rewrites, cached.?.rewrites);
            } else {
                try std.testing.expect(cached == null);
            }
        }
    }
}

test "unique predecessor branch truth is re-rooted onto downstream Boolean edges" {
    const function_id = ir.FunctionId.fromIndex(0);
    const other_function_id = ir.FunctionId.fromIndex(1);
    const entry_id = ir.BlockId.fromIndex(0);
    const then_mid_id = ir.BlockId.fromIndex(1);
    const then_source_id = ir.BlockId.fromIndex(2);
    const then_target_id = ir.BlockId.fromIndex(3);
    const else_mid_id = ir.BlockId.fromIndex(4);
    const else_source_id = ir.BlockId.fromIndex(5);
    const else_target_id = ir.BlockId.fromIndex(6);
    const condition_id = ir.ValueId.fromIndex(0);
    const other_condition_id = ir.ValueId.fromIndex(1);
    const then_parameter_id = ir.ValueId.fromIndex(2);
    const else_parameter_id = ir.ValueId.fromIndex(3);

    const path_blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition_id,
            .then_edge = .{ .target = then_mid_id },
            .else_edge = .{ .target = else_mid_id },
        } } },
        .{ .id = then_mid_id, .function = function_id, .terminator = .{ .jump = .{ .target = then_source_id } } },
        .{ .id = then_source_id, .function = function_id, .terminator = .{ .jump = .{
            .target = then_target_id,
            .arguments = &.{condition_id},
        } } },
        .{
            .id = then_target_id,
            .function = function_id,
            .parameters = &.{then_parameter_id},
            .terminator = .{ .return_values = &.{} },
        },
        .{ .id = else_mid_id, .function = function_id, .terminator = .{ .jump = .{ .target = else_source_id } } },
        .{ .id = else_source_id, .function = function_id, .terminator = .{ .jump = .{
            .target = else_target_id,
            .arguments = &.{condition_id},
        } } },
        .{
            .id = else_target_id,
            .function = function_id,
            .parameters = &.{else_parameter_id},
            .terminator = .{ .return_values = &.{} },
        },
    };
    const path_values = [_]ir.Value{
        .{ .id = condition_id, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = other_condition_id, .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{
            .id = then_parameter_id,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .block_parameter = .{ .block = then_target_id, .index = 0 } },
        },
        .{
            .id = else_parameter_id,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .block_parameter = .{ .block = else_target_id, .index = 0 } },
        },
    };
    const function_blocks = [_]ir.BlockId{
        entry_id,
        then_mid_id,
        then_source_id,
        then_target_id,
        else_mid_id,
        else_source_id,
        else_target_id,
    };
    const path_source: ir.Program = .{
        .program_id = "unique-predecessor-branch-truth",
        .entry_function = function_id,
        .functions = &.{.{
            .id = function_id,
            .parameters = &.{ condition_id, other_condition_id },
            .entry_block = entry_id,
            .blocks = &function_blocks,
        }},
        .blocks = &path_blocks,
        .instructions = &.{},
        .values = &path_values,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var path_terms: std.ArrayList(ir.SolverTerm) = .empty;
    var path_constraints: std.ArrayList(ir.Constraint) = .empty;
    var path_evidence: std.ArrayList(ir.Evidence) = .empty;
    try edge_facts.derive(allocator, &path_source, &path_terms, &path_constraints, &path_evidence);

    var derived = path_source;
    derived.solver_terms = path_terms.items;
    derived.constraints = path_constraints.items;
    derived.evidence = path_evidence.items;
    var then_fact: ?ir.Constraint = null;
    var else_fact: ?ir.Constraint = null;
    for (derived.constraints) |constraint| switch (constraint.scope) {
        .edge => |edge| {
            if (edge.source == then_source_id and edge.kind == .jump) then_fact = constraint;
            if (edge.source == else_source_id and edge.kind == .jump) else_fact = constraint;
        },
        else => {},
    };
    try std.testing.expect(then_fact != null and else_fact != null);
    switch (derived.solver_terms[then_fact.?.predicate.index()].operation) {
        .value => |candidate| try std.testing.expectEqual(then_parameter_id, candidate),
        else => return error.TestUnexpectedResult,
    }
    const else_operand = switch (derived.solver_terms[else_fact.?.predicate.index()].operation) {
        .logical_not => |operand| operand,
        else => return error.TestUnexpectedResult,
    };
    switch (derived.solver_terms[else_operand.index()].operation) {
        .value => |candidate| try std.testing.expectEqual(else_parameter_id, candidate),
        else => return error.TestUnexpectedResult,
    }
    try std.testing.expect(edge_facts.replaysConstraint(&derived, then_fact.?));
    try std.testing.expect(edge_facts.replaysConstraint(&derived, else_fact.?));

    var rewritten_blocks = path_blocks;
    rewritten_blocks[entry_id.index()].terminator.branch.then_edge = .{ .target = then_source_id };
    const predecessor_rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = entry_id,
        .kind = .branch_then,
        .from = .{ .target = then_mid_id },
        .to = .{ .target = then_source_id },
        .rule = .forwarding_jump,
    }};
    var rewritten = derived;
    rewritten.blocks = &rewritten_blocks;
    rewritten.edge_rewrites = &predecessor_rewrites;
    try std.testing.expect(edge_facts.replaysConstraint(&rewritten, then_fact.?));

    var changed_blocks = path_blocks;
    changed_blocks[entry_id.index()].terminator.branch.else_edge.target = then_mid_id;
    var changed = derived;
    changed.blocks = &changed_blocks;
    try std.testing.expect(!edge_facts.replaysConstraint(&changed, then_fact.?));

    changed_blocks = path_blocks;
    changed_blocks[else_mid_id.index()].terminator.jump.target = then_source_id;
    changed.blocks = &changed_blocks;
    try std.testing.expect(!edge_facts.replaysConstraint(&changed, then_fact.?));

    changed_blocks = path_blocks;
    changed_blocks[else_source_id.index()].terminator = .{ .jump = .{
        .target = then_target_id,
        .arguments = &.{other_condition_id},
    } };
    changed.blocks = &changed_blocks;
    try std.testing.expect(!edge_facts.replaysConstraint(&changed, then_fact.?));

    changed_blocks = path_blocks;
    changed_blocks[entry_id.index()].terminator = .{ .jump = .{ .target = then_mid_id } };
    changed_blocks[then_mid_id.index()].terminator = .{ .branch = .{
        .condition = other_condition_id,
        .then_edge = .{ .target = then_source_id },
        .else_edge = .{ .target = entry_id },
    } };
    changed.blocks = &changed_blocks;
    try std.testing.expect(!edge_facts.replaysConstraint(&changed, then_fact.?));

    changed_blocks = path_blocks;
    changed_blocks[then_mid_id.index()].function = other_function_id;
    changed.blocks = &changed_blocks;
    try std.testing.expect(!edge_facts.replaysConstraint(&changed, then_fact.?));

    changed_blocks = path_blocks;
    changed_blocks[then_mid_id.index()].id = else_mid_id;
    changed.blocks = &changed_blocks;
    try std.testing.expect(!edge_facts.replaysConstraint(&changed, then_fact.?));
}

test "unique predecessor branch truth accepts depth 64 and rejects depth 65" {
    inline for ([_]usize{ 64, 65 }) |predecessor_depth| {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const allocator = arena.allocator();

        const function_id = ir.FunctionId.fromIndex(0);
        const condition_id = ir.ValueId.fromIndex(0);
        const parameter_id = ir.ValueId.fromIndex(1);
        const source_id = ir.BlockId.fromIndex(predecessor_depth);
        const target_id = ir.BlockId.fromIndex(predecessor_depth + 1);
        const else_id = ir.BlockId.fromIndex(predecessor_depth + 2);
        const block_count = predecessor_depth + 3;

        const block_ids = try allocator.alloc(ir.BlockId, block_count);
        const chain_blocks = try allocator.alloc(ir.Block, block_count);
        for (block_ids, 0..) |*block_id, index| block_id.* = ir.BlockId.fromIndex(index);

        chain_blocks[0] = .{ .id = block_ids[0], .function = function_id, .terminator = .{ .branch = .{
            .condition = condition_id,
            .then_edge = .{ .target = block_ids[1] },
            .else_edge = .{ .target = else_id },
        } } };
        for (1..predecessor_depth) |index| {
            chain_blocks[index] = .{ .id = block_ids[index], .function = function_id, .terminator = .{ .jump = .{
                .target = block_ids[index + 1],
            } } };
        }
        const edge_arguments = [_]ir.ValueId{condition_id};
        chain_blocks[source_id.index()] = .{ .id = source_id, .function = function_id, .terminator = .{ .jump = .{
            .target = target_id,
            .arguments = &edge_arguments,
        } } };
        const target_parameters = [_]ir.ValueId{parameter_id};
        chain_blocks[target_id.index()] = .{
            .id = target_id,
            .function = function_id,
            .parameters = &target_parameters,
            .terminator = .{ .return_values = &.{} },
        };
        chain_blocks[else_id.index()] = .{
            .id = else_id,
            .function = function_id,
            .terminator = .{ .return_values = &.{} },
        };

        const function_parameters = [_]ir.ValueId{condition_id};
        const chain_functions = [_]ir.Function{.{
            .id = function_id,
            .parameters = &function_parameters,
            .entry_block = block_ids[0],
            .blocks = block_ids,
        }};
        const chain_values = [_]ir.Value{
            .{ .id = condition_id, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
            .{
                .id = parameter_id,
                .function = function_id,
                .type = .boolean,
                .origin = .{ .block_parameter = .{ .block = target_id, .index = 0 } },
            },
        };
        const source: ir.Program = .{
            .program_id = "unique-predecessor-depth-bound",
            .entry_function = function_id,
            .functions = &chain_functions,
            .blocks = chain_blocks,
            .instructions = &.{},
            .values = &chain_values,
        };

        var terms_list: std.ArrayList(ir.SolverTerm) = .empty;
        var constraint_list: std.ArrayList(ir.Constraint) = .empty;
        var evidence_list: std.ArrayList(ir.Evidence) = .empty;
        try edge_facts.derive(allocator, &source, &terms_list, &constraint_list, &evidence_list);

        var downstream_predicate: ?ir.SolverTermId = null;
        for (constraint_list.items) |constraint| switch (constraint.scope) {
            .edge => |edge| if (edge.source == source_id and edge.kind == .jump and edge.target == target_id) {
                try std.testing.expect(downstream_predicate == null);
                downstream_predicate = constraint.predicate;
            },
            else => {},
        };
        try std.testing.expect(downstream_predicate != null);

        const operation = terms_list.items[downstream_predicate.?.index()].operation;
        if (predecessor_depth == 64) {
            switch (operation) {
                .value => |candidate| try std.testing.expectEqual(parameter_id, candidate),
                else => return error.TestUnexpectedResult,
            }
        } else {
            switch (operation) {
                .binary => |binary| try std.testing.expectEqual(ir.SolverBinaryOperator.equal, binary.operator),
                else => return error.TestUnexpectedResult,
            }
        }
    }
}

test "an edge fact carried through an authenticated clone fold stays in scope" {
    // heldout-chord-n12 shape (T6-CONSTRAINT-SCOPE-REENTRY): the arm is split into a clone, the clone is
    // folded back into its original (an endpoint the arm's history already holds; only a clone fold may
    // do that, validate_proofs.zig hasCanonicalRewritePrefix) and the original is split again. The arm
    // truth fact derived before the first split is carried by all three structural rewrites to the live edge.
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const second_clone = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const fixture_evidence = ir.EvidenceId.fromIndex(0);
    const arm_evidence = ir.EvidenceId.fromIndex(1);
    const first_group = ir.NodeSplitGroupId.fromIndex(0);
    const second_group = ir.NodeSplitGroupId.fromIndex(2);
    const fold_blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = second_clone },
            .else_edge = .{ .target = exit },
        } }, .evidence = &.{fixture_evidence} },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{ .target = exit } }, .evidence = &.{fixture_evidence} },
        .{ .id = clone, .function = function_id, .terminator = .{ .jump = .{ .target = exit } }, .evidence = &.{fixture_evidence} },
        .{ .id = second_clone, .function = function_id, .terminator = .{ .jump = .{ .target = exit } }, .evidence = &.{fixture_evidence} },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} }, .evidence = &.{fixture_evidence} },
    };
    const fold_functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, owner, clone, second_clone, exit },
        .entry_block = entry,
        .evidence = &.{fixture_evidence},
    }};
    const fold_values = [_]ir.Value{.{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } }};
    const fold_evidence = [_]ir.Evidence{
        .{ .id = fixture_evidence, .kind = .dynamic_fixture, .locator = "fixture:clone-fold-reentry" },
        .{ .id = arm_evidence, .kind = .structural_derivation, .locator = "backend:cfg-branch-arm-truth:v1" },
    };
    const fold_terms = [_]ir.SolverTerm{.{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .value = condition } }};
    const fold_constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{arm_evidence},
        .scope = .{ .edge = .{ .source = entry, .kind = .branch_then, .target = owner } },
    }};
    const history = [_]ir.CfgEdgeRewrite{
        .{ .id = ir.EdgeRewriteId.fromIndex(0), .source = entry, .kind = .branch_then, .from = .{ .target = owner }, .to = .{ .target = clone }, .rule = .node_split, .node_split_group = first_group },
        .{ .id = ir.EdgeRewriteId.fromIndex(1), .source = entry, .kind = .branch_then, .from = .{ .target = clone }, .to = .{ .target = owner }, .rule = .clone_fold, .node_split_group = first_group },
        .{ .id = ir.EdgeRewriteId.fromIndex(2), .source = entry, .kind = .branch_then, .from = .{ .target = owner }, .to = .{ .target = second_clone }, .rule = .node_split, .node_split_group = second_group },
    };
    var program: ir.Program = .{
        .program_id = "clone-fold-reentry",
        .entry_function = function_id,
        .functions = &fold_functions,
        .blocks = &fold_blocks,
        .instructions = &.{},
        .values = &fold_values,
        .evidence = &fold_evidence,
        .solver_terms = &fold_terms,
        .constraints = &fold_constraints,
        .edge_rewrites = &history,
    };

    var report = try validation.validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    // Hold today: the history is authenticated and the fact replays at its root edge.
    try std.testing.expect(!report.contains(.invalid_edge_rewrite));
    try std.testing.expect(!report.contains(.invalid_structural_derivation));
    // Fail today: constraintEffectiveTarget returns null at the fold (edge_path.zig:221), entity 0 is refused.
    try std.testing.expect(!report.contains(.invalid_constraint_scope));
    try std.testing.expect(report.isClean());
    try std.testing.expectEqual(@as(?ir.BlockId, second_clone), edge_path.constraintEffectiveTarget(&program, fold_constraints[0]));

    // Only a clone fold may re-enter: with the fold replaced by a split back to the owner, the rewrite
    // and the fact both stay refused.
    var refold = history;
    refold[1].rule = .node_split;
    refold[1].node_split_group = ir.NodeSplitGroupId.fromIndex(1);
    program.edge_rewrites = &refold;
    var refold_report = try validation.validate(std.testing.allocator, &program, .core);
    defer refold_report.deinit();
    try std.testing.expect(refold_report.contains(.invalid_edge_rewrite));
    try std.testing.expect(refold_report.contains(.invalid_constraint_scope));
    try std.testing.expect(edge_path.constraintEffectiveTarget(&program, fold_constraints[0]) == null);
}
